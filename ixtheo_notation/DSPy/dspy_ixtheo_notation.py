#!/bin/python3
# -*- coding: utf-8 -*-
import dspy
from dspy import InputField, OutputField, Signature
from dspy.evaluate import Evaluate
from dspy.teleprompt import BootstrapFewShot, BootstrapFewShotWithRandomSearch, BootstrapFinetune
from pathlib import Path
import logging
import pyjq
import json
import random
import sys
import util
from openai import OpenAI
import os


def SetupChatAI(config):
    base_url = config.get("Server", "base_url")
    model = config.get("Model", "model")
    # API configuration
    api_key = os.environ.get('CHAT_AI_API_KEY')

    if not api_key:
        print("Export CHAT_AI_API_KEY first")
        exit(1)

    root = logging.getLogger()
    root.setLevel(logging.DEBUG)

    handler = logging.StreamHandler(sys.stdout)
    handler.setLevel(logging.INFO)
    formatter = logging.Formatter("%(asctime)s - %(name)s - %(levelname)s - %(message)s")
    handler.setFormatter(formatter)
    root.addHandler(handler)

    chat_ai = dspy.OpenAI(
        api_key = api_key,
        api_provider = "ChatAI",
        api_base = base_url,
        model_type = "text",
        model=model
    )
    return chat_ai


def answer_quality_metric(predicted_classification, manual_classification, trace=None):
    """A simple metric that compares predicted and manually assigned labels"""
    return abs(len(set(predicted_classification) & set(manual_classification) - len(set(manual_classification))))


class IxTheoAutoClassification(dspy.Module):
    def __init__(self, config):
        ixtheo_notations = Path(config.get("Notations", "notations_file")).read_text();
        additional_context = Path(str(config.get("Context", "additional_context_file"))).read_text()
        context_desc=[ixtheo_notations, additional_context]

        class AssignIxTheoNotation(dspy.Signature):
            """Assign an Ixtheo notation based on the given keywords"""
            context = dspy.InputField(desc=context_desc)
            input_data = dspy.InputField()
            ixtheo_notations = dspy.OutputField(desc="""A set of two or three letter notations as JSON array, not more than 5.
                                                        Do not output the textual description of the notations""")
            rationale = dspy.OutputField(desc="A rationale for the selection of the labels")

        class AssignNewKeywords(dspy.Signature):
            """You are a classifier and assign one or more labels to text. The text is given as a json file with id, title, keywords and summary. Use title, keywords and the summary  Avoid notations with only one letter. Generate a summary of the topics first with a bias on title and keywords. Determine the main topic. Determine whether or not the topic is concerned with a topic of theology. Determine the place and time of the topics. Then generate a new set of keywords. Please return your answer in JSON format"""
            input_data = dspy.InputField(desc="Information as JSON object")
            new_keywords = dspy.OutputField(desc="A set of newly assigned keywords as JSON object")
            rationale = dspy.OutputField(desc="A rationale for the selection of the keywords as JSON object with key keywords")
        super().__init__()
        self.generate_new_keywords = dspy.ChainOfThought(AssignNewKeywords)
        self.generate_notations = dspy.ChainOfThought(AssignIxTheoNotation)


    def forward(self, input_data):
        new_keywords = self.generate_new_keywords(input_data=input_data)
        notations = self.generate_notations(input_data=new_keywords.new_keywords, context="")
        print(f"New notations: {notations.ixtheo_notations}")
        print("\n-----------------------------------------------\n")
        print(f"New Keywords: {str(new_keywords.new_keywords)}")
        print(f"New Keywords rationale: {str(new_keywords.rationale)}")
        print(f"Notation rationale: {str(notations.rationale)}")
        return notations


    def run(self, input_data):
        return self.forward(input_data)


def GetRandomOffsets(num_of_samples, fulltext_parsed):
    num_of_elements = pyjq.first('length', fulltext_parsed)
    random_elements = list(random.sample(range(0, num_of_elements-1), num_of_samples))
    return '.' + str(random_elements)


def ReadFulltext(file_path):
    with open(file_path) as json_data:
        fulltext_parsed = json.load(json_data)
        return fulltext_parsed


def Usage():
    print("Usage: " + sys.argv[0] + " [--sample number_of_samples] augmented_tocs_with_notations.json output_directory")
    sys.exit(-1)


def GenerateTrainingSet(items):
    inputs = pyjq.all('del(.[].ixtheo_notation) | .[]', items)
    gold_standard_results = pyjq.all('.[].ixtheo_notation', items)
    combined = zip(inputs, gold_standard_results)
    return [ dspy.Example(input_data = json.dumps(input), ixtheo_notations = json.dumps(result)).with_inputs("input_data") for input, result in combined ]


def GetPredictions(config, items):
    ixtheo_auto_classification = IxTheoAutoClassification(config)
    for item in items:
        print(pyjq.first('.id', item))
        #new_notations = ProcessRecord(config, str(pyjq.first('del(.ixtheo_notation)', item)), output_directory)
        new_notations = ixtheo_auto_classification(str(pyjq.first('del(.ixtheo_notation)', item)))
        print("\n************************************************\n")
        print("New notations: " + str(new_notations.ixtheo_notations))
        print("Original Notations: " + str(pyjq.first('.ixtheo_notation', item)))

        print("\n###############################################\n")

def Optimize(config, items):
    optimizer_config = dict(max_bootstrapped_demos=4, max_labeled_demos=4)
    teleprompter = BootstrapFewShot(metric=answer_quality_metric, **optimizer_config)
    optimized = teleprompter.compile(IxTheoAutoClassification(config), trainset=GenerateTrainingSet(items))


def Main():
    use_samples = False

    if len(sys.argv) != 3 and len(sys.argv) != 5:
        Usage()

    if len(sys.argv) == 5:
        optional_parameter = sys.argv.pop(1)
        if optional_parameter != '--sample':
            Usage()
        use_samples = True

    if len(sys.argv) == 4:
        number_of_samples = int(sys.argv.pop(1))
        if not isinstance(number_of_samples, int) or not (number_of_samples > 0):
            Usage()

    augmented_tocs_with_notations = sys.argv[1]
    output_directory = sys.argv[2]

    config=util.LoadConfigFile('../conf/' +  os.path.basename(sys.argv[0])[:-2] + "conf")
    client = SetupChatAI(config)
    dspy.settings.configure(lm=client)

    jq_array_element_selector = '.[]'
    if use_samples:
       jq_array_element_selector = GetRandomOffsets(number_of_samples, ReadFulltext(augmented_tocs_with_notations))


    items = pyjq.all(jq_array_element_selector, ReadFulltext(augmented_tocs_with_notations))
    #GetPredictions(config, items)
    Optimize(config, items)



if __name__ == "__main__":
    Main()