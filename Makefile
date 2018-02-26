TUEFIND_FLAVOUR ?= "unknown"
.PHONY: all install clean test install_configs

all:
	$(MAKE) -C cpp/lib/mkdep;
	$(MAKE) -C cpp;
	if [ $(TUEFIND_FLAVOUR) != "unknown" ]; then\
	    $(MAKE) -C solr_plugins;\
	    $(MAKE) -C solrmarc_mixin;\
	    $(MAKE) -C cronjobs;\
	fi

install: install_configs
	$(MAKE) -C cpp/lib/mkdep install;
	$(MAKE) -C cpp install;
	if [ $(TUEFIND_FLAVOUR) != "unknown" ]; then\
	    $(MAKE) -C solr_plugins;\
	    $(MAKE) -C solrmarc_mixin;\
	    $(MAKE) -C cronjobs;\
	fi

clean:
	$(MAKE) -C cpp/lib/mkdep clean;
	$(MAKE) -C cpp clean;
	$(MAKE) -C cronjobs clean;
	$(MAKE) -C solr_plugins clean;
	$(MAKE) -C solrmarc_mixin clean;

test:
	$(MAKE) -C cpp/tests test;

install_configs:
ifeq "$(TUEFIND_FLAVOUR)" "ixtheo"
	@echo "Installing $(TUEFIND_FLAVOUR)..."
	$(MAKE) -C /mnt/ZE020150/FID-Entwicklung/IxTheo/ install
else ifeq "$(TUEFIND_FLAVOUR)" "krimdok"
	@echo "Installing $(TUEFIND_FLAVOUR)..."
	$(MAKE) -C /mnt/ZE020150/FID-Entwicklung/KrimDok/ install
else
	$(warning neither a KrimDok nor an IxTheo installation can be found!)
endif

