/** \file    FileLocker.h
 *  \brief   Declaration of class FileLocker.
 *  \author  Dr. Johannes Ruscheinski
 */

/*
 *  Copyright 2004-2005 Project iVia.
 *  Copyright 2004-2005 The Regents of The University of California.
 *
 *  This file is part of the libiViaCore package.
 *
 *  The libiViaCore package is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Lesser General Public License as published
 *  by the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  libiViaCore is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public License
 *  along with libiViaCore; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

#ifndef FILE_LOCKER_H
#define FILE_LOCKER_H


#ifndef STRING
#       include <string>
#       define STRING
#endif
#include "File.h"


/** \class  FileLocker
 *  \brief  Provides advisory (i.e. requires cooperating processes) file locking.
 */
class FileLocker {
    int lock_fd_;                /**< File descriptor for the file we're locking. */
public:
    enum LockType { READ_ONLY, WRITE_ONLY };
public:
    /** \brief  Construct a FileLocker.  Blocks until we gain access.
     *  \param  fd         The file descriptor that we want to lock.
     *  \param  lock_type  The type of lock that we request.
     */
    FileLocker(const int fd, const LockType lock_type);

    /** Unlocks our file. */
    ~FileLocker();
};


#endif // ifndef FILE_LOCKER_H
