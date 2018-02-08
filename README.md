# libfennel - Hyrax reference implementation #

libfennel is the reference implementation of [Hyrax](https://hyrax.crypto.fyi), a zkSNARK that
requires no trusted setup.

This implementation is written in Python and C/C++. It is compatible with both Python 2.7
and PyPy. (Porting to Python 3.0 would be trivial, but would reduce performance.)

## Building and using ##

The code in this directory is pure Python, but to read PWS files and for elliptic curve operations
we use C/C++ extensions. These extensions live in their own repositories,
[pymiracl](https://github.com/hyraxZK/pymiracl) and [libpws](https://github.com/hyraxZK/libpws).
The easiest way to use the whole system is to check out the
[hyraxZK](https://github.com/hyraxZK/hyraxZK) "meta-repository", which links all the necessary
submodules and has a top-level Makefile.

## Running ##

If you want to run a PWS file, you should use `run_fennel.py` like so:

    ./run_fennel.py -p /path/to/PWS/file

Execute `./run_fennel.py` with no arguments to see all of the possible arguments.

## Tests ##

The `libfenneltests/` subdir has a pretty complete set of tests for libfennel.

You can run the tests like so:

    python libfenneltests/

# License #

Copyright 2017 Riad S. Wahby <rsw@cs.stanford.edu> and the Hyrax authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

# Questions? #

    rsw@cs.stanford.edu
