#!/usr/bin/python
#
# (C) 2017 Riad S. Wahby <rsw@cs.stanford.edu>
#
# libfenneltests runner

# hack: these tests live in a subdir
try:
    import sys
    import os.path
except:
    assert False
else:
    sys.path.insert(1, os.path.abspath(os.path.join(sys.path[0], os.pardir)))

import libfenneltests.commit as commit
import libfenneltests.compute_v as compute_v
import libfenneltests.compute_beta as compute_beta
import libfenneltests.iomlext as iomlext
import libfenneltests.layer as layer
import libfenneltests.circuit as circuit
import libfenneltests.verifier as verifier
import libfenneltests.nonint as nonint
import libfenneltests.nizk as nizk
import libfenneltests.nizkvecwit as nizkvecwit
import libfenneltests.logwit as logwit

DEFAULT_NUM_TESTS = 5

if len(sys.argv) > 1:
    try:
        num_tests = int(sys.argv[1])
    except:
        num_tests = DEFAULT_NUM_TESTS
else:
    num_tests = DEFAULT_NUM_TESTS

for thing in [commit, logwit, compute_v, compute_beta, iomlext, layer, circuit, verifier, nonint, nizk, nizkvecwit]:
    thing.run_tests(num_tests)
