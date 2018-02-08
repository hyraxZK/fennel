#!/usr/bin/python
#
# (C) 2017 Riad S. Wahby <rsw@cs.stanford.edu>
#
# test LayerComputeBeta

# hack: this test lives in a subdir
try:
    import os.path
    import random
    import sys
    import time
except:
    assert False
else:
    sys.path.insert(1, os.path.abspath(os.path.join(sys.path[0], os.pardir)))

from libfennel import util
from libfennel.circuitverifier import VerifierIOMLExt
from libfennel.defs import Defs
from libfennel.layercompute import LayerComputeBeta

nOutBits = 4
lcv = LayerComputeBeta(nOutBits)

def run_test():
    # pylint: disable=global-variable-undefined,redefined-outer-name
    tinputs = [Defs.gen_random() for _ in xrange(0, nOutBits)]
    taus = [Defs.gen_random() for _ in xrange(0, nOutBits)]
    lcv.set_inputs(tinputs)
    assert lcv.outputs == VerifierIOMLExt.compute_beta(tinputs)

    inputs = [util.chi(util.numToBin(x, nOutBits), tinputs) for x in xrange(0, 2**nOutBits)]

    global scratch
    global outputs

    scratch = list(inputs)
    outputs = list(inputs)

    def compute_next_value(tau):
        global scratch
        global outputs

        nscratch = []
        tauInv = (1 - tau) % Defs.prime

        for i in xrange(0, len(scratch) / 2):
            val = ((scratch[2*i] * tauInv) + (scratch[2*i + 1] * tau)) % Defs.prime
            nscratch.append(val)

        del val
        scratch = nscratch

        #ndups = len(outputs) / len(scratch)
        #nouts = [ [val] * ndups for val in scratch ]
        outputs = scratch
        #outputs = [item for sublist in nouts for item in sublist]

    for i in xrange(0, nOutBits):
        assert lcv.inputs == inputs
        assert lcv.outputs == outputs
        assert lcv.scratch == scratch

        compute_next_value(taus[i])
        lcv.next_round(taus[i])

        assert outputs == lcv.outputs
        assert scratch == lcv.scratch

    assert lcv.prevPassValue == scratch[0]
    assert all([lcv.prevPassValue == elm[0] for elm in lcv.outputs_fact])

def speed_test(num_tests):
    nBits = random.randint(3, 8)
    inputs = [ [ Defs.gen_random() for _ in xrange(0, nBits)  ] for _ in xrange(0, num_tests) ]

    lcb = LayerComputeBeta(nBits)
    lcb.other_factors = []
    runtime = time.time()
    for idx in xrange(0, num_tests):
        lcb.set_inputs(inputs[idx])
    runtime = time.time() - runtime

    runtime2 = time.time()
    for idx in xrange(0, num_tests):
        VerifierIOMLExt.compute_beta(inputs[idx])
    runtime2 = time.time() - runtime2

    print "nBits: %d\nLayerComputeBeta: %f\nVerifierIOMLExt: %f\n" % (nBits, runtime, runtime2)

def run_tests(num_tests):
    for i in xrange(0, 64 * num_tests):
        run_test()
        if i % 64 == 0:
            sys.stdout.write('.')
            sys.stdout.flush()

    print " (compute_beta test passed)"

if __name__ == "__main__":
    ntests = 128
    speed = False
    if len(sys.argv) > 1:
        if sys.argv[1] == "-s":
            speed = True
            ntests = 10000
            if len(sys.argv) > 2:
                ntests = int(sys.argv[2])
        else:
            ntests = int(sys.argv[1])

    if speed:
        speed_test(ntests)
    else:
        run_tests(ntests)
