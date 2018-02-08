#!/usr/bin/python
#
# (C) 2017 Riad S. Wahby <rsw@cs.stanford.edu>
#
# test LayerComputeV

# hack: this test lives in a subdir
try:
    import sys
    import os.path
except:
    assert False
else:
    sys.path.insert(1, os.path.abspath(os.path.join(sys.path[0], os.pardir)))

from libfennel.defs import Defs
from libfennel.layercompute import LayerComputeV

nOutBits = 4
lcv = LayerComputeV(nOutBits)

def run_test(nOutBits, nValues):
    # pylint: disable=redefined-outer-name,global-variable-undefined
    inputs = [Defs.gen_random() for _ in xrange(0, nValues)]
    taus = [Defs.gen_random() for _ in xrange(0, nOutBits)]

    lcv.set_inputs(inputs)

    global scratch
    global outputs

    inputs += [0] * (2**nOutBits - nValues)
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

        ndups = len(outputs) / len(scratch)
        nouts = [ [val] * ndups for val in scratch ]
        outputs = [item for sublist in nouts for item in sublist]

    for i in xrange(0, nOutBits):
        assert lcv.inputs == inputs
        assert lcv.outputs == outputs
        assert lcv.scratch == scratch

        compute_next_value(taus[i])
        lcv.next_round(taus[i])

        if i < nOutBits - 1:
            assert outputs == lcv.outputs
            assert scratch == lcv.scratch

    assert lcv.prevPassValue == scratch[0]

def run_tests(num_tests):
    for i in xrange(0, 16 * num_tests):
        run_test(nOutBits, 2**nOutBits - 5)
        run_test(nOutBits, 2**nOutBits - 4)
        run_test(nOutBits, 2**nOutBits - 1)
        run_test(nOutBits, 2**nOutBits - 0)
        if i % 16 == 0:
            sys.stdout.write('.')
            sys.stdout.flush()

    print " (compute_v test passed)"

if __name__ == "__main__":
    run_tests(128)
