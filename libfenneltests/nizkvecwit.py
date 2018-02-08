#!/usr/bin/python
#
# (C) 2017 Riad S. Wahby <rsw@cs.stanford.edu>
#
# test layer prover

# hack: this test lives in a subdir
try:
    import sys
    import os.path
except:
    assert False
else:
    sys.path.insert(1, os.path.abspath(os.path.join(sys.path[0], os.pardir)))

import random

from libfennel.circuitnizkvecwit import CircuitProverVecWitNIZK, CircuitVerifierVecWitNIZK
from libfennel.defs import Defs
from libfennel.fiatshamir import FiatShamir
from libfennel import randutil

def rand_ckt(nInBits, nLayers):
    in0vv = []
    in1vv = []
    typvv = []
    for _ in xrange(0, nLayers):
        (in0v, in1v, typv) = randutil.rand_ckt(nInBits, nInBits)
        in0vv.append(in0v)
        in1vv.append(in1v)
        typvv.append(typv)
    return (in0vv, in1vv, typvv)

def run_one_test(nInBits, nCopies, nLayers, qStat):
    (in0vv, in1vv, typvv) = rand_ckt(nInBits, nLayers)
    prv = CircuitProverVecWitNIZK(nCopies, 2**nInBits, in0vv, in1vv, typvv)

    # blind some of the inputs to the verifier
    nondet_bits = random.randint(0, nInBits-1)
    prv.set_nondet_range(nondet_bits)

    inputs = randutil.rand_inputs(nInBits, nCopies)
    pf = prv.run(inputs)

    ver = CircuitVerifierVecWitNIZK(nCopies, 2**nInBits, in0vv, in1vv, typvv)
    ver.run(pf)

    if not qStat:
        print "nInBits: %d, nCopies: %d, nLayers: %d" % (nInBits, nCopies, nLayers)
        print "    %d group elems, %d bytes in proof" % FiatShamir.proof_size(pf)
        for fArith in [ver.in_a, ver.out_a, ver.sc_a, ver.tV_a, ver.nlay_a]:
            if fArith is not None:
                print "    %s: %s" % (fArith.cat, str(fArith))

def run_rdl_test(nInBits, nCopies, nLayers, qStat):
    (in0vv, in1vv, typvv) = rand_ckt(nInBits, nLayers)
    nRDLBits = nInBits - random.randint(0,2)
    nRDLInputs = 2 ** nRDLBits
    nInputs = 2 ** nInBits
    rdl = [ [ random.randint(0, nRDLInputs - 1) for _ in xrange(0, nInputs) ] for _ in xrange(0, nCopies) ]

    prv = CircuitProverVecWitNIZK(nCopies, 2**nInBits, in0vv, in1vv, typvv)
    prv.set_rdl(rdl, nRDLInputs)

    inputs = randutil.rand_inputs(nRDLBits, 1)
    pf = prv.run(inputs)

    ver = CircuitVerifierVecWitNIZK(nCopies, 2**nInBits, in0vv, in1vv, typvv)
    ver.set_rdl(rdl, nRDLInputs)
    ver.run(pf)

    if not qStat:
        print "nInBits: %d, nCopies: %d, nLayers: %d" % (nInBits, nCopies, nLayers)
        print "    %d group elems, %d bytes in proof" % FiatShamir.proof_size(pf)
        for fArith in [ver.in_a, ver.out_a, ver.sc_a, ver.tV_a, ver.nlay_a]:
            if fArith is not None:
                print "    %s: %s" % (fArith.cat, str(fArith))

def run_tests(num_tests, qStat=True):
    for i in xrange(0, num_tests):
        Defs.track_fArith = i % 2 == 0
        run_one_test(random.randint(2, 4), 2**random.randint(3, 8), random.randint(2, 5), qStat)
        run_rdl_test(random.randint(3, 5), 2**random.randint(3, 8), random.randint(2, 5), qStat)

        if qStat:
            sys.stdout.write('.')
            sys.stdout.flush()

    if qStat:
        print " (nizk-vec-wit test passed)"

if __name__ == "__main__":
    run_tests(16, False)
