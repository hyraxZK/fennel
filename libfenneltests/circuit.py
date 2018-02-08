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

from libfennel import util, randutil
from libfennel.circuitprover import CircuitProver
from libfennel.defs import Defs
from libfennel.layercompute import LayerComputeBeta

def run_one_test(nInBits, nCopies):
    nOutBits = nInBits

    (in0v, in1v, typv) = randutil.rand_ckt(nOutBits, nInBits)
    inputs = randutil.rand_inputs(nInBits, nCopies)

    circuit = CircuitProver(nCopies, 2**nInBits, [in0v], [in1v], [typv])
    circuit.set_inputs(inputs)

    z1 = [Defs.gen_random() for _ in xrange(0, nOutBits)]
    z2 = [Defs.gen_random() for _ in xrange(0, circuit.nCopyBits)]

    circuit.set_z(z1, z2, None, None, True)

    # mlExt of outputs
    outflat = util.flatten(circuit.ckt_outputs)
    inLayer_mults = LayerComputeBeta(nOutBits + circuit.nCopyBits, z1 + z2)
    assert len(outflat) == len(inLayer_mults.outputs)
    inLayermul = util.mul_vecs(inLayer_mults.outputs, outflat)
    inLayerExt = sum(inLayermul) % Defs.prime

    w1 = [ Defs.gen_random() for _ in xrange(0, nInBits) ]
    w2 = [ Defs.gen_random() for _ in xrange(0, nInBits) ]
    w3 = [ Defs.gen_random() for _ in xrange(0, circuit.nCopyBits) ]

    initOutputs = circuit.get_outputs()

    assert inLayerExt == (initOutputs[0] + sum(initOutputs)) % Defs.prime

    for i in xrange(0, len(w3)):
        circuit.next_round(w3[i])
        circuit.get_outputs()

    for i in xrange(0, len(w1)):
        circuit.next_round(w1[i])
        circuit.get_outputs()

    for i in xrange(0, len(w2)):
        circuit.next_round(w2[i])
        finalOutputs = circuit.get_outputs()

    # check the outputs by computing mlext of layer input directly

    inflat = util.flatten(inputs)

    v1_mults = LayerComputeBeta(circuit.layer_inbits[0] + circuit.nCopyBits, w1 + w3)
    assert len(inflat) == len(v1_mults.outputs)
    v1inmul = util.mul_vecs(v1_mults.outputs, inflat)
    v1 = sum(v1inmul) % Defs.prime

    v2_mults = LayerComputeBeta(circuit.layer_inbits[0] + circuit.nCopyBits, w2 + w3)
    assert len(inflat) == len(v2_mults.outputs)
    v2inmul = util.mul_vecs(v2_mults.outputs, inflat)
    v2 = sum(v2inmul) % Defs.prime

    assert v1 == finalOutputs[0]
    assert v2 == sum(finalOutputs) % Defs.prime

def run_tests(num_tests):
    for _ in xrange(0, num_tests):
        run_one_test(random.randint(2, 6), 2**random.randint(1, 6))
        sys.stdout.write('.')
        sys.stdout.flush()

    print " (circuit test passed)"

if __name__ == "__main__":
    run_tests(128)
