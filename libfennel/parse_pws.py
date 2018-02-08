#!/usr/bin/python
#
# (C) 2017 Riad S. Wahby <rsw@cs.nyu.edu>
#
# take output from pylibpws and turn it into something we can use in libfennel

import libfennel.gateprover as gp
import libfennel.util as util

def parse_pws(input_pws):
    input_layer = input_pws[0]
    input_pws = input_pws[1:]

    in0vv = []
    in1vv = []
    typvv = []
    muxvv = []
    for lay in xrange(0, len(input_pws)):
        in0v = []
        in1v = []
        typv = []
        muxv = []

        for (gStr, in0, in1, mx) in input_pws[lay]:
            in0v.append(in0)
            in1v.append(in1)
            muxv.append(mx if mx is not None else 0)

            if gStr == 'ADD':
                typv.append(gp.AddGateProver)
            elif gStr == 'MUL':
                typv.append(gp.MulGateProver)
            elif gStr == 'SUB':
                typv.append(gp.SubGateProver)
            elif gStr == 'MUX':
                typv.append(gp.MuxGateProver)
            elif gStr == 'OR':
                typv.append(gp.OrGateProver)
            elif gStr == 'XOR':
                typv.append(gp.XorGateProver)
            elif gStr == 'NOT':
                typv.append(gp.NotGateProver)
            elif gStr == 'NAND':
                typv.append(gp.NandGateProver)
            elif gStr == 'NOR':
                typv.append(gp.NorGateProver)
            elif gStr == 'NXOR':
                typv.append(gp.NxorGateProver)
            elif gStr == 'NAAB':
                typv.append(gp.NaabGateProver)
            elif gStr == 'PASS':
                typv.append(gp.PassGateProver)
            else:
                assert False, "Unknown gate type %s" % gStr

        in0vv.append(in0v)
        in1vv.append(in1v)
        typvv.append(typv)
        muxvv.append(muxv)

    if len(in0vv[-1]) == 1:
        in0vv[-1].append(0)
        in1vv[-1].append(0)
        typvv[-1].append(gp.AddGateProver)
        muxvv[-1].append(0)
    return (input_layer, in0vv, in1vv, typvv, muxvv)

# handle RDL pws
def parse_rdl(rFile, nCopies, pInputs):
    # 1. check that rFile is of the proper form
    lenPI = len(pInputs)
    pInPad = 2 ** util.clog2(lenPI) - lenPI
    assert len(rFile) == 2
    assert all( ent[0] == "PASS" for ent in rFile[1] )
    if len(rFile[1]) != nCopies * lenPI:
        raise ValueError("This RDL appears to be for the wrong number of copies (%d, expected %d)" % (len(rFile[1]), nCopies * lenPI))

    # 2. generate the mapping
    rdl_map = []
    for idx in xrange(0, nCopies):
        rdl_ent = [ ent[1] for ent in rFile[1][idx*lenPI:(idx+1)*lenPI] ]
        rdl_ent += [0] * pInPad
        rdl_map.append(rdl_ent)

    return (rFile[0], rdl_map)

# circuitverifier and circuitprover use this as their metaclass
class FromPWS(type):
    def from_pws(cls, input_pws, nCopies):
        (input_layer, in0vv, in1vv, typvv, muxvv) = parse_pws(input_pws)
        return (input_layer, cls(nCopies, len(input_layer), in0vv, in1vv, typvv, muxvv))
