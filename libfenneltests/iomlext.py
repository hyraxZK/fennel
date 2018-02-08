#!/usr/bin/python
#
# (C) 2017 Riad S. Wahby <rsw@cs.stanford.edu>
#
# test IO MLExt streaming algorithm (due to Victor Vu)

# hack: this test lives in a subdir
try:
    import sys
    import os.path
except:
    assert False
else:
    sys.path.insert(1, os.path.abspath(os.path.join(sys.path[0], os.pardir)))

import random
import time

from libfennel.circuitverifier import VerifierIOMLExt
from libfennel.defs import Defs
from libfennel.layercompute import LayerComputeBeta, LayerComputeV
import libfennel.util as util

def run_one_test(nbits, squawk, nbins, pattern):
    z = [ Defs.gen_random() for _ in xrange(0, nbits) ]

    inv = [ Defs.gen_random() for _ in xrange(0, (2 ** nbits) - nbins) ]
    if pattern is 0:
        inv += [ 0 for _ in xrange(0, nbins) ]
    elif pattern is 1:
        inv += [ 1 for _ in xrange(0, nbins) ]
    elif pattern == 2:
        inv += [ (i % 2) for i in xrange(0, nbins) ]
    elif pattern == 3:
        inv += [ ((i + 1) % 2) for i in xrange(0, nbins) ]
    else:
        inv += [ random.randint(0, 1) for _ in xrange(0, nbins) ]

    assert len(inv) == (2 ** nbits)

    Defs.track_fArith = True
    fa = Defs.fArith()
    oldrec = fa.new_cat("old")
    newrec = fa.new_cat("new")
    nw2rec = fa.new_cat("nw2")

    oldbeta = LayerComputeBeta(nbits, z, oldrec)
    oldval = sum(util.mul_vecs(oldbeta.outputs, inv)) % Defs.prime
    oldrec.did_mul(len(inv))
    oldrec.did_add(len(inv)-1)

    newcomp = VerifierIOMLExt(z, newrec)
    newval = newcomp.compute(inv)

    nw2comp = LayerComputeV(nbits, nw2rec)
    nw2comp.other_factors = []
    nw2comp.set_inputs(inv)
    for zz in z:
        nw2comp.next_round(zz)
    nw2val = nw2comp.prevPassValue

    assert oldval == newval, "error for inputs (new) %s : %s" % (str(z), str(inv))
    assert oldval == nw2val, "error for inputs (nw2) %s : %s" % (str(z), str(inv))

    if squawk:
        print
        print "nbits: %d" % nbits
        print "OLD: %s" % str(oldrec)
        print "NEW: %s" % str(newrec)
        print "NW2: %s" % str(nw2rec)

    betacomp = VerifierIOMLExt.compute_beta(z)
    beta_lo = random.randint(0, 2**nbits - 1)
    beta_hi = random.randint(beta_lo, 2**nbits - 1)
    betacomp2 = VerifierIOMLExt.compute_beta(z, None, 1, beta_lo, beta_hi)
    # make sure that the right range was generated, and correctly
    assert len(betacomp) == len(betacomp2)
    assert all([ b is None for b in betacomp2[:beta_lo] ])
    assert all([ b is not None for b in betacomp2[beta_lo:beta_hi + 1] ])
    assert all([ b is None for b in betacomp2[beta_hi+1:] ])
    assert all([ b2 == b if b2 is not None else True for (b, b2) in zip(betacomp, betacomp2) ])

    return newrec.get_counts()

def run_tests(num_tests, squawk=False):
    for _ in xrange(0, num_tests):
        nbits = random.randint(3, 8)
        run_one_test(nbits, squawk, 0, 0)
        if not squawk:
            sys.stdout.write('.')
            sys.stdout.flush()

    if not squawk:
        print " (iomlext test passed)"

def run_savetests():
    Defs.savebits = True
    if len(sys.argv) > 2:
        nbits = int(sys.argv[2])
    else:
        nbits = 5
    fval = run_one_test(nbits, False, 0, 0)
    print "%d/0: %d muls, %d adds" % (nbits, fval[0], fval[1])
    print

    for lnbins in xrange(0, nbits + 1):
        nbins = 2 ** lnbins
        tot_m = 0
        tot_a = 0
        final = 300.0
        for _ in xrange(0, int(final)):
            vals = run_one_test(nbits, False, nbins, 4)
            tot_m += vals[0]
            tot_a += vals[1]

        print "%d/%d: %f muls, %f adds" % (nbits, nbins, tot_m/final, tot_a/final)
        fval = run_one_test(nbits, False, nbins, 2)
        print "%d/%d: %d muls, %d adds" % (nbits, nbins, fval[0], fval[1])
        print

def speed_test(num_tests):
    nbits = random.randint(3, 8)
    taus = [ Defs.gen_random() for _ in xrange(0, nbits) ]
    inputs = [ [ Defs.gen_random() for _ in xrange(0, 2**nbits) ] for _ in xrange(0, num_tests) ]

    vim = VerifierIOMLExt(taus)
    runtime = time.time()
    for idx in xrange(0, num_tests):
        vim.compute_nosavebits(inputs[idx])
    runtime = time.time() - runtime

    runtime2 = time.time()
    for idx in xrange(0, num_tests):
        vim.compute_savebits(inputs[idx])
    runtime2 = time.time() - runtime2

    runtime3 = time.time()
    for idx in xrange(0, num_tests):
        vim.compute_sqrtbits(inputs[idx])
    runtime3 = time.time() - runtime3

    print "nBits: %d\nnosavebits: %f\nsavebits: %f\nsqrtbits: %f\n" % (nbits, runtime, runtime2, runtime3)

if __name__ == "__main__":
    ntests = 128
    speed = False
    save = False
    if len(sys.argv) > 1:
        if sys.argv[1] == "-s":
            speed = True
            if len(sys.argv) > 2:
                ntests = int(sys.argv[2])
        elif sys.argv[1] == "-S":
            save = True
        else:
            ntests = int(sys.argv[1])

    if speed:
        speed_test(ntests)
    elif save:
        run_savetests()
    else:
        run_tests(ntests, True)
