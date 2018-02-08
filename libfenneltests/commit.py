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

from libfennel.circuitverifier import VerifierIOMLExt
from libfennel import commit
from libfennel.defs import Defs

def run_one_test():
    run_scalar_test(random.choice(('m159', 'm191', 'm221', 'm255')))
    run_vector_test(random.choice(('m159', 'm191', 'm221', 'm255')))

def run_scalar_helper(com):
    # check PoK
    xval = com.gops.rand_scalar()
    chal = com.gops.rand_scalar()
    (c1val, r1val) = com.commit(xval)
    (aval, t1, t2) = com.pok_init()
    (z1, z2) = com.pok_finish(xval, r1val, t1, t2, chal)
    assert com.pok_check(c1val, aval, chal, z1, z2)

    # check Proof of equality
    (c2val, r2val) = com.commit(xval)
    chal = com.gops.rand_scalar()
    (aval, t1) = com.est_init()
    z = com.est_eq(r1val, r2val, t1, chal)
    assert com.est_eq_check(c1val, c2val, aval, chal, z)

    # check Proof of opening
    chal = com.gops.rand_scalar()
    (aval, t1) = com.est_init()
    z = com.est_val(r1val, t1, chal)
    assert com.est_val_check(c1val, xval, aval, chal, z)

    # check Proof of product
    yval = com.gops.rand_scalar()
    zval = (xval * yval) % com.gops.q
    (c3val, r3val) = com.commit(yval)
    (c4val, r4val) = com.commit(zval)
    xvals = (xval, yval, zval)
    cvals = (c1val, c3val, c4val)
    rvals = (r1val, r3val, r4val)
    chal = com.gops.rand_scalar()
    chal2 = com.gops.rand_scalar()
    (avals, bvals) = com.prod_init(c1val)
    zvals = com.prod_finish(xvals, rvals, bvals, chal)
    assert com.prod_check(cvals, avals, zvals, chal)
    assert not com.prod_check(cvals, avals, zvals, chal2)
    assert not com.prod_check((c1val, c2val, c4val), avals, zvals, chal)

def run_vector_helper(com):
    # two random vectors and their dot product
    Jvec = [ com.gops.rand_scalar() for _ in xrange(0, com.gops.maxlen) ]
    Avec = [ com.gops.rand_scalar() for _ in xrange(0, com.gops.maxlen) ]
    s0 = sum([ (j * a) % Defs.prime for (j, a) in zip(Jvec, Avec) ]) % Defs.prime

    # commit to dot product
    (C0, rs) = com.commit(s0)

    # now commit to A vector in pieces
    com.reset()
    alphas = []
    for i in xrange(0, len(Avec) // 3):
        alphas.append(com.commitvec(Avec[3*i:3*i+3]))
    # remainder
    rem = len(Avec) - 3 * (len(Avec) // 3)
    alphas.append(com.commitvec(Avec[-rem:]))

    # now get the masking commitment from P
    delvals = com.vecpok_init()

    # continue with Jvec-dependent piece
    Cval = com.vecpok_cont(Jvec)

    # finish PoK
    chal = com.gops.rand_scalar()
    zvals = com.vecpok_finish(1, rs, (), (), chal)

    # check PoK
    assert com.vecpok_check(alphas, delvals, zvals, Cval, C0, Jvec, chal)
    assert com.vecpok_check_lay(alphas, delvals, zvals, Cval, C0, (C0, C0, C0), Jvec, 1, (0, 0, 0, 0), chal)

def run_vecpoly_helper(com):
    wcom = commit.WitnessCommit(com)

    # generate a random vector and random point and compute mlext
    rlen = random.randint(4, 10)
    rvals = [ com.gops.rand_scalar() for _ in xrange(0, rlen) ]
    wvals = [ com.gops.rand_scalar() for _ in xrange(0, 2 ** rlen) ]
    zeta_val = VerifierIOMLExt(rvals).compute(wvals)
    szeta = com.gops.rand_scalar()
    zeta = com.gops.pow_gh(zeta_val, szeta)

    # commit to the witness
    cvals = wcom.witness_commit(wvals)
    wcom.set_rvals(rvals, 1)
    (aval, Cval) = wcom.eval_init()

    # V challenge
    chal = com.gops.rand_scalar()
    (zvals, zh, zc) = wcom.eval_finish(chal, szeta)

    # now V checks
    wcom2 = commit.WitnessCommit(com)
    wcom2.set_rvals(rvals, 1)
    assert wcom2.eval_check(cvals, aval, Cval, zvals, zh, zc, chal, zeta, 0)

def run_scalar_test(curve):
    com = commit.PedCommit(curve, None)
    com.set_field()
    assert com.gops.q == Defs.prime
    run_scalar_helper(com)
    com.gops.clear()

def run_vector_test(curve):
    com = commit.PedVecCommit(curve, None, 130)
    com.set_field()
    assert com.gops.q == Defs.prime
    run_scalar_helper(com)
    run_vector_helper(com)
    run_vecpoly_helper(com)
    com.gops.clear()

def run_tests(num_tests):
    for _ in xrange(0, num_tests):
        run_one_test()
        sys.stdout.write('.')
        sys.stdout.flush()

    print " (commit test passed)"

if __name__ == "__main__":
    run_tests(128)
