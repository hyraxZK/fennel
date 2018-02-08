#!/usr/bin/python
#
# (C) 2017 Riad S. Wahby <rsw@cs.stanford.edu>
#
# test log inner product

# hack: this test lives in a subdir
try:
    import random
    import sys
    import os.path
except:
    assert False
else:
    sys.path.insert(1, os.path.abspath(os.path.join(sys.path[0], os.pardir)))

from libfennel import commit, iomlext, util
from libfennel.defs import Defs

ecsdir = os.path.join(os.path.join(os.path.dirname(os.path.realpath(__file__))), '../libfennel/ecslib/')

def run_one_test(curve):
    com = commit.PedVecCommit(curve, None, 130)
    com.set_field()
    assert Defs.prime == com.gops.q
    run_helper(com, commit.WitnessLogCommitShort)
    run_helper(com, commit.WitnessLogCommitLong)

def run_helper(com, ctype):
    bitdiv = random.choice((0, 2, 3, 4, 5))
    lw = ctype(com, bitdiv)

    logn = util.clog2(com.gops.maxlen)
    if 2 ** logn > com.gops.maxlen:
        logn -= 1
    rvals = [ com.gops.rand_scalar() for _ in xrange(0, logn) ]
    r0val = com.gops.rand_scalar()
    avals = [ com.gops.rand_scalar() for _ in xrange(0, 2**logn) ]
    dpval = (iomlext.VerifierIOMLExt(rvals).compute(avals) * r0val + 3) % Defs.prime

    # commit to avals and dpval
    Aval = lw.witness_commit(avals)
    (Zval, rZval) = com.commit(dpval)

    # run prover side of commitment
    lw.set_rvals_p(rvals, r0val, rZval)
    redc_vals = []
    chal_vals = []
    cont = True
    while cont:
        redc_vals.append(lw.redc_init())
        chal_vals.append(com.gops.rand_scalar())
        cont = lw.redc_cont_p(chal_vals[-1])

    fin_init_val = lw.fin_init()
    fin_chal = com.gops.rand_scalar()
    fin_finish_val = lw.fin_finish(fin_chal)

    # run verifier side of commitment
    lwv = ctype(com, bitdiv)
    lwv.set_rvals_v(rvals, r0val, Aval, Zval, 3)
    for (rv, cv) in zip(redc_vals, chal_vals):
        cont = lwv.redc_cont_v(cv, rv)

    assert lwv.fin_check(fin_chal, fin_init_val, fin_finish_val)

def run_tests(num_tests):
    for _ in xrange(0, num_tests):
        run_one_test(random.choice(('m159', 'm191', 'm221', 'm255')))
        sys.stdout.write('.')
        sys.stdout.flush()

    print " (logwit test passed)"

if __name__ == "__main__":
    nruns = 128
    if len(sys.argv) > 1:
        nruns = int(sys.argv[1])
    run_tests(nruns)
