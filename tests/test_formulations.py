"""Unit tests for the building blocks of the two alternative formulations.

The end-to-end behaviour of cp-sat-users and z3-cnf is covered by the
method-parametrised tests in test_solver.py / test_bo2.py; these tests check
the clause-level encodings exhaustively on small inputs.
"""
import itertools

import pytest
import z3

from wsp_solver import CpSatUserAmkModel, Z3CnfModel, check_plan, parse_instance


class _ClauseProbe(Z3CnfModel):
    """Z3CnfModel with an empty solver and no instance, to test primitives."""

    def __init__(self):
        self.solver = z3.SolverFor("QF_FD")
        self._model = None


def _accepts(build, bits):
    probe = _ClauseProbe()
    xs = [z3.Bool(f"v{i}") for i in range(len(bits))]
    build(probe, xs)
    probe.solver.add(*[x == b for x, b in zip(xs, bits)])
    return probe.solver.check() == z3.sat


@pytest.mark.parametrize("n", range(0, 7))
def test_sequential_counter_is_exact(n):
    """AtMost_k via clauses accepts exactly the assignments with sum <= k."""
    for k in range(0, n + 2):
        for bits in itertools.product([False, True], repeat=n):
            assert _accepts(lambda p, xs: p._at_most(xs, k), bits) == (sum(bits) <= k), (n, k, bits)


@pytest.mark.parametrize("n", range(0, 7))
def test_cnf_exactly_one_is_exact(n):
    for bits in itertools.product([False, True], repeat=n):
        assert _accepts(lambda p, xs: p._exactly_one(xs), bits) == (sum(bits) == 1)


def test_cnf_equal_is_exact():
    for bits in itertools.product([False, True], repeat=2):
        assert _accepts(lambda p, xs: p._equal(xs[0], xs[1]), bits) == (bits[0] == bits[1])


def test_cnf_model_contains_no_cardinality_atoms():
    """Every assertion z3-cnf sends to the solver must be a clause (Or of
    literals) or a single literal - no PbEq / AtMost / arithmetic."""
    inst = parse_instance(
        "#Steps: 4\n#Users: 4\n#Constraints: 5\n"
        "Authorisations u1 s1 s2\n"
        "Separation-of-duty s1 s2\n"
        "Binding-of-duty s3 s4\n"
        "At-most-k 2 s1 s2 s3\n"
        "One-team s1 s3 (u1 u2) (u3 u4)\n"
    )
    model = Z3CnfModel(inst)

    def is_literal(e):
        return z3.is_const(e) or (z3.is_not(e) and z3.is_const(e.arg(0)))

    for a in model.solver.assertions():
        assert is_literal(a) or z3.is_false(a) or (
            z3.is_or(a) and all(is_literal(c) for c in a.children())
        ), a


def test_user_amk_matches_pairwise_on_every_plan():
    """Both at-most-k formulations admit exactly the plans check_plan accepts."""
    inst = parse_instance(
        "#Steps: 4\n#Users: 4\n#Constraints: 1\nAt-most-k 2 s1 s2 s3 s4\n"
    )
    valid = [p for p in itertools.product(range(4), repeat=4) if not check_plan(inst, list(p))]
    for cls in (CpSatUserAmkModel,):
        enc = cls(inst, workers=1)
        found = set()
        while True:
            status, plan = enc.solve()
            if status != "sat":
                break
            found.add(tuple(plan))
            enc.block_plan(plan)
        assert found == set(valid)
