"""Formal pytest coverage for the Phase 5 speed-ups."""
from pathlib import Path

import pytest

from wsp_solver import (
    MULTIPLE, UNIQUE, _attempt, check_plan, prune_users, read_instance,
)

ROOT = Path(__file__).resolve().parent.parent
BOO = ROOT / "instances" / "6-constraint-BoO"

PRUNEABLE = [
    ROOT / "instances/examples/example10.txt",
    ROOT / "instances/examples/example11.txt",
    ROOT / "instances/3-constraint/0.txt",
    ROOT / "instances/5-constraint/2.txt",
    BOO / "16.txt",
    BOO / "17.txt",
]

all_methods = pytest.mark.parametrize("method", ["cp-sat", "z3-int", "z3-bool"])


def test_prune_keeps_constraint_counts():
    inst = read_instance(ROOT / "instances/examples/example11.txt")
    assert inst.n_constraints_parsed == inst.n_constraints_declared
    small, alive = prune_users(inst)
    assert alive is not None and len(alive) < inst.n_users
    assert small.n_constraints_parsed == small.n_constraints_declared


def test_prune_maps_back_to_valid_plan():
    inst = read_instance(BOO / "17.txt")  # Bo2 + prunable users
    small, alive = prune_users(inst)
    status, plan, other, mul = _attempt(small, "cp-sat", {})
    assert status == "sat"
    mapped = [alive[u] for u in plan]
    assert check_plan(inst, mapped) == []
    if other is not None:
        assert check_plan(inst, [alive[u] for u in other]) == []


@all_methods
@pytest.mark.parametrize("path", PRUNEABLE, ids=lambda p: p.name)
def test_pruning_preserves_verdict_and_uniqueness(path, method):
    full = read_instance(path)
    small, alive = prune_users(full)
    st1, p1, _, mu1 = _attempt(full, method, {})
    st2, p2, _, mu2 = _attempt(small, method, {})
    assert st1 == st2
    assert mu1 == mu2
    if st2 == "sat":
        assert check_plan(full, [alive[u] for u in p2]) == []


@all_methods
def test_portfolio_agrees_with_plain_method(method):
    path = BOO / "17.txt"
    from wsp_solver import Solver
    plain = Solver(str(path), method=method)
    port = Solver(str(path), method="portfolio")
    assert plain["sat"] == port["sat"]
    assert plain["mul_sol"] == port["mul_sol"]


def test_portfolio_falls_through_on_timeout(monkeypatch):
    """With z3-int first and a 2s limit, example17 must fall through to cp-sat
    (README: z3-int cannot finish it; cp-sat solves in ~0.3s)."""
    import wsp_solver
    from wsp_solver import Solver
    monkeypatch.setattr(wsp_solver, "PORTFOLIO_ORDER", ("z3-int", "cp-sat"))
    d = Solver(str(ROOT / "instances/examples/example17.txt"),
               method="portfolio", time_limit=2)
    assert d["sat"] == "sat"
    assert d["method_used"] == "cp-sat"


def test_portfolio_solver_key_present():
    from wsp_solver import METHODS, PORTFOLIO_ORDER
    assert set(METHODS) == {"cp-sat", "z3-int", "z3-bool"}
    assert PORTFOLIO_ORDER == ("cp-sat", "z3-bool", "z3-int")
