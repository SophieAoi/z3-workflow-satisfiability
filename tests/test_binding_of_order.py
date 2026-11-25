"""Tests for our sixth constraint type, binding of order (pi(a) <= pi(b)).

The 6-constraint-BoO instances were made with generate_bo2_instances.py and
their answers were worked out by brute force, so we compare against those.
"""
import itertools
from pathlib import Path

import pytest

from wsp_solver import (
    METHODS,
    MULTIPLE,
    UNIQUE,
    Solver,
    check_plan,
    parse_instance,
    read_instance,
)

all_methods = pytest.mark.parametrize("method", sorted(METHODS))

ROOT = Path(__file__).resolve().parent.parent
BOO = ROOT / "instances" / "6-constraint-BoO"
BOO_INSTANCES = sorted(
    (p for p in BOO.glob("*.txt") if p.stem.isdigit()), key=lambda p: int(p.stem)
)


def read_solution(path):
    lines = [l.strip() for l in path.read_text().splitlines() if l.strip()]
    if lines[0] == "unsat":
        return None
    pairs = [l.split(":") for l in lines[1:]]
    plan = {int(s.strip()[1:]) - 1: int(u.strip()[1:]) - 1 for s, u in pairs}
    return [plan[i] for i in range(len(plan))]


def test_parse_binding_of_order():
    inst = parse_instance("#Steps: 2\n#Users: 2\n#Constraints: 1\nBINDING-OF-ORDER s1 s2\n")
    assert inst.binding_of_order == [(0, 1)]
    assert inst.n_constraints_parsed == 1


def test_check_plan_bo2_semantics():
    inst = parse_instance(
        "#Steps: 2\n#Users: 3\n#Constraints: 1\nBinding-of-order s1 s2\n"
    )
    assert check_plan(inst, [0, 2]) == []   # u1 <= u3
    assert check_plan(inst, [1, 1]) == []   # equal users allowed (no SoD here)
    assert any("Bo2" in e for e in check_plan(inst, [2, 0]))  # u3 <= u1 fails


@all_methods
@pytest.mark.parametrize("path", BOO_INSTANCES, ids=lambda p: p.name)
def test_boo_family_agrees_with_reference(path, method):
    reference = read_solution(path.with_name(path.stem + "-solution.txt"))
    d = Solver(str(path), method=method)
    if reference is None:
        assert d["sat"] == "unsat"
        assert d["mul_sol"] == ""
    else:
        assert d["sat"] == "sat"
        inst = read_instance(path)
        assert check_plan(inst, d["plan"]) == []
        assert d["mul_sol"] in (UNIQUE, MULTIPLE)


@all_methods
def test_boo_tight_instances_are_unique(method):
    """In instances 16-19 each step has one allowed user, in increasing order."""
    for path in BOO_INSTANCES[16:]:
        d = Solver(str(path), method=method)
        assert d["sat"] == "sat"
        assert d["mul_sol"] == UNIQUE, path.name


@all_methods
@pytest.mark.parametrize("path", BOO_INSTANCES[:10], ids=lambda p: p.name)
def test_boo_small_instances_cross_checked_with_brute_force(path, method):
    inst = read_instance(path)
    choices = [[u for u in range(inst.n_users) if inst.authorised(u, s)]
               for s in range(inst.n_steps)]
    n_valid = 0
    for plan in itertools.product(*choices):
        if not check_plan(inst, list(plan)):
            n_valid += 1
            if n_valid >= 2:
                break
    d = Solver(str(path), method=method)
    assert d["sat"] == ("sat" if n_valid else "unsat")
    if n_valid:
        assert d["mul_sol"] == (UNIQUE if n_valid == 1 else MULTIPLE)
