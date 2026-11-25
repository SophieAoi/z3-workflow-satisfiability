"""End-to-end solver tests against the appendix table and reference solutions."""
import csv
import itertools
from pathlib import Path

import pytest

from wsp_solver import (
    METHODS,
    MULTIPLE,
    UNIQUE,
    Solver,
    check_plan,
    read_instance,
    transform_output,
)

ROOT = Path(__file__).resolve().parent.parent
INSTANCES = ROOT / "instances"
EXAMPLES = INSTANCES / "examples"

with open(EXAMPLES / "expected.csv") as f:
    EXPECTED = {row["instance"]: row for row in csv.DictReader(f)}

FAMILY_INSTANCES = sorted(
    p for p in INSTANCES.glob("*-constraint*/*.txt") if not p.name.endswith("-solution.txt")
)


# Every test below runs once per solution method.
pytestmark = pytest.mark.parametrize("method", sorted(METHODS))

# Instances a method cannot finish in reasonable time (performance, not
# correctness - documented in the README benchmark notes).
TOO_SLOW = {
    "z3-int": ("4-constraint-hard/", "examples/example17.txt", "examples/example19.txt"),
    # per-user at-most-k: times out on the hard family and example19, and
    # needs 30 s+ on examples 16/17 (results/benchmark.csv)
    "cp-sat-users": (
        "4-constraint-hard/",
        "examples/example16.txt",
        "examples/example17.txt",
        "examples/example19.txt",
    ),
}


def skip_if_too_slow(method, path):
    rel = str(path.relative_to(INSTANCES))
    if rel.startswith(TOO_SLOW.get(method, ())):
        pytest.skip(f"{method} too slow on {rel}")


SMALL_INSTANCES = sorted(
    p for p in INSTANCES.glob("*-small/*.txt") if not p.name.endswith("-solution.txt")
) + sorted(EXAMPLES.glob("example[1-8].txt"))


def assert_valid(path, d):
    assert d["sat"] == "sat"
    inst = read_instance(path)
    assert check_plan(inst, d["plan"]) == []
    if d["mul_sol"] == MULTIPLE:
        assert d["other_plan"] != d["plan"]
        assert check_plan(inst, d["other_plan"]) == []
    else:
        assert d["mul_sol"] == UNIQUE


def count_solutions_brute_force(inst, stop_at=2):
    """Enumerate every authorised plan; independent of any solver."""
    choices = [
        [u for u in range(inst.n_users) if inst.authorised(u, s)]
        for s in range(inst.n_steps)
    ]
    count = 0
    for plan in itertools.product(*choices):
        if not check_plan(inst, list(plan)):
            count += 1
            if count >= stop_at:
                break
    return count


@pytest.mark.parametrize("name", sorted(EXPECTED))
def test_examples_sat_and_uniqueness(name, method):
    path = EXAMPLES / f"{name}.txt"
    skip_if_too_slow(method, path)
    d = Solver(str(path), method=method)
    if EXPECTED[name]["sat"] == "1":
        assert_valid(path, d)
        expected = UNIQUE if EXPECTED[name]["unique"] == "1" else MULTIPLE
        assert d["mul_sol"] == expected
    else:
        assert d["sat"] == "unsat"
        assert d["mul_sol"] == ""


@pytest.mark.parametrize("path", SMALL_INSTANCES, ids=lambda p: str(p.relative_to(INSTANCES)))
def test_small_instances_agree_with_brute_force(path, method):
    n = count_solutions_brute_force(read_instance(path))
    d = Solver(str(path), method=method)
    assert d["sat"] == ("sat" if n else "unsat")
    if n:
        assert d["mul_sol"] == (MULTIPLE if n > 1 else UNIQUE)


@pytest.mark.parametrize("path", FAMILY_INSTANCES, ids=lambda p: str(p.relative_to(INSTANCES)))
def test_family_sat_status_matches_reference(path, method):
    skip_if_too_slow(method, path)
    reference = path.with_name(path.stem + "-solution.txt").read_text().split()[0]
    d = Solver(str(path), method=method)
    if reference == "sat":
        assert_valid(path, d)
    else:
        assert d["sat"] == "unsat"


def test_example3_unique_plan_and_output_format(method):
    d = Solver(str(EXAMPLES / "example3.txt"), method=method)
    assert d["sol"] == ["s1: u3", "s2: u1", "s3: u3"]  # the only solution
    out = transform_output(d)
    assert out.startswith("\r\nsat\r\ns1: u3\r\ns2: u1\r\ns3: u3\r\n" + UNIQUE + "\r\n")
    assert out.endswith("ms")
