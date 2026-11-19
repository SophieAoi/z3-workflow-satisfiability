"""End-to-end solver tests against the appendix table and reference solutions."""
import csv
from pathlib import Path

import pytest

from wsp_solver import Solver, check_plan, read_instance, transform_output

ROOT = Path(__file__).resolve().parent.parent
INSTANCES = ROOT / "instances"
EXAMPLES = INSTANCES / "examples"

with open(EXAMPLES / "expected.csv") as f:
    EXPECTED = {row["instance"]: row for row in csv.DictReader(f)}

FAMILY_INSTANCES = sorted(
    p for p in INSTANCES.glob("*-constraint*/*.txt") if not p.name.endswith("-solution.txt")
)


def assert_valid(path, d):
    assert d["sat"] == "sat"
    assert check_plan(read_instance(path), d["plan"]) == []


@pytest.mark.parametrize("name", sorted(EXPECTED))
def test_examples_sat_status(name):
    path = EXAMPLES / f"{name}.txt"
    d = Solver(str(path))
    if EXPECTED[name]["sat"] == "1":
        assert_valid(path, d)
    else:
        assert d["sat"] == "unsat"


@pytest.mark.parametrize("path", FAMILY_INSTANCES, ids=lambda p: str(p.relative_to(INSTANCES)))
def test_family_sat_status_matches_reference(path):
    reference = path.with_name(path.stem + "-solution.txt").read_text().split()[0]
    d = Solver(str(path))
    if reference == "sat":
        assert_valid(path, d)
    else:
        assert d["sat"] == "unsat"


def test_example3_unique_plan_and_output_format():
    d = Solver(str(EXAMPLES / "example3.txt"))
    assert d["sol"] == ["s1: u3", "s2: u1", "s3: u3"]  # the only solution
    out = transform_output(d)
    assert out.startswith("\r\nsat\r\ns1: u3\r\n") and out.endswith("ms")
