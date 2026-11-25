"""Tests for the parser and the independent plan checker."""
import csv
from pathlib import Path

import pytest

from wsp_solver import check_plan, parse_instance, read_instance

ROOT = Path(__file__).resolve().parent.parent
INSTANCES = ROOT / "instances"
EXAMPLES = INSTANCES / "examples"

ALL_INSTANCE_FILES = sorted(
    p for p in INSTANCES.rglob("*.txt") if not p.name.endswith("-solution.txt")
)
SOLUTION_FILES = sorted(INSTANCES.rglob("*-solution.txt"))


def load_expected():
    with open(EXAMPLES / "expected.csv") as f:
        return {row["instance"]: row for row in csv.DictReader(f)}


def read_solution(path: Path):
    """Return None for 'unsat', else a 0-based plan list."""
    lines = [l.strip() for l in path.read_text().splitlines() if l.strip()]
    if lines[0] == "unsat":
        return None
    pairs = [l.split(":") for l in lines[1:]]
    plan = {int(s.strip()[1:]) - 1: int(u.strip()[1:]) - 1 for s, u in pairs}
    return [plan[i] for i in range(len(plan))]


def test_appendix_example3():
    inst = read_instance(EXAMPLES / "example3.txt")
    assert (inst.n_steps, inst.n_users) == (3, 4)
    assert inst.authorisations == {0: {0, 1}, 1: {2}, 3: {2}}
    assert inst.binding_of_duty == [(0, 2)]
    assert inst.separation_of_duty == [(0, 1), (1, 2)]
    # The unique solution given in Appendix 1: s1->u3, s2->u1, s3->u3
    assert check_plan(inst, [2, 0, 2]) == []
    assert check_plan(inst, [0, 0, 2]) != []


def test_format_tolerance():
    text = (
        "#Steps: 4\n#Users: 8\n#Constraints: 3\n"
        "AUTHORISATIONS   u1    s1 s2.\n"
        "at-most-k 2 s1 s2 s3\n"
        "One-team s1 s2 s4 (u1 u2) (u5 u7 u8) (u3)\n"
    )
    inst = parse_instance(text)
    assert inst.authorisations == {0: {0, 1}}
    assert inst.at_most_k == [(2, (0, 1, 2))]
    assert inst.one_team == [((0, 1, 3), ((0, 1), (4, 6, 7), (2,)))]


def test_tabs_and_irregular_whitespace():
    """The appendix says extra whitespace should be ignored, so tabs too."""
    text = (
        "#Steps:3\n#users: 4\n#Constraints: 4\n\n"
        "authorisations\tu1\ts1 s2.\n"
        "At-most-k\t2\ts1  s2\ts3\n"
        "binding-of-duty\ts1\ts3\n"
        "One-team\ts1 s2\t(u1\tu2)  (u3)\n"
    )
    inst = parse_instance(text)
    assert inst.authorisations == {0: {0, 1}}
    assert inst.at_most_k == [(2, (0, 1, 2))]
    assert inst.binding_of_duty == [(0, 2)]
    assert inst.one_team == [((0, 1), ((0, 1), (2,)))]


def test_empty_authorisation_means_no_steps():
    inst = parse_instance("#Steps: 1\n#Users: 2\n#Constraints: 1\nAuthorisations u1\n")
    assert not inst.authorised(0, 0)
    assert inst.authorised(1, 0)  # u2 unrestricted


@pytest.mark.parametrize("path", ALL_INSTANCE_FILES, ids=lambda p: str(p.relative_to(INSTANCES)))
def test_every_instance_parses_with_declared_constraint_count(path):
    inst = read_instance(path)
    assert inst.n_constraints_parsed == inst.n_constraints_declared


@pytest.mark.parametrize("name,row", sorted(load_expected().items()))
def test_example_constraint_types_match_appendix_table(name, row):
    inst = read_instance(EXAMPLES / f"{name}.txt")
    present = {
        "auth": bool(inst.authorisations),
        "bod": bool(inst.binding_of_duty),
        "sod": bool(inst.separation_of_duty),
        "at_most_k": bool(inst.at_most_k),
        "one_team": bool(inst.one_team),
    }
    assert present == {k: row[k] == "1" for k in present}


@pytest.mark.parametrize("path", SOLUTION_FILES, ids=lambda p: str(p.relative_to(INSTANCES)))
def test_reference_solutions_pass_checker(path):
    """check_plan should accept every sat solution from Moodle.
    (So we know check_plan is right before using it on our own answers.)"""
    plan = read_solution(path)
    if plan is None:
        pytest.skip("unsat instance")
    inst = read_instance(path.with_name(path.name.replace("-solution", "")))
    assert check_plan(inst, plan) == []
