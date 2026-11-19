"""Workflow Satisfiability Problem (WSP) solver - COMP3070 Coursework 2.

Single-file submission. Entry point is ``Solver(filename, **kwargs)``, which
keeps the signature and return dict of the module's CW2 template.

Provenance:
  * ``Solver`` signature, the result-dict keys and the ``__main__`` demo come
    from the module's CW2_template.ipynb.
  * ``transform_output`` is copied verbatim from the module's helper.py.
  * Everything else (parser, plan checker, encodings) is our group's work.

Conventions: steps and users are 0-indexed internally (s1 -> 0, u1 -> 0) and
converted back to 1-indexed names only when producing output.
"""
from __future__ import annotations

import re
import sys
from dataclasses import dataclass, field
from time import time as currenttime

# --------------------------------------------------------------------------- #
# Instance model
# --------------------------------------------------------------------------- #


@dataclass
class Instance:
    """A parsed WSP instance (S, U, A, C), all indices 0-based."""

    n_steps: int
    n_users: int
    n_constraints_declared: int
    # user -> steps that user may perform. Users absent from this dict are
    # unrestricted (Appendix 1: "If authorisations are not specified for a
    # user, that user can be assigned any steps").
    authorisations: dict[int, frozenset[int]] = field(default_factory=dict)
    separation_of_duty: list[tuple[int, int]] = field(default_factory=list)
    binding_of_duty: list[tuple[int, int]] = field(default_factory=list)
    at_most_k: list[tuple[int, tuple[int, ...]]] = field(default_factory=list)
    # (steps T, teams U_1..U_r); teams are pairwise disjoint user sets
    one_team: list[tuple[tuple[int, ...], tuple[tuple[int, ...], ...]]] = field(
        default_factory=list
    )

    @property
    def n_constraints_parsed(self) -> int:
        return (
            len(self.authorisations)
            + len(self.separation_of_duty)
            + len(self.binding_of_duty)
            + len(self.at_most_k)
            + len(self.one_team)
        )

    def authorised(self, user: int, step: int) -> bool:
        allowed = self.authorisations.get(user)
        return allowed is None or step in allowed


# --------------------------------------------------------------------------- #
# Parsing
# --------------------------------------------------------------------------- #

_HEADER = re.compile(r"#\s*(steps|users|constraints)\s*:\s*(\d+)", re.IGNORECASE)
_STEP = re.compile(r"s(\d+)", re.IGNORECASE)
_USER = re.compile(r"u(\d+)", re.IGNORECASE)
_TEAM = re.compile(r"\(([^)]*)\)")


def _steps(text: str) -> tuple[int, ...]:
    return tuple(int(x) - 1 for x in _STEP.findall(text))


def _users(text: str) -> tuple[int, ...]:
    return tuple(int(x) - 1 for x in _USER.findall(text))


def parse_instance(text: str) -> Instance:
    """Parse the Appendix 1 format. Case-insensitive, tolerant of extra
    whitespace, CRLF line endings and stray punctuation."""
    header: dict[str, int] = {}
    lines: list[str] = []
    for raw in text.splitlines():
        line = raw.strip()
        if not line:
            continue
        m = _HEADER.match(line)
        if m:
            header[m.group(1).lower()] = int(m.group(2))
        else:
            lines.append(line)

    inst = Instance(header["steps"], header["users"], header["constraints"])
    for line in lines:
        name, _, rest = line.partition(" ")
        name = name.lower()
        if name == "authorisations":
            (user,) = _users(rest.split()[0])
            inst.authorisations[user] = frozenset(_steps(" ".join(rest.split()[1:])))
        elif name == "separation-of-duty":
            a, b = _steps(rest)
            inst.separation_of_duty.append((a, b))
        elif name == "binding-of-duty":
            a, b = _steps(rest)
            inst.binding_of_duty.append((a, b))
        elif name == "at-most-k":
            k_str, _, scope = rest.strip().partition(" ")
            inst.at_most_k.append((int(k_str), _steps(scope)))
        elif name == "one-team":
            scope = rest.split("(", 1)[0]
            teams = tuple(_users(t) for t in _TEAM.findall(rest))
            inst.one_team.append((_steps(scope), teams))
        else:
            raise ValueError(f"Unknown constraint: {line!r}")
    return inst


def read_instance(filename: str) -> Instance:
    with open(filename, encoding="utf-8") as f:
        return parse_instance(f.read())


# --------------------------------------------------------------------------- #
# Plan checking (independent of any solver - used for testing and to
# double-check every solution we output)
# --------------------------------------------------------------------------- #


def check_plan(inst: Instance, plan: list[int]) -> list[str]:
    """Return a list of violated constraints; empty list means plan is valid.

    ``plan[s]`` is the (0-based) user assigned to step ``s``.
    """
    errors: list[str] = []
    if len(plan) != inst.n_steps:
        return [f"plan has {len(plan)} steps, expected {inst.n_steps}"]
    for s, u in enumerate(plan):
        if not 0 <= u < inst.n_users:
            errors.append(f"s{s+1} assigned to unknown user u{u+1}")
        elif not inst.authorised(u, s):
            errors.append(f"u{u+1} not authorised for s{s+1}")
    for a, b in inst.separation_of_duty:
        if plan[a] == plan[b]:
            errors.append(f"SoD violated: s{a+1}, s{b+1}")
    for a, b in inst.binding_of_duty:
        if plan[a] != plan[b]:
            errors.append(f"BoD violated: s{a+1}, s{b+1}")
    for k, scope in inst.at_most_k:
        if len({plan[s] for s in scope}) > k:
            errors.append(f"At-most-{k} violated on {scope}")
    for scope, teams in inst.one_team:
        used = {plan[s] for s in scope}
        if not any(used <= set(team) for team in teams):
            errors.append(f"One-team violated on {scope}")
    return errors


# --------------------------------------------------------------------------- #
# Solving
# --------------------------------------------------------------------------- #


def Solver(filename, **kwargs):
    """Solve the WSP instance in ``filename``.

    Returns a dict with keys (template contract):
      sat      'sat' | 'unsat'
      sol      list of 's<i>: u<j>' strings ('' when unsat)
      mul_sol  'other solutions exist' | 'this is the only solution' ('' when unsat)
      exe_time '<n>ms'
    """
    inst = read_instance(filename)
    starttime = int(currenttime() * 1000)

    # TODO Phase 2+: build the model, solve, then re-solve with a blocking
    # clause to decide uniqueness. Must return plan as list[int] (0-based).
    raise NotImplementedError("Encoding not implemented yet - see README phases")


# Copied verbatim from the module's helper.py (CW2 Helper.ipynb).
def transform_output(d):
    crlf = '\r\n'
    s=[]
    s = ''.join(kk + crlf for kk in d['sol'])
    s=d['sat']+crlf+s+d['mul_sol']
    s=crlf+ s + crlf+str(d['exe_time']) if 'exe_time' in d else s
    return s


if __name__ == "__main__":
    dpath = sys.argv[1] if len(sys.argv) > 1 else "instances/examples/example3.txt"
    d = Solver(dpath, silent=False)
    print(transform_output(d))
