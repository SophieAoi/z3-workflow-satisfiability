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

import itertools
import re
import sys
from dataclasses import dataclass, field
from time import time as currenttime

from ortools.sat.python import cp_model

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


class CpSatBooleanModel:
    """Approach 1: OR-Tools CP-SAT with a Boolean (one-hot) encoding.

    Decision variables: x[s, u] <=> pi(s) = u. A variable is only created for
    authorised pairs, so the Authorisations constraint is enforced by omission
    (unauthorised pairs are implicitly fixed to false).

      Assignment   forall s:            ExactlyOne_u x[s,u]
      SoD (a, b)   forall u:            x[a,u] + x[b,u] <= 1
      BoD (a, b)   forall u:            x[a,u] == x[b,u]
      At-most-k    pairwise "same user" vars m[s,t] over T; count the steps
                   that start a new user group; that count <= k
                   (see _add_at_most_k)
      One-team     ExactlyOne_i z[i];   forall s in T, u in U_i: x[s,u] -> z[i]
                   forall s in T, u in no team: x[s,u] = 0
    """

    def __init__(self, inst: Instance):
        self.inst = inst
        self.model = cp_model.CpModel()
        m = self.model
        self.x: dict[tuple[int, int], cp_model.IntVar] = {
            (s, u): m.NewBoolVar(f"x_s{s+1}_u{u+1}")
            for s in range(inst.n_steps)
            for u in range(inst.n_users)
            if inst.authorised(u, s)
        }
        # Users eligible for each step; an empty list makes ExactlyOne
        # infeasible, which correctly reports unsat.
        self.users_of: list[list[int]] = [[] for _ in range(inst.n_steps)]
        for s, u in self.x:
            self.users_of[s].append(u)
        self.same: dict[tuple[int, int], cp_model.IntVar] = {}

        for s in range(inst.n_steps):
            m.AddExactlyOne(self.x[s, u] for u in self.users_of[s])
        for a, b in inst.separation_of_duty:
            self._add_sod(a, b)
        for a, b in inst.binding_of_duty:
            self._add_bod(a, b)
        for i, (k, scope) in enumerate(inst.at_most_k):
            self._add_at_most_k(i, k, scope)
        for i, (scope, teams) in enumerate(inst.one_team):
            self._add_one_team(i, scope, teams)

    def _add_sod(self, a: int, b: int) -> None:
        for u in set(self.users_of[a]) & set(self.users_of[b]):
            self.model.AddAtMostOne(self.x[a, u], self.x[b, u])

    def _add_bod(self, a: int, b: int) -> None:
        ua, ub = set(self.users_of[a]), set(self.users_of[b])
        for u in ua & ub:
            self.model.Add(self.x[a, u] == self.x[b, u])
        # A user eligible for only one of the two steps can never be chosen.
        for s, u in [(a, u) for u in ua - ub] + [(b, u) for u in ub - ua]:
            self.model.Add(self.x[s, u] == 0)

    def _same_user(self, a: int, b: int) -> cp_model.IntVar:
        """Boolean m[a,b] with  m[a,b] -> pi(a) = pi(b)  (created once per pair).

        Encoded as  m & x[a,u] -> x[b,u]  in both directions. Only this
        direction is needed for soundness: the solver is free to set m true
        whenever the steps really do share a user, and setting it false only
        over-counts distinct users, which can never admit an invalid plan.
        """
        a, b = min(a, b), max(a, b)
        if (a, b) not in self.same:
            m = self.model.NewBoolVar(f"same_s{a+1}_s{b+1}")
            self.same[a, b] = m
            for s, t in ((a, b), (b, a)):
                eligible_t = set(self.users_of[t])
                for u in self.users_of[s]:
                    if u in eligible_t:
                        self.model.AddBoolOr([m.Not(), self.x[s, u].Not(), self.x[t, u]])
                    else:
                        self.model.AddBoolOr([m.Not(), self.x[s, u].Not()])
        return self.same[a, b]

    def _add_at_most_k(self, idx: int, k: int, scope: tuple[int, ...]) -> None:
        """Count distinct users in T via step pairs, not via users.

        Order T as t_1..t_m. Let f_i mean "t_i starts a new user group", i.e.
        no earlier t_j shares its user:   f_i  or  OR_{j<i} m[t_j, t_i].
        Then  sum_i f_i <= k. Transitivity clauses on m within T tighten
        propagation. With |T| = 5 this is O(|T|^2 * |U|) clauses instead of
        one indicator per user, and it is far stronger in practice: the
        user-indicator version timed out (>20s) on example17/19 and the
        4-constraint-hard family, while this one solves them in ~1-2s.
        """
        scope = sorted(set(scope))
        f = []
        for i, t in enumerate(scope):
            fi = self.model.NewBoolVar(f"amk{idx}_new_s{t+1}")
            self.model.AddBoolOr([fi] + [self._same_user(scope[j], t) for j in range(i)])
            f.append(fi)
        for a, b, c in itertools.combinations(scope, 3):
            ab, bc, ac = self._same_user(a, b), self._same_user(b, c), self._same_user(a, c)
            for p, q, r in ((ab, bc, ac), (ab, ac, bc), (ac, bc, ab)):
                self.model.AddBoolOr([p.Not(), q.Not(), r])
        self.model.Add(sum(f) <= k)

    def _add_one_team(self, idx, scope, teams) -> None:
        z = [self.model.NewBoolVar(f"team{idx}_{i}") for i in range(len(teams))]
        self.model.AddExactlyOne(z)
        team_of = {u: i for i, team in enumerate(teams) for u in team}
        for s in scope:
            for u in self.users_of[s]:
                if u in team_of:
                    self.model.AddImplication(self.x[s, u], z[team_of[u]])
                else:
                    self.model.Add(self.x[s, u] == 0)

    def extract_plan(self, solver: cp_model.CpSolver) -> list[int]:
        return [
            next(u for u in self.users_of[s] if solver.Value(self.x[s, u]))
            for s in range(self.inst.n_steps)
        ]


def Solver(filename, **kwargs):
    """Solve the WSP instance in ``filename``.

    Optional kwargs:
      time_limit  seconds before CP-SAT gives up (default: none)
      workers     CP-SAT search workers (default: 8)

    Returns a dict with keys (template contract):
      sat      'sat' | 'unsat'
      sol      list of 's<i>: u<j>' strings ('' when unsat)
      mul_sol  'other solutions exist' | 'this is the only solution' ('' when unsat)
      exe_time '<n>ms'  (parse + build + solve)
    """
    starttime = int(currenttime() * 1000)
    inst = read_instance(filename)
    enc = CpSatBooleanModel(inst)

    solver = cp_model.CpSolver()
    solver.parameters.num_search_workers = kwargs.get("workers", 8)
    if "time_limit" in kwargs:
        solver.parameters.max_time_in_seconds = kwargs["time_limit"]
    status = solver.Solve(enc.model)

    d = dict(sat="unsat", sol="", mul_sol="", plan=None)
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        plan = enc.extract_plan(solver)
        # Defensive: never output a plan the independent checker rejects.
        violations = check_plan(inst, plan)
        assert not violations, f"encoding bug: {violations}"
        d["sat"] = "sat"
        d["plan"] = plan
        d["sol"] = [f"s{s+1}: u{u+1}" for s, u in enumerate(plan)]
        # TODO Phase 2: re-solve with a blocking clause to fill mul_sol.
    elif status != cp_model.INFEASIBLE:
        d["sat"] = "unknown"  # time limit hit before a verdict

    d["exe_time"] = f"{int(currenttime() * 1000) - starttime}ms"
    return d


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
