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

import z3
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


class BooleanEncoding:
    """One-hot (Boolean) encoding of the WSP, written once and shared by the
    CP-SAT backend (approach 1) and the z3 backend (approach 3).

    Decision variables: x[s, u] <=> pi(s) = u. A variable is only created for
    authorised pairs, so the Authorisations constraint is enforced by omission
    (unauthorised pairs are implicitly fixed to false).

      Assignment   forall s:            ExactlyOne_u x[s,u]
      SoD (a, b)   forall u:            not x[a,u] or not x[b,u]
      BoD (a, b)   forall u:            x[a,u] == x[b,u]
      At-most-k    pairwise "same user" vars m[s,t] over T; count the steps
                   that start a new user group; that count <= k
                   (see _add_at_most_k)
      One-team     ExactlyOne_i z[i];   forall s in T, u in U_i: x[s,u] -> z[i]
                   forall s in T, u in no team: not x[s,u]

    Subclasses supply the solver-specific primitives (``_new_bool``, ``_neg``,
    ``_clause``, ``_exactly_one``, ``_at_most``, ``_equal``) plus ``_value``
    and ``_check``. Everything below is therefore pure propositional logic
    with cardinality constraints, independent of the solver.
    """

    def __init__(self, inst: Instance):
        self.inst = inst
        self.x = {
            (s, u): self._new_bool(f"x_s{s+1}_u{u+1}")
            for s in range(inst.n_steps)
            for u in range(inst.n_users)
            if inst.authorised(u, s)
        }
        # Users eligible for each step; an empty list makes ExactlyOne
        # infeasible, which correctly reports unsat.
        self.users_of: list[list[int]] = [[] for _ in range(inst.n_steps)]
        for s, u in self.x:
            self.users_of[s].append(u)
        self.same: dict[tuple[int, int], object] = {}

        for s in range(inst.n_steps):
            self._exactly_one([self.x[s, u] for u in self.users_of[s]])
        for a, b in inst.separation_of_duty:
            self._add_sod(a, b)
        for a, b in inst.binding_of_duty:
            self._add_bod(a, b)
        for i, (k, scope) in enumerate(inst.at_most_k):
            self._add_at_most_k(i, k, scope)
        for i, (scope, teams) in enumerate(inst.one_team):
            self._add_one_team(i, scope, teams)

    # -- constraint encodings ------------------------------------------------

    def _add_sod(self, a: int, b: int) -> None:
        for u in set(self.users_of[a]) & set(self.users_of[b]):
            self._clause([self._neg(self.x[a, u]), self._neg(self.x[b, u])])

    def _add_bod(self, a: int, b: int) -> None:
        ua, ub = set(self.users_of[a]), set(self.users_of[b])
        for u in ua & ub:
            self._equal(self.x[a, u], self.x[b, u])
        # A user eligible for only one of the two steps can never be chosen.
        for s, u in [(a, u) for u in ua - ub] + [(b, u) for u in ub - ua]:
            self._clause([self._neg(self.x[s, u])])

    def _same_user(self, a: int, b: int):
        """Boolean m[a,b] with  m[a,b] -> pi(a) = pi(b)  (created once per pair).

        Encoded as  m & x[a,u] -> x[b,u]  in both directions. Only this
        direction is needed for soundness: the solver is free to set m true
        whenever the steps really do share a user, and setting it false only
        over-counts distinct users, which can never admit an invalid plan.
        """
        a, b = min(a, b), max(a, b)
        if (a, b) not in self.same:
            m = self._new_bool(f"same_s{a+1}_s{b+1}")
            self.same[a, b] = m
            for s, t in ((a, b), (b, a)):
                eligible_t = set(self.users_of[t])
                for u in self.users_of[s]:
                    if u in eligible_t:
                        self._clause([self._neg(m), self._neg(self.x[s, u]), self.x[t, u]])
                    else:
                        self._clause([self._neg(m), self._neg(self.x[s, u])])
        return self.same[a, b]

    def _add_at_most_k(self, idx: int, k: int, scope: tuple[int, ...]) -> None:
        """Count distinct users in T via step pairs, not via users.

        Order T as t_1..t_m. Let f_i mean "t_i starts a new user group", i.e.
        no earlier t_j shares its user:   f_i  or  OR_{j<i} m[t_j, t_i].
        Then  AtMost_k(f_1..f_m). Transitivity clauses on m within T tighten
        propagation. With |T| = 5 this is O(|T|^2 * |U|) clauses instead of
        one indicator per user, and it is far stronger in practice: the
        user-indicator version timed out (>20s) on example17/19 and the
        4-constraint-hard family, while this one solves them in ~1-2s.
        """
        scope = sorted(set(scope))
        f = []
        for i, t in enumerate(scope):
            fi = self._new_bool(f"amk{idx}_new_s{t+1}")
            self._clause([fi] + [self._same_user(scope[j], t) for j in range(i)])
            f.append(fi)
        for a, b, c in itertools.combinations(scope, 3):
            ab, bc, ac = self._same_user(a, b), self._same_user(b, c), self._same_user(a, c)
            for p, q, r in ((ab, bc, ac), (ab, ac, bc), (ac, bc, ab)):
                self._clause([self._neg(p), self._neg(q), r])
        self._at_most(f, k)

    def _add_one_team(self, idx, scope, teams) -> None:
        z = [self._new_bool(f"team{idx}_{i}") for i in range(len(teams))]
        self._exactly_one(z)
        team_of = {u: i for i, team in enumerate(teams) for u in team}
        for s in scope:
            for u in self.users_of[s]:
                if u in team_of:
                    self._clause([self._neg(self.x[s, u]), z[team_of[u]]])
                else:
                    self._clause([self._neg(self.x[s, u])])

    # -- solving -------------------------------------------------------------

    def solve(self) -> tuple[str, list[int] | None]:
        status = self._check()
        if status != "sat":
            return status, None
        plan = [
            next(u for u in self.users_of[s] if self._value(self.x[s, u]))
            for s in range(self.inst.n_steps)
        ]
        return "sat", plan

    def block_plan(self, plan: list[int]) -> None:
        """Forbid exactly this plan:  OR_s  not x[s, plan[s]].

        Only the x variables are blocked. Auxiliary variables (same-user,
        new-group and team selectors) are functions of, or free given, x, so
        blocking them as well could wrongly rule out the same plan with
        different auxiliary values, or miss a genuinely different plan.
        """
        self._clause([self._neg(self.x[s, u]) for s, u in enumerate(plan)])


class CpSatBooleanModel(BooleanEncoding):
    """Approach 1: the Boolean encoding solved by OR-Tools CP-SAT."""

    def __init__(self, inst: Instance, time_limit=None, workers=8, **_):
        self.model = cp_model.CpModel()
        self.solver = cp_model.CpSolver()
        self.solver.parameters.num_search_workers = workers
        if time_limit is not None:
            self.solver.parameters.max_time_in_seconds = time_limit
        super().__init__(inst)

    def _new_bool(self, name):
        return self.model.NewBoolVar(name)

    def _neg(self, lit):
        return lit.Not()

    def _clause(self, lits):
        self.model.AddBoolOr(lits)

    def _exactly_one(self, lits):
        self.model.AddExactlyOne(lits)

    def _at_most(self, lits, k):
        self.model.Add(sum(lits) <= k)

    def _equal(self, a, b):
        self.model.Add(a == b)

    def _check(self) -> str:
        status = self.solver.Solve(self.model)
        if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            return "sat"
        return "unsat" if status == cp_model.INFEASIBLE else "unknown"

    def _value(self, lit) -> bool:
        return bool(self.solver.Value(lit))


class Z3BooleanModel(BooleanEncoding):
    """Approach 3: the same Boolean encoding solved by z3.

    Cardinality constraints use z3's native pseudo-Boolean atoms
    (``PbEq``/``AtMost``) rather than arithmetic over 0/1 integers, so the
    whole problem stays propositional. ``logic`` selects the z3 solver:
    'QF_FD' (finite-domain: SAT core with native cardinality handling) by
    default, or None for z3's general-purpose solver.
    """

    def __init__(self, inst: Instance, time_limit=None, logic="QF_FD", **_):
        self.solver = z3.SolverFor(logic) if logic else z3.Solver()
        if time_limit is not None:
            self.solver.set("timeout", int(time_limit * 1000))
        self._model = None
        super().__init__(inst)

    def _new_bool(self, name):
        return z3.Bool(name)

    def _neg(self, lit):
        return z3.Not(lit)

    def _clause(self, lits):
        self.solver.add(z3.Or(lits))  # Or([]) is False

    def _exactly_one(self, lits):
        if not lits:
            self.solver.add(z3.BoolVal(False))
        else:
            self.solver.add(z3.PbEq([(l, 1) for l in lits], 1))

    def _at_most(self, lits, k):
        if len(lits) > k:
            self.solver.add(z3.AtMost(*lits, k))

    def _equal(self, a, b):
        self.solver.add(a == b)

    def _check(self) -> str:
        result = self.solver.check()
        self._model = self.solver.model() if result == z3.sat else None
        if result == z3.sat:
            return "sat"
        return "unsat" if result == z3.unsat else "unknown"

    def _value(self, lit) -> bool:
        return z3.is_true(self._model.eval(lit, model_completion=True))


class Z3IntegerModel:
    """Approach 2: z3 (SMT, linear integer arithmetic) with one integer per step.

    Decision variables: pi[s] in {0..n-1}, the user assigned to step s.
    "Exactly one user per step" holds by construction - it is a function.

      Authorisation  forall s:   OR_{u : u may do s} pi[s] = u
                     (users with no Authorisations line are allowed for all
                     steps; if every user is allowed, only the bounds remain)
      SoD (a, b)     pi[a] != pi[b]
      BoD (a, b)     pi[a] == pi[b]
      At-most-k      T = (t_1..t_m):  f_i := AND_{j<i} pi[t_j] != pi[t_i]
                     ("t_i starts a new user group"),  sum_i [f_i] <= k
      One-team       OR_i AND_{s in T} (OR_{u in U_i} pi[s] = u)

    The at-most-k formula is the same "count new groups" idea as the CP-SAT
    pairwise encoding, but here the equalities are native, so no channelling
    clauses are needed. This makes the formulation very close to the
    mathematical definition in Appendix 1.
    """

    def __init__(self, inst: Instance, time_limit=None, **_):
        self.inst = inst
        self.solver = z3.Solver()
        if time_limit is not None:
            self.solver.set("timeout", int(time_limit * 1000))
        n = inst.n_users
        self.pi = [z3.Int(f"pi_s{s+1}") for s in range(inst.n_steps)]
        add = self.solver.add

        for s, p in enumerate(self.pi):
            add(p >= 0, p < n)
            eligible = [u for u in range(n) if inst.authorised(u, s)]
            if len(eligible) < n:
                add(z3.Or([p == u for u in eligible]))  # Or([]) is False -> unsat
        for a, b in inst.separation_of_duty:
            add(self.pi[a] != self.pi[b])
        for a, b in inst.binding_of_duty:
            add(self.pi[a] == self.pi[b])
        for k, scope in inst.at_most_k:
            scope = sorted(set(scope))
            new_group = [
                z3.And([self.pi[scope[j]] != self.pi[t] for j in range(i)])
                for i, t in enumerate(scope)
            ]
            add(z3.Sum([z3.If(f, 1, 0) for f in new_group]) <= k)
        for scope, teams in inst.one_team:
            add(z3.Or([
                z3.And([z3.Or([self.pi[s] == u for u in team]) for s in scope])
                for team in teams
            ]))

    def solve(self) -> tuple[str, list[int] | None]:
        result = self.solver.check()
        if result == z3.sat:
            m = self.solver.model()
            return "sat", [m.eval(p, model_completion=True).as_long() for p in self.pi]
        return ("unsat" if result == z3.unsat else "unknown"), None

    def block_plan(self, plan: list[int]) -> None:
        """Forbid exactly this plan:  OR_s  pi[s] != plan[s]."""
        self.solver.add(z3.Or([p != u for p, u in zip(self.pi, plan)]))


METHODS = {
    "cp-sat": CpSatBooleanModel,
    "z3-int": Z3IntegerModel,
    "z3-bool": Z3BooleanModel,
}
MULTIPLE = "other solutions exist"
UNIQUE = "this is the only solution"


def Solver(filename, **kwargs):
    """Solve the WSP instance in ``filename`` and decide uniqueness.

    Uniqueness: after the first plan is found, it is forbidden with a
    blocking clause and the same model is solved again. SAT on the second
    call means another plan exists; UNSAT proves the first plan is unique.

    Optional kwargs:
      method      one of METHODS (default 'cp-sat')
      time_limit  seconds per solver call (default: none)
      workers     CP-SAT search workers (default: 8)

    Returns a dict with keys (template contract):
      sat      'sat' | 'unsat' | 'unknown' (time limit hit)
      sol      list of 's<i>: u<j>' strings ('' when unsat)
      mul_sol  MULTIPLE | UNIQUE | '' (unsat, or limit hit on second call)
      exe_time '<n>ms'  (parse + build + both solves)
    plus extra keys ignored by transform_output:
      plan            0-based plan list, or None
      other_plan      a second distinct plan when MULTIPLE, else None
    """
    starttime = int(currenttime() * 1000)
    inst = read_instance(filename)
    enc = METHODS[kwargs.get("method", "cp-sat")](inst, **kwargs)

    d = dict(sat="unsat", sol="", mul_sol="", plan=None, other_plan=None)
    status, plan = enc.solve()
    d["sat"] = status
    if status == "sat":
        # Defensive: never output a plan the independent checker rejects.
        violations = check_plan(inst, plan)
        assert not violations, f"encoding bug: {violations}"
        d["plan"] = plan
        d["sol"] = [f"s{s+1}: u{u+1}" for s, u in enumerate(plan)]

        enc.block_plan(plan)
        status2, other = enc.solve()
        if status2 == "sat":
            assert other != plan and not check_plan(inst, other), "blocking bug"
            d["mul_sol"] = MULTIPLE
            d["other_plan"] = other
        elif status2 == "unsat":
            d["mul_sol"] = UNIQUE
        # else: time limit on the second call -> uniqueness unknown, leave ''

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
    # Usage: python wsp_solver.py [instance_file] [method]
    dpath = sys.argv[1] if len(sys.argv) > 1 else "instances/examples/example3.txt"
    method = sys.argv[2] if len(sys.argv) > 2 else "cp-sat"
    d = Solver(dpath, method=method, silent=False)
    print(transform_output(d))
