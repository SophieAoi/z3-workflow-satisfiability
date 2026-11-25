"""COMP3070 Coursework 2: Workflow Satisfiability Problem solver.

Call Solver(filename, **kwargs). It has the same signature and returns the
same dict as the CW2 template.

From the module:
  - the Solver signature, the result dict keys and the __main__ part are
    based on CW2_template.ipynb
  - transform_output is copied unchanged from helper.py
Everything else was written by our group.

Steps and users are numbered from 0 inside the code (s1 -> 0, u1 -> 0) and
from 1 again in the output.
"""
from __future__ import annotations

import itertools
import re
import sys
from dataclasses import dataclass, field
from time import time as currenttime
from typing import Protocol

from ortools.sat.python import cp_model

# z3 is only used by the z3 methods. cp-sat (the default) only needs
# OR-Tools, so the file still runs if z3 isn't installed.
try:
    import z3
except ImportError:
    z3 = None


def _require_z3() -> None:
    if z3 is None:
        raise ImportError(
            "this method needs the z3 solver: pip install z3-solver "
            "(the default method 'cp-sat' only needs ortools)"
        )


# --------------------------------------------------------------------------- #
# Instance model
# --------------------------------------------------------------------------- #


@dataclass
class Instance:
    """A parsed instance. Steps and users are 0-based."""

    n_steps: int
    n_users: int
    n_constraints_declared: int
    # user -> steps they are allowed to do. Users not in here can do any
    # step (Appendix 1).
    authorisations: dict[int, frozenset[int]] = field(default_factory=dict)
    separation_of_duty: list[tuple[int, int]] = field(default_factory=list)
    binding_of_duty: list[tuple[int, int]] = field(default_factory=list)
    # binding of order (a, b): pi(a) <= pi(b), comparing user numbers
    binding_of_order: list[tuple[int, int]] = field(default_factory=list)
    at_most_k: list[tuple[int, tuple[int, ...]]] = field(default_factory=list)
    # (steps T, teams). Teams don't overlap.
    one_team: list[tuple[tuple[int, ...], tuple[tuple[int, ...], ...]]] = field(
        default_factory=list
    )

    @property
    def n_constraints_parsed(self) -> int:
        return (
            len(self.authorisations)
            + len(self.separation_of_duty)
            + len(self.binding_of_duty)
            + len(self.binding_of_order)
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
    """Read an instance in the Appendix 1 format.

    Ignores case, extra spaces/tabs, Windows line endings and stray
    punctuation such as a full stop at the end of a line.
    """
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
        # split on any whitespace, so tabs work too
        name, rest = (line.split(None, 1) + [""])[:2]
        name = name.lower()
        if name in ("authorisations", "authorizations"):
            (user,) = _users(rest.split()[0])
            inst.authorisations[user] = frozenset(_steps(" ".join(rest.split()[1:])))
        elif name == "separation-of-duty":
            a, b = _steps(rest)
            inst.separation_of_duty.append((a, b))
        elif name == "binding-of-duty":
            a, b = _steps(rest)
            inst.binding_of_duty.append((a, b))
        elif name == "binding-of-order":
            a, b = _steps(rest)
            inst.binding_of_order.append((a, b))
        elif name == "at-most-k":
            k_str, scope = (rest.split(None, 1) + [""])[:2]
            k = int(re.match(r"\d+", k_str).group())
            inst.at_most_k.append((k, _steps(scope)))
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
# Plan checking. Doesn't use a solver, so we can use it to check the
# solvers' answers.
# --------------------------------------------------------------------------- #


def check_plan(inst: Instance, plan: list[int]) -> list[str]:
    """Return the constraints the plan breaks (an empty list means it's valid).

    plan[s] is the user given to step s.
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
    for a, b in inst.binding_of_order:
        if plan[a] > plan[b]:
            errors.append(f"Bo2 violated: s{a+1} on u{plan[a]+1}, s{b+1} on u{plan[b]+1}")
    for k, scope in inst.at_most_k:
        if len({plan[s] for s in scope}) > k:
            errors.append(f"At-most-{k} violated on {scope}")
    for scope, teams in inst.one_team:
        used = {plan[s] for s in scope}
        if not any(used <= set(team) for team in teams):
            errors.append(f"One-team violated on {scope}")
    return errors


# --------------------------------------------------------------------------- #
# Preprocessing: remove users who can't do any step
# --------------------------------------------------------------------------- #


def prune_users(inst: Instance) -> tuple[Instance, list[int] | None]:
    """Remove users whose Authorisations line has no steps.

    They can't be in any plan, so removing them doesn't change the answer.
    The remaining users keep their order, so binding of order still works.
    Returns (smaller_instance, alive), where alive[i] is the original number
    of user i, or (inst, None) if there was nothing to remove.
    """
    prunable = {
        u
        for u, steps in inst.authorisations.items()
        if not steps
    }
    if not prunable:
        return inst, None
    alive = [u for u in range(inst.n_users) if u not in prunable]
    pos = {u: i for i, u in enumerate(alive)}
    # each removed user had one Authorisations line
    small = Instance(inst.n_steps, len(alive),
                     inst.n_constraints_declared - len(prunable))
    small.authorisations = {
        pos[u]: steps for u, steps in inst.authorisations.items() if u in pos
    }
    small.separation_of_duty = list(inst.separation_of_duty)
    small.binding_of_duty = list(inst.binding_of_duty)
    small.binding_of_order = list(inst.binding_of_order)
    small.at_most_k = list(inst.at_most_k)
    small.one_team = [
        (scope, tuple(tuple(pos[u] for u in team if u in pos) for team in teams))
        for scope, teams in inst.one_team
    ]
    return small, alive


# --------------------------------------------------------------------------- #
# Solving
# --------------------------------------------------------------------------- #


class Model(Protocol):
    """What every method in METHODS provides.

    solve() returns ("sat", plan), ("unsat", None), or ("unknown", None) if
    it ran out of time. block_plan(plan) rules out that one plan, so calling
    solve() again tells us if there is another solution.
    """

    def __init__(self, inst: Instance, **kwargs) -> None: ...

    def solve(self) -> tuple[str, list[int] | None]: ...

    def block_plan(self, plan: list[int]) -> None: ...


class BooleanEncoding:
    """One-hot (Boolean) formulation, used by cp-sat, z3-bool, cp-sat-users
    and z3-cnf.

    x[s, u] is true when step s is given to user u. We only make x[s, u] if
    u is allowed to do s, which takes care of the Authorisations constraint.

      Assignment   forall s:            ExactlyOne_u x[s,u]
      SoD (a, b)   forall u:            not x[a,u] or not x[b,u]
      BoD (a, b)   forall u:            x[a,u] == x[b,u]
      Bo2 (a,b)    per-step chain ord[s][u] meaning "pi(s) >= u";
                   forall u >= 1:       ord[a][u] -> ord[b][u]
      At-most-k    pairwise "same user" vars m[s,t] over T; count the steps
                   that start a new user group; that count <= k
                   (see _add_at_most_k)
      One-team     ExactlyOne_i z[i];   forall s in T, u in U_i: x[s,u] -> z[i]
                   forall s in T, u in no team: not x[s,u]

    The constraints are built from a few basic operations (_new_bool, _neg,
    _clause, _exactly_one, _at_most, _equal, plus _check and _value), and
    each subclass implements these for its solver.

    AMK_ENCODING picks the at-most-k version: "pairwise" (default) or "users".
    """

    AMK_ENCODING = "pairwise"

    def __init__(self, inst: Instance):
        self.inst = inst
        self.x = {
            (s, u): self._new_bool(f"x_s{s+1}_u{u+1}")
            for s in range(inst.n_steps)
            for u in range(inst.n_users)
            if inst.authorised(u, s)
        }
        # users allowed to do each step (if a step has none, ExactlyOne
        # can't be satisfied and we get unsat, which is right)
        self.users_of: list[list[int]] = [[] for _ in range(inst.n_steps)]
        for s, u in self.x:
            self.users_of[s].append(u)
        self.same: dict[tuple[int, int], object] = {}
        # ord[s, u] means pi(s) >= u. Only made for steps that are in a
        # binding of order constraint.
        self._ord: dict[tuple[int, int], object] = {}
        self._ord_built: set[int] = set()

        for s in range(inst.n_steps):
            self._exactly_one([self.x[s, u] for u in self.users_of[s]])
        for a, b in inst.separation_of_duty:
            self._add_sod(a, b)
        for a, b in inst.binding_of_duty:
            self._add_bod(a, b)
        for a, b in inst.binding_of_order:
            self._add_bo2(a, b)
        add_amk = {
            "pairwise": self._add_at_most_k,
            "users": self._add_at_most_k_users,
        }[self.AMK_ENCODING]
        for i, (k, scope) in enumerate(inst.at_most_k):
            add_amk(i, k, scope)
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
        # a user who can only do one of the two steps can't be used for it
        for s, u in [(a, u) for u in ua - ub] + [(b, u) for u in ub - ua]:
            self._clause([self._neg(self.x[s, u])])

    def _ensure_ord(self, s: int) -> None:
        """Make the variables ord[s, u] (meaning pi(s) >= u) for step s.

        ord[s, u] <-> ord[s, u-1] and not x[s, u-1], with ord[s, 0] true.
        Because it's an <->, ord is fixed once x is, so block_plan only has
        to block x. Uses one variable per user.
        """
        if s in self._ord_built:
            return
        self._ord_built.add(s)
        prev = None  # None stands for ord[s][0], which is true
        for u in range(1, self.inst.n_users):
            cur = self._new_bool(f"ord_s{s+1}_ge_u{u+1}")
            self._ord[s, u] = cur
            xu = self.x.get((s, u - 1))  # None if u-1 can't do s
            # cur -> prev
            if prev is not None:
                self._clause([self._neg(cur), prev])
            # cur -> pi(s) != u-1
            if xu is not None:
                self._clause([self._neg(cur), self._neg(xu)])
            # prev and pi(s) != u-1 -> cur (prev None means true,
            # xu None means pi(s) != u-1 is always true)
            if xu is None:
                self._clause([cur] if prev is None else [self._neg(prev), cur])
            elif prev is None:
                self._clause([xu, cur])
            else:
                self._clause([self._neg(prev), xu, cur])
            prev = cur

    def _add_bo2(self, a: int, b: int) -> None:
        """Binding of order pi(a) <= pi(b): ord[a, u] -> ord[b, u] for all u >= 1."""
        self._ensure_ord(a)
        self._ensure_ord(b)
        for u in range(1, self.inst.n_users):
            self._clause([self._neg(self._ord[a, u]), self._ord[b, u]])

    def _same_user(self, a: int, b: int):
        """Variable m[a, b] meaning steps a and b have the same user.

        We only add m -> pi(a) = pi(b), as  m and x[a,u] -> x[b,u]  (and the
        same the other way). The other direction isn't needed: if m is false
        when the users are the same, we count one user too many, which can
        only make the constraint stricter, never let a wrong plan through.
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
        """At-most-k, counted over pairs of steps instead of over users.

        Take T as t_1..t_m. f_i means t_i has a user that no earlier step in T
        has:   f_i or m[t_1, t_i] or ... or m[t_(i-1), t_i].
        Then at most k of the f_i can be true. We also add transitivity
        clauses for m. This was a lot faster than the per-user version on the
        big instances (see cp-sat-users).
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

    def _add_at_most_k_users(self, idx: int, k: int, scope: tuple[int, ...]) -> None:
        """At-most-k, counted over users (the other version).

        y[u] means user u does a step in T:  x[s,u] -> y[u] for s in T, and
        at most k of the y[u] are true. y[u] can be true for a user who
        isn't used, but that only counts too many, so it's still correct.
        This is closest to the definition, but slow when lots of users are
        allowed to do the steps, so it's not the default.
        """
        users = sorted({u for s in scope for u in self.users_of[s]})
        y = {u: self._new_bool(f"amk{idx}_used_u{u+1}") for u in users}
        for s in set(scope):
            for u in self.users_of[s]:
                self._clause([self._neg(self.x[s, u]), y[u]])
        self._at_most(list(y.values()), k)

    def _add_one_team(
        self,
        idx: int,
        scope: tuple[int, ...],
        teams: tuple[tuple[int, ...], ...],
    ) -> None:
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
        """Rule out this plan:  not x[0, plan[0]] or not x[1, plan[1]] or ...

        Only the x variables go in the clause. If we also blocked the helper
        variables (m, f, z, ord) we could miss a different plan or allow
        the same plan again with different helper values.
        """
        self._clause([self._neg(self.x[s, u]) for s, u in enumerate(plan)])


class CpSatBooleanModel(BooleanEncoding):
    """cp-sat: the one-hot formulation solved with OR-Tools CP-SAT."""

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


class CpSatUserAmkModel(CpSatBooleanModel):
    """cp-sat-users: same as cp-sat but with the per-user at-most-k.

    Only the at-most-k part is different, so comparing the two shows the
    effect of the at-most-k formulation on its own.
    """

    AMK_ENCODING = "users"


class Z3BooleanModel(BooleanEncoding):
    """z3-bool: the one-hot formulation solved with z3.

    Counting constraints use z3's PbEq and AtMost, so everything stays
    Boolean. logic is the z3 solver to use: 'QF_FD' by default (it was
    faster in our tests), or None for z3's normal solver.
    """

    def __init__(self, inst: Instance, time_limit=None, logic="QF_FD", **_):
        _require_z3()
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


class Z3CnfModel(Z3BooleanModel):
    """z3-cnf: the one-hot formulation written only as clauses (CNF).

    Same as z3-bool, but the counting constraints are turned into clauses:

      a <-> b             (not a or b) and (a or not b)
      at most k true      sequential counter (Sinz, 2005), with helper
                          variables r[i][j] = "at least j+1 of x_1..x_(i+1)
                          are true"; about n*k clauses
      exactly one true    (x_1 or ... or x_n) and at most 1 true
    """

    def _equal(self, a, b):
        self._clause([self._neg(a), b])
        self._clause([a, self._neg(b)])

    def _exactly_one(self, lits):
        self._clause(lits)  # empty list -> empty clause -> unsat
        self._at_most(lits, 1)

    def _at_most(self, lits, k):
        """sum(lits) <= k as clauses, using a sequential counter (Sinz, 2005)."""
        n = len(lits)
        if k >= n:
            return
        if k == 0:
            for l in lits:
                self._clause([self._neg(l)])
            return
        # r[i][j]: at least j+1 of lits[0..i] are true
        r = [[z3.FreshBool("sc") for _ in range(k)] for _ in range(n - 1)]
        neg = self._neg
        self._clause([neg(lits[0]), r[0][0]])
        for j in range(1, k):
            self._clause([neg(r[0][j])])
        for i in range(1, n - 1):
            self._clause([neg(lits[i]), r[i][0]])
            self._clause([neg(r[i - 1][0]), r[i][0]])
            for j in range(1, k):
                self._clause([neg(lits[i]), neg(r[i - 1][j - 1]), r[i][j]])
                self._clause([neg(r[i - 1][j]), r[i][j]])
            # lits[i] can't be true if k earlier ones already are
            self._clause([neg(lits[i]), neg(r[i - 1][k - 1])])
        self._clause([neg(lits[n - 1]), neg(r[n - 2][k - 1])])


class Z3IntegerModel:
    """z3-int: one integer per step, solved with z3.

    pi[s] in 0..n-1 is the user given to step s, so each step automatically
    gets exactly one user.

      Authorisations  pi[s] = u1 or pi[s] = u2 or ... (the allowed users)
      SoD (a, b)      pi[a] != pi[b]
      BoD (a, b)      pi[a] == pi[b]
      Bo2 (a, b)      pi[a] <= pi[b]
      At-most-k       f_i = (pi[t_i] differs from pi[t_j] for all j < i),
                      then f_1 + ... + f_m <= k
      One-team        for some team, every step in T has a user in that team
    """

    def __init__(self, inst: Instance, time_limit=None, **_):
        _require_z3()
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
                add(z3.Or([p == u for u in eligible]))  # no allowed users -> unsat
        for a, b in inst.separation_of_duty:
            add(self.pi[a] != self.pi[b])
        for a, b in inst.binding_of_duty:
            add(self.pi[a] == self.pi[b])
        for a, b in inst.binding_of_order:
            add(self.pi[a] <= self.pi[b])
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
        """Rule out this plan:  pi[0] != plan[0] or pi[1] != plan[1] or ..."""
        self.solver.add(z3.Or([p != u for p, u in zip(self.pi, plan)]))


METHODS: dict[str, type[Model]] = {
    "cp-sat": CpSatBooleanModel,
    "z3-int": Z3IntegerModel,
    "z3-bool": Z3BooleanModel,
    "cp-sat-users": CpSatUserAmkModel,  # per-user at-most-k
    "z3-cnf": Z3CnfModel,               # clauses only
}
# the order the portfolio method tries things in
PORTFOLIO_ORDER = ("cp-sat", "z3-bool", "z3-int")
MULTIPLE = "other solutions exist"
UNIQUE = "this is the only solution"


class EncodingError(RuntimeError):
    """A method gave a plan that check_plan says is wrong.

    This would be a bug in one of our formulations, so we stop with an error
    rather than print a wrong answer. (Not an assert, because asserts are
    skipped with python -O.)
    """


def _attempt(
    inst: Instance, method: str, kwargs: dict
) -> tuple[str, list[int] | None, list[int] | None, str]:
    """Solve with one method, then check if the solution is unique.

    Returns (status, plan, other_plan, mul_sol). mul_sol is '' if the second
    solve ran out of time.
    """
    enc = METHODS[method](inst, **kwargs)
    status, plan = enc.solve()
    if status != "sat":
        return status, None, None, ""
    # check the plan ourselves before using it
    violations = check_plan(inst, plan)
    if violations:
        raise EncodingError(f"{method} returned an invalid plan: {violations}")
    enc.block_plan(plan)
    status2, other = enc.solve()
    if status2 == "sat":
        if other == plan:
            raise EncodingError(f"{method} returned the blocked plan again")
        violations = check_plan(inst, other)
        if violations:
            raise EncodingError(f"{method} returned an invalid second plan: {violations}")
        return "sat", plan, other, MULTIPLE
    if status2 == "unsat":
        return "sat", plan, None, UNIQUE
    return "sat", plan, None, ""


def Solver(filename, **kwargs):
    """Solve the instance in filename and say whether the solution is unique.

    Reads the file, removes users who can't do anything (prune_users) and
    solves with the chosen method. For uniqueness, the plan we found is
    ruled out and we solve again: if there's another plan, the solution
    isn't unique, and if not, it is.

    Optional kwargs:
      method      'cp-sat' (default)  one-hot encoding, OR-Tools CP-SAT
                  'z3-bool'           one-hot encoding, z3 (pseudo-Boolean)
                  'z3-int'            integer encoding, z3 (SMT)
                  'cp-sat-users'      cp-sat with per-user at-most-k
                  'z3-cnf'            one-hot encoding in pure CNF, z3
                  'portfolio'         try cp-sat, z3-bool, z3-int in turn
      time_limit  seconds per solver call (default: no limit)
      workers     CP-SAT search workers (default: 8)
      logic       z3 solver for z3-bool / z3-cnf (default 'QF_FD';
                  None for z3's general solver)

    portfolio tries the methods in PORTFOLIO_ORDER and stops at the first
    one that gives a full answer, so if one method runs out of time the next
    one gets a go.

    Returns a dict with the template's keys:
      sat      'sat' | 'unsat' | 'unknown' (time limit hit)
      sol      list of 's<i>: u<j>' strings ('' when unsat)
      mul_sol  MULTIPLE | UNIQUE | '' (unsat, or limit hit on second call)
      exe_time '<n>ms'  (parse + prune + build + both solves)
    and some extra keys that transform_output doesn't use:
      plan            0-based plan in original user numbering, or None
      other_plan      a second distinct plan when MULTIPLE, else None
      method_used     which method produced the verdict
    """
    starttime = int(currenttime() * 1000)
    inst = read_instance(filename)
    inst, alive = prune_users(inst)
    method = kwargs.get("method", "cp-sat")

    d = dict(sat="unsat", sol="", mul_sol="", plan=None, other_plan=None)
    if method == "portfolio":
        # keep the whole answer from one method and stop once we have
        # a full answer
        best = None
        for m in PORTFOLIO_ORDER:
            if m.startswith("z3") and z3 is None:
                continue  # z3 isn't installed
            status, plan, other, mul = _attempt(inst, m, kwargs)
            settled = status == "unsat" or (status == "sat" and mul)
            if settled or best is None or best[0] == "unknown":
                best = (status, plan, other, mul, m)
            if settled:
                break
        status, plan, other, mul, used = best
        d.update(sat=status, plan=plan, other_plan=other, mul_sol=mul, method_used=used)
    else:
        status, plan, other, mul = _attempt(inst, method, kwargs)
        d.update(sat=status, plan=plan, other_plan=other, mul_sol=mul, method_used=method)

    # put the users back to their original numbers
    if d["plan"] is not None:
        if alive is not None:
            d["plan"] = [alive[u] for u in d["plan"]]
            if d["other_plan"] is not None:
                d["other_plan"] = [alive[u] for u in d["other_plan"]]
        d["sol"] = [f"s{s+1}: u{u+1}" for s, u in enumerate(d["plan"])]

    d["exe_time"] = f"{int(currenttime() * 1000) - starttime}ms"
    return d


# Copied unchanged from the module's helper.py.
def transform_output(d):
    crlf = '\r\n'
    s=[]
    s = ''.join(kk + crlf for kk in d['sol'])
    s=d['sat']+crlf+s+d['mul_sol']
    s=crlf+ s + crlf+str(d['exe_time']) if 'exe_time' in d else s
    return s


if __name__ == "__main__":
    # Usage: python wsp_solver.py <instance_file> [method]
    if len(sys.argv) < 2:
        sys.exit(
            "usage: python wsp_solver.py <instance_file> [method]\n"
            f"methods: {', '.join(METHODS)}, portfolio (default: cp-sat)"
        )
    dpath = sys.argv[1]
    method = sys.argv[2] if len(sys.argv) > 2 else "cp-sat"
    d = Solver(dpath, method=method, silent=False)
    print(transform_output(d))
