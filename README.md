# Workflow Satisfiability Problem Solver

COMP3070 Symbolic Artificial Intelligence, Coursework 2 (group, 30% of the module), Autumn 2026/27.

**Deadline:** Tuesday 1 December 2026, 18:00, via Moodle. Late work loses 5% per calendar day, not counting weekends.

## The problem

The **Workflow Satisfiability Problem (WSP)** comes from access control. You are given a set $U$ of users and a set $S$ of workflow steps. The task is to find a plan $\pi : S \to U$ that satisfies every constraint.

- Every step gets **exactly one** user.
- A user may do several steps, or none.

The solver reports **sat** with a plan, or **unsat**. For a sat instance it must also say whether the plan is **the only solution**.

### Constraint types (Appendix 1)

| Constraint | File syntax | Requirement |
|---|---|---|
| **Authorisations** $(u, A)$ | `Authorisations u1 s1 s2` | $\pi(s) = u \Rightarrow s \in A$. A user with **no** Authorisations line may do **any** step. An empty list (`Authorisations u1`) means the user may do **no** steps. |
| **Separation of duty** $(s', s'')$ | `Separation-of-duty s1 s2` | $\pi(s') \neq \pi(s'')$ |
| **Binding of duty** $(s', s'')$ | `Binding-of-duty s1 s3` | $\pi(s') = \pi(s'')$ |
| **At-most-k** $(k, T)$ | `At-most-k 2 s1 s2 s3` | $\lvert\{\pi(s) : s \in T\}\rvert \le k$ |
| **One-team** $(T, U_1..U_r)$ | `One-team s1 s2 s4 (u1 u2) (u5 u7 u8) (u3)` | $\{\pi(s) : s \in T\} \subseteq U_i$ for some $i$. The teams are pairwise disjoint. |

### Input format

```
#Steps: 3
#Users: 4
#Constraints: 6
Authorisations u1 s1 s2
...
```

- Keywords are case-insensitive, and extra whitespace is ignored.
- Steps and users are numbered from 1.
- The provided files use CRLF line endings.

### Output format

The output must match the module's template and helper (`transform_output`):

```
sat
s1: u3
s2: u1
s3: u3
this is the only solution      # or: other solutions exist
12ms
```

## Instance data (`instances/`)

| Folder | Count | Notes |
|---|---|---|
| `examples/` | 19 | Appendix 1 examples, with no solution files. Expected sat/unique results are in `expected.csv`. Examples 1–8 are small (for debugging), 9–15 are medium (for testing) and 16–19 are large (for performance). |
| `1-constraint-small`, `3-constraint-small`, `4-constraint-small`, `5-constraint-small` | 20 each | Tiny instances |
| `3-constraint`, `4-constraint`, `5-constraint` | 20 each | Families with shared properties, suited to empirical analysis |
| `4-constraint-hard` | 20 | 60 steps, 500 users: the stress tests |

Every family folder holds `N.txt` with a matching `N-solution.txt`. A solution file is **one** valid plan, not necessarily the only one: two Moodle downloads gave different plans for the same instance. Tests must therefore **verify** our plan with `check_plan`, not compare it line by line with the solution file.

> **Note:** the constraint-type ticks in the Appendix 1 table are not accurate. For example, example7 has no BoD or at-most-k constraints. `expected.csv` takes the type columns from the files themselves and the sat/unique columns from the appendix.

## What we hand in

1. **Solver**: `wsp_solver.py`, a **single file** that exposes `Solver(filename, **kwargs) -> dict`. It will also be run on **unseen** instances.
2. **Group report** as a PDF, with sections a–h in order (see the marking table below). Write the group letter on it.

### Marking

| Part | Weight | What counts |
|---|---|---|
| 1. Completeness and correctness | 30% | Correct on unseen instances; terminates with a solution whenever one exists; "at least SIX constraint instances" (wording unclear, see open questions); extra marks for further methods, alternative formulations and constraints |
| 2. Quality and elegance | 20% | Clear, documented, tested, efficient code; a compact mathematical formulation |
| 3. Report | 50% | a) contents/novelty, b) formulations, c) alternative formulations and solutions, d) implementation (including **how uniqueness is detected**), e) evaluation with timings, f) discussion comparing approaches, g) conclusion, h) APA references |

For higher marks the group needs **three or more solution approaches** and **at least two alternative formulations**, all fully worked out.

## Implementation phases

| # | Phase | Output | Status |
|---|---|---|---|
| 0 | **Foundations**: parser, `Instance` model, independent `check_plan` verifier, tests against all 160 instances and 122 reference plans | `wsp_solver.py`, `tests/` | ✅ done |
| 1 | **Baseline: OR-Tools CP-SAT, Boolean encoding** (`CpSatBooleanModel`). Variables $x_{s,u}$ exist only for authorised pairs; `AddExactlyOne` per step; SoD $x_{a,u}+x_{b,u}\le1$; BoD $x_{a,u}=x_{b,u}$; one-team via team selectors $z_i$ with `AddExactlyOne`. At-most-k uses pairwise "same user" variables $m_{s,t}$ (see below). Every plan is re-checked with `check_plan` before it is returned. | all 179 instances solved correctly, max 5.5 s | ✅ done |
| 2 | **Uniqueness check**: add a blocking clause $\bigvee_s \neg x_{s,\pi(s)}$ to the same model and solve again. SAT means other solutions exist (the second plan is also checked); UNSAT proves the plan is unique. Only the $x$ variables are blocked; auxiliary variables are not. Tested against the appendix (examples 3, 5 and 7 unique) and against brute-force solution counts on all 88 small instances. | 6 unique / 88 multiple, all correct | ✅ done |
| 3 | **Approach 2: z3, integer encoding** (`Z3IntegerModel`, `method="z3-int"`). One `Int` variable $\pi_s \in [0,n)$ per step. Authorisation is $\bigvee_{u \in A^{-1}(s)} \pi_s = u$; SoD and BoD are `!=` and `==`; at-most-k is $\sum_i [\bigwedge_{j<i} \pi_{t_j} \ne \pi_{t_i}] \le k$; one-team is $\bigvee_i \bigwedge_{s\in T} \pi_s \in U_i$. Uniqueness is blocked with $\bigvee_s \pi_s \ne \pi^*(s)$. | correct everywhere it finishes; too slow on example17/19 and `4-constraint-hard` | ✅ done |
| 4 | **Approach 3: z3, Boolean / pseudo-Boolean encoding** (`PbEq`, `AtMost`) and/or a CNF encoding (propositional logic, clausal form) | third solver | ⬜ |
| 5 | **Efficiency**: drop users with no authorisations; merge users with identical authorisations when constraints are user-independent; symmetry breaking; solver parameters (workers, time limit) | faster runs on `4-constraint-hard` and examples 16–19 | ⬜ |
| 6 | **Extra constraint types** (extra marks): e.g. at-least-k, super-user/assignment-dependent, Wang–Li style. Extend the parser, all encodings and `check_plan`. Write our own test instances for them. | ≥ 6 constraint types, new instances | ⬜ |
| 7 | **Benchmark harness**: run every approach on every instance, verify each plan with `check_plan`, record times to CSV, plot results | `results/`, report figures | ⬜ |
| 8 | **Report** sections a–h; final single-file check; submit | PDF + `.py` | ⬜ |

### Phase 1 finding: at-most-k encoding matters (report material)

The first version encoded at-most-k with one indicator variable per user per constraint: $x_{s,u} \Rightarrow y_u$ and $\sum_u y_u \le k$. With 500 users this relaxes poorly. Examples 17 and 19 and most of `4-constraint-hard` hit a 20 s limit without an answer, and example16 took 17 s.

The second version counts distinct users over **pairs of steps**. $m_{s,t} \Rightarrow \pi(s)=\pi(t)$. For $T = (t_1..t_m)$, $f_i \lor \bigvee_{j<i} m_{t_j,t_i}$ marks the steps that start a new user group, and $\sum f_i \le k$. Transitivity clauses are added within $T$. With this version every instance solves in 0.3–5.5 s. Running both encodings together was slower than the pairwise one alone. Both versions are worth keeping as alternative formulations in the report.

### Phase 3 finding: the direct integer model is the most readable but the slowest

`z3-int` is almost a word-for-word copy of the Appendix 1 definitions. It is correct on everything it finishes (examples 1–16 and 18, and all families except `4-constraint-hard`), and it agrees with brute force on all 88 small instances. On the large instances it is much slower than CP-SAT:

| Instance | cp-sat | z3-int (default) | z3 `QF_FD` | z3 `QF_LIA` | z3 enum sort | z3 bit-vector |
|---|---|---|---|---|---|---|
| example16 (sat) | 1.2 s | 3.4–7 s | 25 s | 3.9 s | 6.2 s | 10.6 s |
| example17 (sat) | 0.3 s | >60 s | 3.1 s | 32 s | >60 s | 34 s |
| example18 (unsat) | <1 s | 8.3 s | – | – | – | – |
| example19 (unsat) | 1.3 s | >60 s | >60 s | >60 s | >60 s | >60 s |
| 4-constraint-hard/0 | 1.2 s | >60 s | >60 s (56 s with implied constraint) | >60 s | >60 s | >60 s |

We tried other z3 logics, user domains (enumerated sort, bit-vectors) and an implied constraint ($\ge |T|-k$ equal pairs per at-most-k scope). None fixed the hard cases consistently. A likely explanation for the report is that each $\pi_a \ne \pi_b$ becomes a case split ($<$ or $>$) in arithmetic, whereas CP-SAT's one-hot model propagates SoD and authorisation directly at the Boolean level. Phase 4 (z3 Boolean/PB) tests this. The cp-sat timings in this table come from separate runs, so treat them as indicative until the phase 7 benchmark.

### Open questions for the convenor

- Does "Set at least SIX constraint instances" mean six constraint *types* (the appendix defines five, so we would need at least one extra) or six of our own test instance files? Doing both is the safe choice.
- How is `Solver` called on unseen instances? We currently assume `Solver(path)` and the template dict format.

## Project layout

```
.
├── wsp_solver.py      # the single-file submission (parser, checker, solvers, output)
├── tests/             # pytest tests
├── instances/         # all instance families plus examples/expected.csv
├── docs/              # report drafts, figures
├── requirements.txt
└── pytest.ini
```

## Setup and usage

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt

pytest                                               # run tests
python wsp_solver.py instances/examples/example3.txt          # default: cp-sat
python wsp_solver.py instances/examples/example3.txt z3-int   # alternative method
```

## References

- Wang, Q., & Li, N. (2010). Satisfiability and resiliency in workflow authorization systems. *ACM Transactions on Information and System Security, 13*(4).
- Cohen, D., Crampton, J., Gagarin, A., Gutin, G., & Jones, M. (2014). Iterative plan construction for the workflow satisfiability problem. *Journal of Artificial Intelligence Research, 51*, 555–577.
- Karapetyan, D., Parkes, A. J., Gutin, G., & Gagarin, A. (2019). Pattern-based approach to the workflow satisfiability problem with user-independent constraints. *Journal of Artificial Intelligence Research, 66*, 85–122.
- z3 Python API: https://z3prover.github.io/api/html/namespacez3py.html
- OR-Tools CP-SAT: https://developers.google.com/optimization/cp/cp_solver
