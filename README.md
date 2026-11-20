# Workflow Satisfiability Problem Solver

COMP3070 Symbolic AI, Coursework 2 (group, 30%), Autumn 2026/27.

Deadline: Tuesday 1 December 2026, 18:00, on Moodle. Late penalty is 5% per calendar day, excluding weekends.

## The problem

Given a set of users $U$ and workflow steps $S$, find a plan $\pi : S \to U$ that satisfies all the constraints. Every step gets exactly one user; a user can do any number of steps, including none.

The solver outputs `sat` with a plan or `unsat`. For sat instances it also has to say whether the plan is the only solution.

### Constraint types (Appendix 1)

| Constraint | File syntax | Requirement |
|---|---|---|
| Authorisations $(u, A)$ | `Authorisations u1 s1 s2` | $\pi(s) = u \Rightarrow s \in A$. Users without an Authorisations line can do any step. `Authorisations u1` with no steps means u1 can do nothing. |
| Separation of duty $(s', s'')$ | `Separation-of-duty s1 s2` | $\pi(s') \neq \pi(s'')$ |
| Binding of duty $(s', s'')$ | `Binding-of-duty s1 s3` | $\pi(s') = \pi(s'')$ |
| At-most-k $(k, T)$ | `At-most-k 2 s1 s2 s3` | $\lvert\{\pi(s) : s \in T\}\rvert \le k$ |
| One-team $(T, U_1..U_r)$ | `One-team s1 s2 s4 (u1 u2) (u5 u7 u8) (u3)` | $\{\pi(s) : s \in T\} \subseteq U_i$ for some $i$ (teams are disjoint) |

### Input format

```
#Steps: 3
#Users: 4
#Constraints: 6
Authorisations u1 s1 s2
...
```

Keywords are case-insensitive, extra whitespace is allowed, and steps and users are numbered from 1. The provided files have CRLF line endings.

### Output format

Same as the module template and `transform_output` helper:

```
sat
s1: u3
s2: u1
s3: u3
this is the only solution      # or: other solutions exist
12ms
```

## Instances (`instances/`)

| Folder | Count | Notes |
|---|---|---|
| `examples/` | 19 | Appendix 1 examples. There are no solution files; expected results are in `expected.csv`. 1–8 are small, 9–15 medium, 16–19 large. |
| `1-`, `3-`, `4-`, `5-constraint-small` | 20 each | Very small |
| `3-constraint`, `4-constraint`, `5-constraint` | 20 each | Medium-sized families |
| `4-constraint-hard` | 20 | 60 steps, 500 users |

Each family folder has `N.txt` and `N-solution.txt`. The solution file only gives one valid plan (two Moodle downloads had different plans for the same instance), so the tests check our plans with `check_plan` instead of comparing with the file.

The constraint-type ticks in the Appendix 1 table don't match the files (e.g. example7 has no BoD or at-most-k). In `expected.csv` the type columns come from the files and the sat/unique columns from the appendix.

## Submission

1. `wsp_solver.py`, a single file with `Solver(filename, **kwargs) -> dict`. It will also be run on unseen instances.
2. Group report (PDF), sections a–h in order, with the group letter on it.

### Marking

| Part | Weight | Covers |
|---|---|---|
| Completeness and correctness | 30% | Correct on unseen instances, finds a solution when one exists, "at least SIX constraint instances" (unclear, see below), extra methods/formulations/constraints |
| Quality and elegance | 20% | Code quality, tests, efficiency, a compact formulation |
| Report | 50% | a) contents, b) formulations, c) alternatives, d) implementation incl. how uniqueness is checked, e) evaluation with timings, f) discussion, g) conclusion, h) references (APA) |

Higher marks need at least three solution approaches and two alternative formulations.

## Phases

| # | Phase | Status |
|---|---|---|
| 0 | Parser, `Instance`, `check_plan`, tests on all 179 instances and the 122 reference plans | done |
| 1 | CP-SAT, one-hot encoding (`cp-sat`, default method) | done |
| 2 | Uniqueness check with a blocking clause | done |
| 3 | z3, integer encoding (`z3-int`) | done |
| 4 | z3, one-hot encoding with pseudo-Boolean constraints (`z3-bool`) | done |
| 5 | Speed-ups: drop users with no authorisations, merge identical users, symmetry breaking, solver settings | todo |
| 6 | Extra constraint types (at-least-k, super-user, ...) and our own test instances | todo |
| 7 | Benchmark script: all methods on all instances, results to CSV, plots | todo |
| 8 | Report and submission | todo |

## Formulations

### One-hot encoding (`cp-sat`, `z3-bool`)

$x_{s,u}$ is true iff $\pi(s) = u$. It is only created when $u$ is authorised for $s$, which covers the Authorisations constraint. This is written once in `BooleanEncoding`; `CpSatBooleanModel` and `Z3BooleanModel` just supply the solver calls.

| Constraint | Encoding |
|---|---|
| One user per step | $\text{ExactlyOne}_u\, x_{s,u}$ |
| SoD $(a,b)$ | $\neg x_{a,u} \lor \neg x_{b,u}$ for each $u$ |
| BoD $(a,b)$ | $x_{a,u} \leftrightarrow x_{b,u}$ for each $u$; users eligible for only one of the steps are set false |
| At-most-k | $m_{s,t}$ means "s and t have the same user" ($m_{s,t} \land x_{s,u} \rightarrow x_{t,u}$). $f_i \lor \bigvee_{j<i} m_{t_j,t_i}$ marks a step with a new user; $\text{AtMost}_k(f)$. Plus transitivity clauses on $m$. |
| One-team | team selectors $z_i$ with $\text{ExactlyOne}_i\, z_i$ and $x_{s,u} \rightarrow z_{team(u)}$; users in no team are set false |
| Uniqueness | add $\bigvee_s \neg x_{s,\pi^*(s)}$ and solve again |

z3 uses `PbEq` and `AtMost` with the `QF_FD` solver. Only the $x$ variables are blocked for uniqueness, since blocking the auxiliary ones could exclude the same plan or miss a different one.

### Integer encoding (`z3-int`)

One integer $\pi_s \in [0, n)$ per step:

| Constraint | Encoding |
|---|---|
| Authorisation | $\bigvee_{u \text{ authorised for } s} \pi_s = u$ |
| SoD / BoD | $\pi_a \ne \pi_b$ / $\pi_a = \pi_b$ |
| At-most-k | $\sum_i [\bigwedge_{j<i} \pi_{t_j} \ne \pi_{t_i}] \le k$ |
| One-team | $\bigvee_i \bigwedge_{s \in T} \bigvee_{u \in U_i} \pi_s = u$ |
| Uniqueness | add $\bigvee_s \pi_s \ne \pi^*(s)$ and solve again |

## Results so far

### At-most-k encoding

The first CP-SAT version used one variable per user per at-most-k constraint ($x_{s,u} \Rightarrow y_u$, $\sum_u y_u \le k$). With 500 users, examples 17 and 19 and most of `4-constraint-hard` didn't finish in 20 s, and example16 took 17 s. Switching to the pairwise $m_{s,t}$ version above got every instance under about 7 s. Using both together was slower than the pairwise one alone.

### Times on the large instances

Times include the uniqueness re-solve; 60 s limit per solver call. Times vary by up to about 2x between runs on the same machine, so these are rough until the phase 7 benchmark.

| Instance | cp-sat | z3-int | z3-bool (`QF_FD`) | z3-bool (default solver) |
|---|---|---|---|---|
| example16 (sat) | 1–2 s | 3–48 s | 22.4 s | 87.7 s |
| example17 (sat) | 0.3 s | >60 s | 0.9 s | 1.5 s |
| example18 (unsat) | <1 s | 4–90 s | 2.6 s | 2.9 s |
| example19 (unsat) | 1.3 s | >60 s | 3.8 s | 8.2 s |
| 4-constraint-hard/0 (sat) | 1.2 s | >60 s | 2.5 s | 12.1 s |
| 4-constraint-hard/1 (unsat) | 2.5 s | >60 s | 4.7 s | 12.1 s |
| 4-constraint-hard/2 (sat) | 7.1 s | >60 s | 3.5 s | 36.8 s |
| 4-constraint-hard/18 (unsat) | 7.3 s | >60 s | 10.3 s | 25.2 s |

On the small and medium families all methods take under 100 ms.

Notes:
- `z3-int` gets every instance it finishes right, but times out on example17, example19 and all of `4-constraint-hard`, and its times on example16/18 swing a lot between runs (3 s to 90 s). We also tried other z3 logics (`QF_FD`, `QF_LIA`), users as an enum sort or bit-vectors, and an extra implied constraint for at-most-k. None of them fixed it.
- Our guess is that each $\pi_a \ne \pi_b$ turns into a case split ($<$ or $>$) in integer arithmetic. The one-hot encoding avoids this, and with it z3 solves everything, which fits that explanation.
- `QF_FD` was faster than z3's default solver on every instance, so it's the default for `z3-bool` (`logic=None` switches back).
- example16 is the only instance where `z3-int` beats `z3-bool`. Possibly because it is the only large example with unrestricted users (90 of 500), which add a lot of one-hot variables. Not checked yet.
- CP-SAT is still the fastest overall with the same encoding, probably because it runs a parallel portfolio search and z3 doesn't.

## Open questions

- Does "Set at least SIX constraint instances" mean six constraint types (the appendix has five) or six of our own instance files? Probably safest to do both.
- How will `Solver` be called on the unseen instances? We're assuming `Solver(path)` and the template's dict format.

## Layout

```
.
├── wsp_solver.py      # submission file: parser, checker, encodings, Solver()
├── tests/             # pytest
├── instances/         # instance families + examples/expected.csv
├── docs/              # report drafts, figures
├── requirements.txt
└── pytest.ini
```

## Setup

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt

pytest
python wsp_solver.py instances/examples/example3.txt            # cp-sat
python wsp_solver.py instances/examples/example3.txt z3-int     # or z3-bool
```

## References

- Wang, Q., & Li, N. (2010). Satisfiability and resiliency in workflow authorization systems. *ACM Transactions on Information and System Security, 13*(4).
- Cohen, D., Crampton, J., Gagarin, A., Gutin, G., & Jones, M. (2014). Iterative plan construction for the workflow satisfiability problem. *Journal of Artificial Intelligence Research, 51*, 555–577.
- Karapetyan, D., Parkes, A. J., Gutin, G., & Gagarin, A. (2019). Pattern-based approach to the workflow satisfiability problem with user-independent constraints. *Journal of Artificial Intelligence Research, 66*, 85–122.
- z3 Python API: https://z3prover.github.io/api/html/namespacez3py.html
- OR-Tools CP-SAT: https://developers.google.com/optimization/cp/cp_solver
