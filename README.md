# Workflow Satisfiability Problem Solver

COMP3070 Symbolic Artificial Intelligence, Coursework 2 (group, 30% of the module), Autumn 2026/27.

**Deadline:** Tuesday 1 December 2026, 18:00, via Moodle. Late work loses 5% per calendar day, not counting weekends.

## The problem

The **Workflow Satisfiability Problem (WSP)** comes from access control. An organisation runs a workflow made of **steps**, and each step must be done by a **user**. The task is to assign every step to a user so that:

- each user only does steps they are **authorised** for, and
- every security **constraint** on the workflow holds.

The solver either returns a valid assignment or reports that none exists (UNSAT).

### Formal definition

A WSP instance is a tuple $(S, U, A, C)$:

| Symbol | Meaning |
|---|---|
| $S = \{s_1,\dots,s_k\}$ | the workflow steps |
| $U = \{u_1,\dots,u_n\}$ | the users |
| $A \subseteq U \times S$ | authorisations: $(u, s) \in A$ means user $u$ may do step $s$ |
| $C$ | the constraints |

A **plan** is a function $\pi : S \to U$. It is **valid** if $(\pi(s), s) \in A$ for every step $s$ and $\pi$ satisfies every constraint in $C$.

### Common constraint types

These are the standard constraint types from the WSP literature and the labs. Check the instance format on Moodle for the exact syntax.

| Constraint | Meaning |
|---|---|
| **Separation of duty** $(s_1, s_2)$ | $\pi(s_1) \neq \pi(s_2)$: different users must do the two steps |
| **Binding of duty** $(s_1, s_2)$ | $\pi(s_1) = \pi(s_2)$: the same user must do both steps |
| **At-most-k** $(k, T)$ | the steps in scope $T$ use at most $k$ distinct users |
| **One-team** $(T, \{t_1,\dots,t_m\})$ | every step in $T$ goes to members of one team $t_i$ |

The coursework asks for **at least six constraint types** in the formulation. The four above cover the standard ones, so we still need extra ones such as at-least-k, super-user or wang-li style constraints, or our own.

## What we hand in

1. **Solver code in Python.** This is compulsory. z3, OR-Tools and similar libraries are allowed. Put everything in a **single `.py` file** if possible; otherwise zip the files.
2. **Group report as a PDF.**

Our solver will also be run on **unseen instances**, not just the examples we were given. It must finish with a solution whenever one exists.

## How it is marked

| Part | Weight | What counts |
|---|---|---|
| 1. Completeness and correctness | 30% | Solves instances correctly, including unseen ones; ≥ 6 constraint types; extra marks for further methods, alternative formulations and constraints |
| 2. Quality and elegance | 20% | Clear, maintainable, documented, tested and efficient code; a compact, elegant mathematical formulation |
| 3. Group report | 50% | Sections listed below, in that order |

For extra marks the group should present **three or more solution approaches** and **at least two alternative formulations**, all fully worked out.

### Report structure (sections must appear in this order)

- **a) Report contents.** Introduce the solver and language. Cover functionality that doesn't always work, earlier research on the WSP, and what is new or extra in our work.
- **b) Formulations and alternative formulations.** Give a full formulation for each constraint type in first-order logic, propositional logic, clausal form, or another suitable notation. Define any new notation. Explain why each formulation is correct and why we chose each API function.
- **c) Alternative formulations and alternative solutions.**
- **d) Implementation.** Explain how to run the solver and how it works, including **how it detects whether there are multiple solutions**. List known bugs.
- **e) Evaluation.** Say whether each sample instance is solved correctly. Include timing and performance analysis.
- **f) Discussion.** Analyse and compare the solutions and alternative solutions in detail. This section is mandatory.
- **g) Conclusion.** Summarise what worked, the limitations, and what we would do with more time.
- **h) References.** Use APA style.

Write the **group letter** (e.g. "Group B") on the report. Each member submits a Peer Assessment Factor form.

## Candidate solution approaches

These are possible routes to the three or more approaches and two or more alternative formulations:

| Approach | Encoding idea |
|---|---|
| z3 SMT, integer encoding | one `Int` variable per step holding a user index; SoD/BoD written as `!=` / `==` |
| z3 SAT, Boolean encoding | $x_{s,u}$ is true when step $s$ goes to user $u$; exactly-one per step via `PbEq`/`AtMost`; at-most-k via auxiliary "user used" variables |
| z3 pseudo-Boolean / `Optimize` | same Boolean model with cardinality constraints; can also minimise the number of users |
| OR-Tools CP-SAT | Boolean or integer model with `AddExactlyOne`, `AddAllDifferent` and similar |
| User-independent / pattern-based | for UI constraints, search over partitions of the steps (Cohen et al., Karapetyan et al.) |

**Multiple solutions:** after finding a model, add a blocking clause $\neg \bigwedge_s (\pi(s) = \text{model}(s))$ and solve again. If the result is SAT, the instance has more than one solution.

## Project layout

```
.
├── README.md
├── requirements.txt   # z3-solver, ortools, pytest
├── instances/         # sample and custom WSP instance files
├── tests/             # pytest tests
└── docs/              # report drafts, figures, timing results
```

## Setup

You need Python 3.10 or later; we develop on 3.11.

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
```

Check that the install worked:

```bash
python -c "import z3, ortools; print('z3', z3.get_version_string(), '| ortools', ortools.__version__)"
```

## Useful references

- Wang, Q., & Li, N. (2010). Satisfiability and resiliency in workflow authorization systems. *ACM Transactions on Information and System Security, 13*(4).
- Cohen, D., Crampton, J., Gagarin, A., Gutin, G., & Jones, M. (2014). Iterative plan construction for the workflow satisfiability problem. *Journal of Artificial Intelligence Research, 51*, 555–577.
- Karapetyan, D., Parkes, A. J., Gutin, G., & Gagarin, A. (2019). Pattern-based approach to the workflow satisfiability problem with user-independent constraints. *Journal of Artificial Intelligence Research, 66*, 85–122.
- z3 Python API: https://z3prover.github.io/api/html/namespacez3py.html
- OR-Tools CP-SAT: https://developers.google.com/optimization/cp/cp_solver
