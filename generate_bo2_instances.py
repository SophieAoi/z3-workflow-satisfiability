"""Generate instances/6-constraint-BoO: our own binding-of-order family.

Each instance mixes all six constraint types. sat instances ship an N-solution.txt
reference plan; unsat instances ship N-solution.txt containing "unsat", following
the repo's existing convention. Truth comes from brute-force enumeration via
check_plan only.
"""
import itertools
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from wsp_solver import check_plan, parse_instance

OUT = Path(__file__).parent / "instances" / "6-constraint-BoO"


def brute_force(inst, stop_at=None):
    choices = [[u for u in range(inst.n_users) if inst.authorised(u, s)]
               for s in range(inst.n_steps)]
    found = []
    for plan in itertools.product(*choices):
        if not check_plan(inst, list(plan)):
            found.append(list(plan))
            if stop_at and len(found) >= stop_at:
                break
    return found


def gen(rng, small):
    n_steps = rng.randint(3, 4) if small else rng.randint(5, 7)
    n_users = rng.randint(4, 5) if small else rng.randint(6, 9)
    cons = []
    # Authorisations: two users get restricted step sets
    for u in rng.sample(range(1, n_users + 1), 2):
        steps = [s for s in range(1, n_steps + 1) if rng.random() < 0.55]
        if steps:
            cons.append(f"Authorisations u{u} " + " ".join(f"s{s}" for s in steps))
    # Binding-of-order: the constraint that gives the family its name
    for _ in range(2 if small else 3):
        a, b = rng.sample(range(1, n_steps + 1), 2)
        cons.append(f"Binding-of-order s{a} s{b}")
    # SoD and BoD
    a, b = sorted(rng.sample(range(1, n_steps + 1), 2))
    cons.append(f"Separation-of-duty s{a} s{b}")
    # Appendix 1 requires two different steps (s' != s''), so always sample a
    # distinct pair, also for 3-step instances.
    c, d = sorted(rng.sample(range(1, n_steps + 1), 2))
    cons.append(f"Binding-of-duty s{c} s{d}")
    # At-most-k
    k = rng.randint(2, 3)
    t = sorted(rng.sample(range(1, n_steps + 1), min(3, n_steps)))
    cons.append(f"At-most-k {k} " + " ".join(f"s{x}" for x in t))
    # One-team: partition a subset of users
    pool = list(range(1, n_users + 1))
    rng.shuffle(pool)
    cut = max(1, len(pool) // 2)
    t1, t2 = sorted(pool[:cut]), sorted(pool[cut:])
    scope = sorted(rng.sample(range(1, n_steps + 1), min(2, n_steps)))
    fmt = lambda team: "(" + " ".join(f"u{u}" for u in team) + ")"
    cons.append("One-team " + " ".join(f"s{x}" for x in scope) + f" {fmt(t1)} {fmt(t2)}")
    # some duplicate lines / mixed case to test robustness, counted in #Constraints
    text = (f"#Steps: {n_steps}\r\n#Users: {n_users}\r\n#Constraints: {len(cons)}\r\n"
            + "\r\n".join(cons) + "\r\n")
    return text


def gen_unique(rng):
    """All-authorised-tight instance: each step has exactly one eligible user
    and the assigned users are non-decreasing, so any binding-of-order line
    (earlier step <= later step) holds and the plan is unique."""
    n_steps = rng.randint(3, 4)
    n_users = rng.randint(4, 6)
    perm = sorted(rng.randrange(n_users) for _ in range(n_steps))
    cons = []
    for u in range(n_users):
        steps = [s for s in range(n_steps) if perm[s] == u]
        line = f"Authorisations u{u+1}" + ("" if not steps else " " + " ".join(f"s{s+1}" for s in steps))
        cons.append(line)
    a, b = rng.sample(range(n_steps), 2)
    a, b = min(a, b), max(a, b)
    cons.append(f"Binding-of-order s{a+1} s{b+1}")
    return (f"#Steps: {n_steps}\r\n#Users: {n_users}\r\n#Constraints: {len(cons)}\r\n"
            + "\r\n".join(cons) + "\r\n")


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    rng = random.Random(2026)
    sat_n = unsat_n = unique = 0
    i = 0
    while i < 20:
        if i >= 16:
            text = gen_unique(rng)
        else:
            text = gen(rng, i < 10)
        inst = parse_instance(text)
        assert inst.n_constraints_parsed == inst.n_constraints_declared, text
        plans = brute_force(inst, stop_at=2)
        (OUT / f"{i}.txt").write_text(text, newline="")
        if not plans:
            (OUT / f"{i}-solution.txt").write_text("unsat\r\n", newline="")
            unsat_n += 1
        else:
            sol = "sat\r\n" + "".join(f"s{s+1}: u{u+1}\r\n" for s, u in enumerate(plans[0]))
            (OUT / f"{i}-solution.txt").write_text(sol, newline="")
            sat_n += 1
            if len(plans) == 1:
                unique += 1
        i += 1
    print(f"wrote 20 instances to {OUT.name}: sat={sat_n} unsat={unsat_n} (unique among sat: {unique})")
    for p in sorted(OUT.glob("*.txt")):
        print(" ", p.name)


if __name__ == "__main__":
    main()
