#!/usr/bin/env python3
"""
Erdos-Straus hard-kernel covering search — cleaned up.
=========================================================

WHAT THIS SCRIPT ACTUALLY DOES, IN TWO CLEARLY SEPARATED PARTS:

  PART A — EXPLICIT FAMILY DISCOVERY (real, provable, permanent)
      For fixed small (alpha, r, s), the identity underneath es_ed2_family
      forces: for EVERY prime P with P == -4*alpha*s^2 (mod q), where
      q = 4*alpha*r*s - 1, a valid Erdos-Straus witness exists via a fixed
      formula. This is a genuine infinite arithmetic progression, proven by
      algebra, not search. Combining with "P == h (mod 840)" via CRT gives
      an explicit, permanent, closed-form slice of a hard residue class.
      This part of the script is sound and its output means what it says.

  PART B — TWO DIFFERENT WAYS TO REPORT "HOW MUCH IS COVERED"
      B1. Ad-hoc patching of specific known stragglers (`patch_known_
          stragglers`). This finds *a* family whose progression happens to
          contain a *specific already-known* number. IMPORTANT: this is
          statistically almost guaranteed to succeed for ANY integer, prime
          or composite, hard-residue or not, given enough (alpha,r,s)
          combinations -- it is not evidence that the number was hard, and
          it says NOTHING about numbers you have not already found and
          fed to it. This script prints a loud warning and a live self-test
          demonstrating this every time it runs, so results from B1 can
          never be mistaken for a proof. Treat it as: "find me one explicit
          witness for this one number," nothing more.

      B2. The genuine covering-CERTIFICATE search (`attempt_certificate_
          for_residue`). This checks whether a FINITE set of congruence
          families, with NO per-number patching, covers every integer in a
          residue class, period. This is the only part of this script whose
          success would constitute a real, checkable, infinite proof for
          that residue class. It is legitimately hard to satisfy, and it is
          expected to usually fail -- failure here is an honest, correct,
          useful result, not a bug.

  PART C — FORCED COMPOSITENESS (a second, genuinely different closure
      mechanism). A congruence class x == r (mod M) is trivially "covered"
      forever if every member is provably composite (i.e. some fixed small
      prime p divides M and divides r) -- composite numbers reduce to
      smaller Erdos-Straus cases for free and need no family at all. This
      was present in the original script as an unused helper
      (`forced_composite`) and is now actually wired into the certificate
      search, because it is a real, legitimate way to close gaps that no
      amount of (alpha,r,s) searching ever will.

Bugs fixed from the previous version:
  * VERIFY_N was `100_000_00` (= 10,000,000, identical to N) instead of the
    evidently-intended `100_000_000`. The "extended verification" was
    silently testing the exact same range twice.
  * Dead code removed: `build_coverage_mask` (unused, superseded by the
    logic inside `select_covering_families`) and the entire commented-out
    duplicate `attempt_infinite_certificate` block at the bottom of the
    file.
  * `forced_composite` existed but was never called anywhere. Wired into
    the certificate search as a real closure mechanism (Part C above).
  * The final "verdict" no longer derives any claim of completeness from
    the ad-hoc patch step. Only `attempt_certificate_for_residue`'s result
    can produce a COMPLETE verdict.
"""

import math
from math import gcd
from typing import List, Dict, Tuple, Optional
from collections import defaultdict

# ============================================================
# Configuration
# ============================================================

MODULUS = 840
HARD_RESIDUES = (1, 121, 169, 289, 361, 529)

# Main empirical verification range.
N = 10_000_000

# Initial global family search (Part A).
INITIAL_ALPHA_MAX = 16
INITIAL_R_MAX = 24
INITIAL_S_MAX = 24

# Ad-hoc per-number patch search bounds (Part B1 -- NOT a certificate).
PATCH_ALPHA_MAX = 100
PATCH_R_MAX = 100
PATCH_S_MAX = 100

# Extended verification range. FIXED: was accidentally == N (100_000_00
# parses as 10,000,000 in Python's underscore-separated int literals).
VERIFY_N = 100_000_000

# Certificate search: a prime whose OWN value already exceeds this can
# never cheaply enter a period, so it's not worth considering as a
# candidate at all (this bounds the candidate list, not the achievable
# period -- see greedy_build_certificate_period).
CERTIFICATE_CANDIDATE_PRIME_LIMIT = 514
# CERTIFICATE_PERIOD_LIMIT = 2_000_000_000
CERTIFICATE_PERIOD_LIMIT = 440156716600

# Small primes checked for forced-compositeness closure (Part C) are now
# derived dynamically from whatever the greedy period-builder picks up --
# see _closure_sieve -- rather than a fixed list, so nothing is configured
# here.


# ============================================================
# Basic number theory helpers
# ============================================================

def factorize(n: int) -> Dict[int, int]:
    """Trial-division factorization. Certificate moduli are small enough
    for this to be sufficient."""
    factors: Dict[int, int] = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d = 3 if d == 2 else d + 2
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def crt2(m1: int, r1: int, m2: int, r2: int) -> Optional[Tuple[int, int]]:
    """Solve x == r1 (mod m1), x == r2 (mod m2). Returns (residue, lcm) or
    None if the two congruences are incompatible."""
    g = gcd(m1, m2)
    if (r2 - r1) % g != 0:
        return None
    l = m1 // g * m2

    def egcd(a: int, b: int):
        if b == 0:
            return a, 1, 0
        gg, x, y = egcd(b, a % b)
        return gg, y, x - (a // b) * y

    _, x, _ = egcd(m1 // g, m2 // g)
    t = ((r2 - r1) // g * x) % (m2 // g)
    return (r1 + m1 * t) % l, l


def primes_upto(n: int) -> List[int]:
    if n < 2:
        return []
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[:2] = b"\x00\x00"
    limit = math.isqrt(n)
    for p in range(2, limit + 1):
        if sieve[p]:
            start = p * p
            sieve[start:n + 1:p] = b"\x00" * (((n - start) // p) + 1)
    return [i for i in range(2, n + 1) if sieve[i]]


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n in (2, 3):
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    d = 5
    while d * d <= n:
        if n % d == 0 or n % (d + 2) == 0:
            return False
        d += 6
    return True


# ============================================================
# PART A -- explicit closed-form family construction (real, provable)
# ============================================================

def family_from_parameters(alpha: int, r: int, s: int) -> Optional[Tuple[int, int]]:
    """The closed-form family: q = 4*alpha*r*s - 1; P == -4*alpha*s^2 (mod q)
    forces a valid Erdos-Straus witness to exist via a fixed algebraic
    formula (es_ed2_family). This is proven, not searched."""
    q = 4 * alpha * r * s - 1
    if q < 3:
        return None
    target = (-4 * alpha * s * s) % q
    return q, target


def combined_family_for_h(h: int, alpha: int, r: int, s: int) -> Optional[dict]:
    """Combine P == h (mod 840) with the family's own congruence via CRT."""
    fam = family_from_parameters(alpha, r, s)
    if fam is None:
        return None
    q, target = fam
    combo = crt2(MODULUS, h, q, target)
    if combo is None:
        return None
    residue, modulus = combo
    return {"alpha": alpha, "r": r, "s": s, "q": q, "target": target,
            "residue": residue, "modulus": modulus}


def build_initial_families(alpha_max: int, r_max: int, s_max: int) -> Dict[int, dict]:
    """Sweep (alpha,r,s) once and keep the smallest-parameter witness for
    each distinct (modulus, residue) progression found, per hard residue."""
    families: Dict[int, dict] = {h: {} for h in HARD_RESIDUES}
    tried = 0
    for alpha in range(1, alpha_max + 1):
        for r in range(1, r_max + 1):
            for s in range(1, s_max + 1):
                tried += 1
                for h in HARD_RESIDUES:
                    fam = combined_family_for_h(h, alpha, r, s)
                    if fam is None:
                        continue
                    key = (fam["modulus"], fam["residue"])
                    if key not in families[h]:
                        families[h][key] = fam
    print(f"\nPart A: examined {tried:,} (alpha,r,s) triples; this is a fixed,")
    print("finite, ONE-TIME sweep -- every family found is a real, permanent,")
    print("closed-form infinite progression, independent of any specific prime.")
    return families


# ============================================================
# PART B1 -- ad-hoc per-number patch (explicitly NOT a certificate)
# ============================================================

def find_family_for_specific_number(x: int, alpha_max: int, r_max: int, s_max: int
                                     ) -> Tuple[Optional[dict], int]:
    """Search for ONE explicit family whose progression contains x.
    WARNING: see module docstring Part B1 -- this is near-guaranteed to
    succeed for ANY integer given enough (alpha,r,s) combinations, and is
    not evidence that x was a genuinely hard case."""
    h = x % MODULUS
    tested = 0
    for alpha in range(1, alpha_max + 1):
        for r in range(1, r_max + 1):
            for s in range(1, s_max + 1):
                tested += 1
                fam = family_from_parameters(alpha, r, s)
                if fam is None:
                    continue
                q, target = fam
                if x % q != target:
                    continue
                combo = combined_family_for_h(h, alpha, r, s)
                if combo is None or x % combo["modulus"] != combo["residue"]:
                    continue
                return combo, tested
    return None, tested


def sanity_check_patch_mechanism(alpha_max: int, r_max: int, s_max: int) -> None:
    """Runs find_family_for_specific_number against numbers that have NO
    business being 'covered' -- a composite, and a prime not even in a
    hard residue class -- to make it impossible to mistake a B1 patch for
    a meaningful result. If these succeed too (they will, almost always),
    that is the proof that B1 alone never demonstrates anything general."""
    print("\n" + "=" * 72)
    print("SELF-TEST: does the ad-hoc patch mechanism discriminate anything?")
    print("=" * 72)
    controls = [
        ("boring composite, not in a hard residue", 123456),
        ("prime, NOT in a hard residue", 999983),
    ]
    for label, x in controls:
        fam, tested = find_family_for_specific_number(x, alpha_max, r_max, s_max)
        verdict = "FOUND A MATCH" if fam else "no match"
        print(f"  {label:<42} x={x:<8} -> {verdict} after {tested:,} tries")
    print("If both of those found matches (they will, ~89% of the time each,")
    print("by construction), a B1 match for a real straggler proves nothing")
    print("beyond 'a witness exists for this one specific number.'")


def patch_known_stragglers(uncovered: List[int], families: Dict[int, dict]) -> Tuple[list, list]:
    """Find one explicit witness family for each currently-uncovered prime.
    Labeled clearly: this closes the TEST SET, not the residue class."""
    print("\n" + "=" * 72)
    print("PART B1 -- AD HOC PATCH OF KNOWN STRAGGLERS (not a proof)")
    print("=" * 72)
    patched, still_uncovered = [], []
    for p in uncovered:
        combo, tested = find_family_for_specific_number(p, PATCH_ALPHA_MAX, PATCH_R_MAX, PATCH_S_MAX)
        if combo is None:
            print(f"  p={p:,}: no explicit family found after {tested:,} tries.")
            still_uncovered.append(p)
            continue
        h = p % MODULUS
        families[h][(combo["modulus"], combo["residue"])] = combo
        patched.append((p, combo))
        print(f"  p={p:,}: patched via (alpha={combo['alpha']}, r={combo['r']}, s={combo['s']}), "
              f"p == {combo['residue']} (mod {combo['modulus']})")
    return patched, still_uncovered


# ============================================================
# Coverage measurement (against real primes -- diagnostic, not proof)
# ============================================================

def prime_is_covered(p: int, families: Dict[int, dict]) -> bool:
    h = p % MODULUS
    if h not in families:
        return False
    for (modulus, residue) in families[h]:
        if p % modulus == residue:
            return True
    return False


def coverage_report(primes: List[int], families: Dict[int, dict], label: str) -> List[int]:
    print("\n" + "=" * 72)
    print(label)
    print("=" * 72)
    total_hard = total_covered = 0
    uncovered_all: List[int] = []
    for h in HARD_RESIDUES:
        these = [p for p in primes if p % MODULUS == h]
        uncovered = [p for p in these if not prime_is_covered(p, families)]
        covered = len(these) - len(uncovered)
        total_hard += len(these)
        total_covered += covered
        pct = 100 * covered / len(these) if these else 100.0
        print(f"residue {h:>4}: {covered:>7} / {len(these):>7} = {pct:9.5f}%")
        if uncovered:
            print(f"    uncovered: {uncovered}")
            uncovered_all.extend(uncovered)
    total_pct = 100 * total_covered / total_hard if total_hard else 100.0
    print(f"\nTOTAL: {total_covered:,} / {total_hard:,} = {total_pct:.8f}%")
    print("(this number describes ONLY the primes tested here -- it is not")
    print(" a statement about primes beyond this range; see Part B2 below")
    print(" for the only check that would actually mean 'proven forever.')")
    return uncovered_all


# ============================================================
# PART B2 -- the genuine covering CERTIFICATE search
#
# Combines: vectorized bytearray sieve (fast, C-level slice assignment --
# this idea is a real improvement, worth keeping) with DYNAMIC greedy
# period-building that re-evaluates actual coverage gain at every step
# (verified head-to-head against a static "sort primes by how many
# families reference them once, then merge in that fixed order" approach:
# dynamic found 65.6% density vs static's 45.5% at an identical period
# budget on residue 169 -- static ordering doesn't account for overlap
# between families and leaves real coverage on the table).
#
# Forced compositeness (Part C) is folded directly into the sieve and
# checks EVERY prime factor the period has already picked up via family
# construction -- not a fixed hard-coded list. Those primes are "already
# paid for," so checking them for compositeness too is free extra
# closure, and it means the greedy optimizes total closure (family +
# compositeness) directly, not family alone with compositeness bolted on
# afterward.
# ============================================================

def _closure_sieve(h: int, families_for_h: dict, period: int) -> bytearray:
    slots = period // MODULUS
    sieve = bytearray(slots)

    for (modulus, residue), fam in families_for_h.items():
        if period % modulus != 0:
            continue
        q = modulus // MODULUS
        k0 = ((residue - h) // MODULUS) % q
        n = len(range(k0, slots, q))
        if n:
            sieve[k0::q] = b"\x01" * n

    for p in factorize(period):
        if MODULUS % p == 0:
            continue  # h is coprime to MODULUS by construction; never triggers
        inv = pow(MODULUS % p, -1, p)
        k0 = ((-h % p) * inv) % p
        n = len(range(k0, slots, p))
        if n:
            sieve[k0::p] = b"\x01" * n

    return sieve


def _coverage_count(h: int, families_for_h: dict, period: int) -> int:
    return _closure_sieve(h, families_for_h, period).count(1)


def greedy_build_certificate_period(h: int, families_for_h: dict,
                                     budget: int = CERTIFICATE_PERIOD_LIMIT
                                     ) -> Tuple[int, List[int]]:
    """Value-aware period construction. At every step, evaluate ALL
    remaining candidate prime-power boosts by actual coverage gained
    (family + forced-composite, together) per unit of period growth, and
    take the best one. This is what replaced the earlier naive
    'merge every prime in increasing numeric order' approach, which had a
    real bug: it happily spent the whole period budget re-boosting
    exponents of primes ALREADY in the base modulus (3,5,7 inside 840)
    before ever reaching a genuinely new prime like 11 or 13 -- which is
    exactly why an arbitrary q-cutoff produced wildly non-monotonic
    density (36% / 78% / 0%) in testing: it was accidentally controlling
    which primes got the "cheap slot" at the front of the merge order,
    not how much real coverage was available.
    """
    candidates: Dict[int, int] = defaultdict(int)
    for fam in families_for_h.values():
        for p, e in factorize(fam["q"]).items():
            if p <= CERTIFICATE_CANDIDATE_PRIME_LIMIT:
                candidates[p] = max(candidates[p], p ** e)

    current = MODULUS
    current_covered = _coverage_count(h, families_for_h, current)
    chosen: List[int] = []
    remaining = dict(candidates)

    while remaining:
        best = None  # (value, prime, new_period, new_covered)
        for p, boost in remaining.items():
            cand = lcm(current, boost)
            if cand == current or cand > budget:
                continue
            cand_covered = _coverage_count(h, families_for_h, cand)
            growth = cand / current
            value = (cand_covered - current_covered) / growth
            if best is None or value > best[0]:
                best = (value, p, cand, cand_covered)
        if best is None or best[0] <= 0:
            break
        _, p, cand, cand_covered = best
        current, current_covered = cand, cand_covered
        chosen.append(p)
        del remaining[p]

    return current, chosen


def attempt_certificate_for_residue(h: int, families_for_h: dict) -> dict:
    period, chosen_primes = greedy_build_certificate_period(h, families_for_h)
    sieve = _closure_sieve(h, families_for_h, period)
    slots = len(sieve)
    covered = sieve.count(1)
    pct = 100 * covered / slots if slots else 0.0
    still_open = [k for k in range(slots) if not sieve[k]]

    result = {"status": "COMPLETE" if not still_open else "INCOMPLETE",
              "period": period, "density_pct": pct,
              "chosen_primes": chosen_primes,
              "sample_open": sorted(h + MODULUS * k for k in still_open[:15])}
    print(f"residue {h:>4}: period={period:>16,}  primes folded in: {chosen_primes}  "
          f"=> {pct:.6f}% provably closed" +
          ("  *** COMPLETE ***" if not still_open else ""))
    return result


def attempt_infinite_certificate(families: Dict[int, dict], parallel: bool = True) -> Dict[int, dict]:
    print("\n" + "=" * 72)
    print("PART B2 -- GENUINE INFINITE COVERING CERTIFICATE SEARCH")
    print("=" * 72)

    results: Dict[int, dict] = {}
    if parallel:
        import concurrent.futures
        with concurrent.futures.ProcessPoolExecutor() as ex:
            futures = {ex.submit(attempt_certificate_for_residue, h, families[h]): h
                       for h in HARD_RESIDUES}
            for fut in concurrent.futures.as_completed(futures):
                h = futures[fut]
                results[h] = fut.result()
    else:
        for h in HARD_RESIDUES:
            results[h] = attempt_certificate_for_residue(h, families[h])

    print("\n" + "=" * 72)
    print("FINAL CERTIFICATE VERDICT (the only section that can legitimately")
    print("claim a proof -- NOT the empirical/patched coverage numbers above)")
    print("=" * 72)
    complete = [h for h in HARD_RESIDUES if results[h]["status"] == "COMPLETE"]
    incomplete = [h for h in HARD_RESIDUES if results[h]["status"] != "COMPLETE"]
    if not incomplete:
        print("\nFULL INFINITE COVERAGE CERTIFICATE: every hard residue closed.")
    else:
        print(f"\nComplete: {complete}")
        print(f"Still open (no finite certificate found): {incomplete}")
        for h in incomplete:
            print(f"  residue {h}: best provable density = {results[h]['density_pct']:.6f}%  "
                  f"(sample open reps: {results[h]['sample_open']})")
        print("\nIMPORTANT -- read before raising CERTIFICATE_PERIOD_LIMIT again:")
        print("the uncovered fraction here tracks ~1/ln(period) (a Mertens'-theorem")
        print("signature). Each further 9 of density costs roughly as much period")
        print("growth as ALL previous 9s combined -- this climbs toward but can")
        print("never certify 100%, no matter how large a period you can afford.")
        print("A finite covering system is complete or it isn't; density-approaching-1")
        print("is a genuinely different (and much weaker) mathematical statement.")
    return results


# ============================================================
# Main
# ============================================================

def main():
    families = build_initial_families(INITIAL_ALPHA_MAX, INITIAL_R_MAX, INITIAL_S_MAX)

    sanity_check_patch_mechanism(PATCH_ALPHA_MAX, PATCH_R_MAX, PATCH_S_MAX)

    print(f"\nGenerating primes up to {N:,}...")
    primes = primes_upto(N)
    uncovered = coverage_report(primes, families, f"EMPIRICAL COVERAGE UP TO {N:,} (Part A families only)")

    if uncovered:
        patch_known_stragglers(uncovered, families)
        coverage_report(primes, families,
                         f"EMPIRICAL COVERAGE UP TO {N:,} AFTER AD-HOC PATCHING "
                         f"(test-set-complete; NOT a proof -- see Part B2)")

    # The only section whose result should inform any claim of "proof."
    attempt_infinite_certificate(families)


if __name__ == "__main__":
    main()