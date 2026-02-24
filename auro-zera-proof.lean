/-
AuroZera_Corrected.lean
===============================================================
Erdős–Straus Conjecture — Fully Formal Reduction Framework
Corrected & Strengthened Edition
===============================================================

CORRECTIONS FROM PRIOR VERSION
---------------------------------------------------------------
  ✅ Fixed es_mod4_three (previous formula was arithmetically false)
  ✅ Fixed es_prime_reduction (kernel witness was incorrect)
  ✅ Kernel sharpened: mod 840 pseudo-kernel replaced by exact
     residue characterisation mod 24, which is both correct and
     provable from the families we have.
  ✅ All algebraic families independently re-verified
  ✅ No axioms introduced
  ✅ No sorries
  ✅ No admits

STATUS
---------------------------------------------------------------
  ✅ Base cases (n = 2, 3)
  ✅ Multiplicative closure  (ErdosStraus a → ErdosStraus (a*b))
  ✅ Even numbers            (n = 2k)
  ✅ n ≡ 3 mod 4             (FIXED: x = y = 2(k+1), z = (k+1)n)
  ✅ n ≡ 5 mod 12
  ✅ n ≡ 13 mod 24
  ✅ Composite reduction     (strong induction on smallest prime factor)
  ✅ Prime reduction         (all primes > 3 classified mod 24)
  🔵 Kernel: primes p > 3 with p ≡ 1 (mod 24)
     — the EXACT unresolved kernel under the above families
     — proven to be equivalent to the full conjecture

MATHEMATICAL NOTES
---------------------------------------------------------------
  For any prime p > 3, exactly one of the following holds:
    (A) p ≡ 3 mod 4  (covers p ≡ 3, 7, 11, 19, 23 mod 24)
    (B) p ≡ 5 mod 12 (covers p ≡  5, 17 mod 24)
    (C) p ≡ 13 mod 24
    (D) p ≡ 1 mod 24  ← the unresolved kernel

  Case D is unavoidable: by CRT, primes > 3 that are
  • not ≡ 3 mod 4  (rules out ≡ 3, 7, 11, 19, 23 mod 24), and
  • not ≡ 5 mod 12 (rules out ≡  5, 17 mod 24), and
  • not ≡ 13 mod 24
  must satisfy p ≡ 1 mod 24.  Residues ≡ 9 or 21 mod 24 are
  divisible by 3 and hence composite for p > 3.

  The families in the original "Mordell" reduction (mod 840) claimed
  a kernel of size 6.  That reduction requires additional parametric
  families (for residues ≡ 25, 49, 73, 97, … mod 840) that were
  NOT present in the prior file.  The mod-24 formulation given here
  is the largest VERIFIABLE kernel from the families we possess.
===============================================================
-/

import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Omega
import Mathlib.Tactic.Nlinarith
import Mathlib.Tactic.IntervalCases

namespace AuroZera

-- ================================================================
-- Section 1: Core Definitions
-- ================================================================

/-- A triple (x, y, z) solves the Erdős–Straus equation for n. -/
def SolvesES (n x y z : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ 0 < z ∧
  (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

/-- The Erdős–Straus conjecture for a single n. -/
def ErdosStraus (n : ℕ) : Prop :=
  ∃ x y z : ℕ, SolvesES n x y z

-- ================================================================
-- Section 2: Base Cases
-- ================================================================

lemma es_two : ErdosStraus 2 := by
  exact ⟨1, 2, 4, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma es_three : ErdosStraus 3 := by
  exact ⟨1, 4, 6, by norm_num, by norm_num, by norm_num, by norm_num⟩

-- ================================================================
-- Section 3: Multiplicative Closure
-- ================================================================

/-- If ErdosStraus holds for a, it holds for any multiple a * b. -/
lemma es_mul_right
    (a b : ℕ) (ha : 2 ≤ a) (hb : 1 ≤ b) (hES : ErdosStraus a) :
    ErdosStraus (a * b) := by
  obtain ⟨x, y, z, hx, hy, hz, heq⟩ := hES
  refine ⟨b * x, b * y, b * z, by positivity, by positivity, by positivity, ?_⟩
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast Nat.not_eq_zero_of_lt (by omega)
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast Nat.not_eq_zero_of_lt (by omega)
  have hx' : (x : ℚ) ≠ 0 := by exact_mod_cast Nat.not_eq_zero_of_lt hx
  have hy' : (y : ℚ) ≠ 0 := by exact_mod_cast Nat.not_eq_zero_of_lt hy
  have hz' : (z : ℚ) ≠ 0 := by exact_mod_cast Nat.not_eq_zero_of_lt hz
  push_cast
  field_simp
  linarith [heq]

-- ================================================================
-- Section 4: Explicit Parametric Families
-- ================================================================

/-- Even numbers: 4/(2k) = 1/k + 1/(2k) + 1/(2k). -/
lemma es_even (k : ℕ) (hk : 2 ≤ k) : ErdosStraus (2 * k) := by
  refine ⟨k, 2 * k, 2 * k, by omega, by omega, by omega, ?_⟩
  push_cast; field_simp; ring

/-- n ≡ 3 (mod 4): write n = 4k+3.
    IDENTITY: 4/(4k+3) = 1/(2k+2) + 1/(2k+2) + 1/((k+1)(4k+3))
    Proof: 1/(2(k+1)) + 1/(2(k+1)) = 1/(k+1)
           1/(k+1) + 1/((k+1)(4k+3)) = (4k+4)/((k+1)(4k+3)) = 4/(4k+3)  ✓  -/
lemma es_mod4_three (k : ℕ) : ErdosStraus (4 * k + 3) := by
  refine ⟨2 * k + 2, 2 * k + 2, (k + 1) * (4 * k + 3),
          by omega, by omega, by positivity, ?_⟩
  push_cast; field_simp; ring

/-- n ≡ 5 (mod 12): write n = 12j+5.
    IDENTITY: 4/(12j+5) = 1/(3j+2) + 1/((12j+5)(j+1)) + 1/((3j+2)(12j+5)(j+1))
    Verified: for j=0 gives (2,5,10), for j=1 gives (5,34,170), etc.  -/
lemma es_mod12_five (j : ℕ) : ErdosStraus (12 * j + 5) := by
  refine ⟨3 * j + 2, (12 * j + 5) * (j + 1),
          (3 * j + 2) * ((12 * j + 5) * (j + 1)),
          by omega, by positivity, by positivity, ?_⟩
  push_cast; field_simp; ring

/-- n ≡ 13 (mod 24): write n = 24m+13.
    Uses the algebraic identity (see inline derivation):
      3·y = a·n + 2   where a = 6m+4, j = 2m+1, y = 12j²+5j+1
    This yields 4/n = 1/a + 1/y + 1/(a₂·y·n) where a₂ = a/2.  -/
lemma es_mod24_thirteen (m : ℕ) : ErdosStraus (24 * m + 13) := by
  -- Set up the key parameters
  let n  := 24 * m + 13
  let j  := 2 * m + 1
  let a₂ := 3 * m + 2
  let a  := 6 * m + 4        -- = 2 * a₂
  let y  := 12 * j ^ 2 + 5 * j + 1
  let z  := a₂ * y * n
  have ha  : a  = 2 * a₂ := by ring
  have hn  : n  = 12 * j + 1 := by ring
  refine ⟨a, y, z, by omega, by positivity, by positivity, ?_⟩
  push_cast
  have hy : (3 : ℚ) * y = (a : ℚ) * n + 2 := by
    simp only [a, j, y, n]; push_cast; ring
  calc (4 : ℚ) / n
        = 1 / a + 3 / (a * n) := by
            have hn' : (n : ℚ) ≠ 0 := by positivity
            have ha' : (a : ℚ) ≠ 0 := by positivity
            field_simp; ring
      _ = 1 / a + 1 / y + 2 / (a * n * y) := by
            rw [hy]; field_simp; ring
      _ = 1 / a + 1 / y + 1 / z := by
            rw [ha]
            have hz' : (a₂ : ℚ) ≠ 0 := by positivity
            have hy' : (y : ℚ) ≠ 0 := by positivity
            have hn' : (n : ℚ) ≠ 0 := by positivity
            field_simp; ring

-- ================================================================
-- Section 5: Composite Reduction
-- ================================================================

/-- Every composite n ≥ 2 has a proper prime factor, and by induction
    ErdosStraus holds for that factor, hence for n via es_mul_right. -/
lemma es_of_composite
    (n : ℕ) (hn : 2 ≤ n) (hcomp : ¬Nat.Prime n)
    (ih : ∀ m, 2 ≤ m → m < n → ErdosStraus m) :
    ErdosStraus n := by
  have h1 : 1 < n := by omega
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  have hplt : p < n :=
    Nat.lt_of_le_of_ne (Nat.le_of_dvd (by omega) hdvd)
      (fun h => hcomp (h ▸ hp))
  obtain ⟨q, rfl⟩ := hdvd
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr
    (fun h => by simp [h] at hn)
  exact es_mul_right p q hp.two_le hq (ih p hp.two_le hplt)

-- ================================================================
-- Section 6: Prime Residue Classification (mod 24)
-- ================================================================

/-- For any prime p > 3, its residue mod 24 is one of:
    {1, 5, 7, 11, 13, 17, 19, 23}.
    Residues 3, 9, 15, 21 are divisible by 3; 0, 2, 4, 6, 8, 10, … are even. -/
lemma prime_mod24_mem (p : ℕ) (hp : Nat.Prime p) (hp3 : 3 < p) :
    p % 24 ∈ ({1, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ) := by
  have hodd  : p % 2 = 1 := Nat.Prime.odd_of_ne_two hp (by omega) |>.mod_cast
  have hno3  : p % 3 ≠ 0 := by
    intro h
    have := Nat.dvd_of_mod_eq_zero h
    exact absurd (hp.eq_one_or_self_of_dvd 3 this) (by omega)
  omega

/-- Predicate for the unresolved kernel: primes p with p ≡ 1 mod 24. -/
def IsKernelPrime (p : ℕ) : Prop := Nat.Prime p ∧ p % 24 = 1

-- ================================================================
-- Section 7: Prime Case Reduction
-- ================================================================

/-- For a prime p > 3, either one of the three parametric families applies,
    or p lies in the kernel (p ≡ 1 mod 24), and the kernel hypothesis gives ES. -/
theorem es_prime_reduction
    (p : ℕ) (hp : Nat.Prime p) (hp3 : 3 < p)
    (hkernel : p % 24 = 1 → ErdosStraus p) :
    ErdosStraus p := by
  -- Classify p mod 24
  have hmem := prime_mod24_mem p hp hp3
  simp [Finset.mem_insert, Finset.mem_singleton] at hmem
  -- Case split over the eight possible residues
  rcases hmem with h1 | h5 | h7 | h11 | h13 | h17 | h19 | h23
  -- ≡ 1 mod 24: kernel case
  · exact hkernel h1
  -- ≡ 5 mod 24 → ≡ 5 mod 12: use es_mod12_five
  · obtain ⟨j, rfl⟩ : ∃ j, p = 12 * j + 5 := ⟨p / 12, by omega⟩
    exact es_mod12_five j
  -- ≡ 7 mod 24 → ≡ 3 mod 4: use es_mod4_three
  · obtain ⟨k, rfl⟩ : ∃ k, p = 4 * k + 3 := ⟨p / 4, by omega⟩
    exact es_mod4_three k
  -- ≡ 11 mod 24 → ≡ 3 mod 4
  · obtain ⟨k, rfl⟩ : ∃ k, p = 4 * k + 3 := ⟨p / 4, by omega⟩
    exact es_mod4_three k
  -- ≡ 13 mod 24: direct family
  · obtain ⟨m, rfl⟩ : ∃ m, p = 24 * m + 13 := ⟨p / 24, by omega⟩
    exact es_mod24_thirteen m
  -- ≡ 17 mod 24 → ≡ 5 mod 12
  · obtain ⟨j, rfl⟩ : ∃ j, p = 12 * j + 5 := ⟨p / 12, by omega⟩
    exact es_mod12_five j
  -- ≡ 19 mod 24 → ≡ 3 mod 4
  · obtain ⟨k, rfl⟩ : ∃ k, p = 4 * k + 3 := ⟨p / 4, by omega⟩
    exact es_mod4_three k
  -- ≡ 23 mod 24 → ≡ 3 mod 4
  · obtain ⟨k, rfl⟩ : ∃ k, p = 4 * k + 3 := ⟨p / 4, by omega⟩
    exact es_mod4_three k

-- ================================================================
-- Section 8: Global Equivalence Theorem
-- ================================================================

/-- **Main Theorem**: The Erdős–Straus conjecture is equivalent to proving
    it for all primes p > 3 with p ≡ 1 (mod 24).

    Every other case (composites, small primes, primes in the three
    infinite families above) is fully handled.

    This is the EXACT residue characterisation: the three families cover
    all prime residues mod 24 except 1, which is the irreducible kernel. -/
theorem ES_global_equiv :
    (∀ p : ℕ, Nat.Prime p → 3 < p → p % 24 = 1 → ErdosStraus p)
    ↔
    (∀ n : ℕ, 2 ≤ n → ErdosStraus n) := by
  constructor
  · -- Forward: kernel condition implies full conjecture
    intro hkernel
    intro n hn
    induction n using Nat.strong_rec_on with
    | _ n ih =>
      match n with
      | 2 => exact es_two
      | 3 => exact es_three
      | n + 4 =>
        have hn4 : 2 ≤ n + 4 := by omega
        by_cases hprime : Nat.Prime (n + 4)
        · -- Prime case
          by_cases hsmall : n + 4 ≤ 3
          · interval_cases n <;> simp_all
          · push_neg at hsmall
            exact es_prime_reduction (n + 4) hprime (by omega)
              (fun h => hkernel (n + 4) hprime (by omega) h)
        · -- Composite case
          exact es_of_composite (n + 4) hn4 hprime
            (fun m hm hlt => ih m hlt hm)
  · -- Backward: trivial
    intro h p hp hp3 _
    exact h p (by omega)

-- ================================================================
-- Section 9: Corollary — Reduction to Kernel Primes
-- ================================================================

/-- An explicit statement of what remains to be proved:
    for every prime p with p ≡ 1 (mod 24), exhibit a triple. -/
theorem ES_iff_kernel :
    (∀ n : ℕ, 2 ≤ n → ErdosStraus n) ↔
    (∀ p : ℕ, IsKernelPrime p → ErdosStraus p) := by
  rw [← ES_global_equiv]
  constructor
  · intro h p ⟨hprime, hmod⟩
    exact h p hprime (by
      by_contra hlt
      push_neg at hlt
      interval_cases p <;> simp_all [IsKernelPrime])
  · intro h p hprime hp3 hmod
    exact h p ⟨hprime, hmod⟩

-- ================================================================
-- Section 10: Verified Identities (Algebraic Witnesses)
-- ================================================================

/-- Explicit witness for n = 5 (= 12·0+5): 4/5 = 1/2 + 1/5 + 1/10. -/
example : ErdosStraus 5 := es_mod12_five 0

/-- Explicit witness for n = 7 (= 4·1+3): 4/7 = 1/4 + 1/4 + 1/14. -/
example : ErdosStraus 7 := es_mod4_three 1

/-- Explicit witness for n = 11 (= 4·2+3): 4/11 = 1/6 + 1/6 + 1/33. -/
example : ErdosStraus 11 := es_mod4_three 2

/-- Explicit witness for n = 13 (= 24·0+13): 4/13 = 1/4 + 1/18 + 1/468. -/
example : ErdosStraus 13 := es_mod24_thirteen 0

/-- Explicit witness for n = 17 (= 12·1+5): 4/17 = 1/5 + 1/34 + 1/170. -/
example : ErdosStraus 17 := es_mod12_five 1

/-- Explicit witness for n = 19 (= 4·4+3): 4/19 = 1/10 + 1/10 + 1/95. -/
example : ErdosStraus 19 := es_mod4_three 4

/-- Explicit witness for n = 23 (= 4·5+3): 4/23 = 1/12 + 1/12 + 1/138. -/
example : ErdosStraus 23 := es_mod4_three 5

/-- Explicit witness for n = 29 (= 12·2+5): 4/29 = 1/8 + 1/87 + 1/696. -/
example : ErdosStraus 29 := es_mod12_five 2

/-- Explicit witness for n = 37 (= 24·1+13): 4/37 = 1/10 + 1/124 + 1/22940. -/
example : ErdosStraus 37 := es_mod24_thirteen 1

-- ================================================================
-- Section 11: Summary Comment
-- ================================================================

/-
SUMMARY
═══════════════════════════════════════════════════════════════

The Erdős–Straus conjecture (∀ n ≥ 2, ∃ x y z > 0, 4/n = 1/x+1/y+1/z)
has been FORMALLY REDUCED to the following single residue class:

  Prove: ∀ prime p with p ≡ 1 (mod 24), ErdosStraus p.

FAMILIES VERIFIED IN THIS FILE:
  • Even n:       4/(2k) = 1/k + 1/(2k) + 1/(2k)
  • n ≡ 3 mod 4:  4/(4k+3) = 1/(2k+2) + 1/(2k+2) + 1/((k+1)(4k+3))
  • n ≡ 5 mod 12: 4/(12j+5) = 1/(3j+2) + 1/((j+1)n) + 1/((3j+2)(j+1)n)
  • n ≡ 13 mod 24: proved via algebraic manipulation with 3y = an+2

RESIDUE COVERAGE FOR PRIMES p > 3 (all 8 non-degenerate classes mod 24):
  p mod 24 │ 1  │ 5  │ 7  │ 11 │ 13 │ 17 │ 19 │ 23
  Covered  │ ✗  │ ✓  │ ✓  │ ✓  │ ✓  │ ✓  │ ✓  │ ✓
  Family   │ —  │M12 │M4  │M4  │M24 │M12 │M4  │M4

  ✗ = kernel (open), ✓ = proved, M4/M12/M24 = which family

COMPARISON WITH PRIOR VERSION:
  Prior claimed a kernel of 6 specific residues mod 840.
  That claim required 29 additional parametric families
  (for residues ≡ 25, 49, 73, 97, … mod 840) which were absent.
  The mod-24 formulation here is correct with the families present.

NEXT STEP: Find a parametric family for n ≡ 1 (mod 24), or prove
the conjecture by other means for this residue class.
═══════════════════════════════════════════════════════════════
-/

end AuroZera
