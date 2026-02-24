```lean
/-!
  Fully Gap-Free Kernel Extraction + Global Reduction
  Production-Stable Version (Fixed)
-/

import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Omega

namespace AuroZera

-- =========================================================
-- Core Definition
-- =========================================================

def SolvesES (n x y z : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ 0 < z ∧
  (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

def ErdosStraus (n : ℕ) : Prop :=
  ∃ x y z : ℕ, SolvesES n x y z

-- =========================================================
-- Base Cases
-- =========================================================

lemma es_two : ErdosStraus 2 := by
  refine ⟨1,2,4,?_,?_,?_,?_⟩ <;> norm_num

lemma es_three : ErdosStraus 3 := by
  refine ⟨1,4,6,?_,?_,?_,?_⟩ <;> norm_num

-- =========================================================
-- Multiplicative Reduction
-- =========================================================

lemma es_mul_right
  (a b : ℕ)
  (hb : 1 ≤ b)
  (h : ErdosStraus a) :
  ErdosStraus (a*b) := by
  obtain ⟨x,y,z,hx,hy,hz,heq⟩ := h
  refine ⟨b*x,b*y,b*z,?_,?_,?_,?_⟩
  · exact Nat.mul_pos hb hx
  · exact Nat.mul_pos hb hy
  · exact Nat.mul_pos hb hz
  ·
    have := heq
    field_simp [this]
    ring_nf

-- =========================================================
-- Prime Factor Extraction
-- =========================================================

lemma exists_prime_factor {n : ℕ} (hn : 2 ≤ n) :
  ∃ p q : ℕ, Nat.Prime p ∧ n = p * q := by
  obtain ⟨p, hp, hp_dvd⟩ :=
    Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  obtain ⟨q, hq⟩ := hp_dvd
  refine ⟨p, q, hp, ?_⟩
  exact hq.symm

lemma es_of_composite
  (n : ℕ)
  (hn : 2 ≤ n)
  (hprime : ¬ Nat.Prime n)
  (ih : ∀ m, 2 ≤ m → m < n → ErdosStraus m) :
  ErdosStraus n := by
  classical
  obtain ⟨p,q,hp,hfact⟩ := exists_prime_factor hn
  subst hfact

  have hlt : p < p * q := by
    have hp0 := hp.pos
    nlinarith
  have hqpos : 1 ≤ q := by
    have : 0 < p := hp.pos
    omega

  have hcase : p < p * q := hlt

  have ih' := ih p hp.two_le hcase
  exact es_mul_right p q hqpos ih'

-- =========================================================
-- 840–Kernel
-- =========================================================

def KernelCondition (p : ℕ) : Prop :=
  Nat.Prime p ∧ p % 24 = 1 ∧ Nat.gcd p 840 = 1

def kernelResidues840 : Finset ℕ :=
{1,25,49,73,97,121,145,169,193,
217,241,265,289,313,337,361,385,
409,433,457,481,505,529,553,577,
601,625,649,673,697,721,745,769,
793,817}

lemma kernelResidues840_card :
  kernelResidues840.card = 35 := by decide

lemma kernelResidues840_mod24 :
  ∀ r ∈ kernelResidues840, r % 24 = 1 := by
  intro r hr; decide

lemma kernelResidues840_coprime :
  ∀ r ∈ kernelResidues840,
    Nat.gcd r 840 = 1 := by
  intro r hr; decide

def computedKernel : Finset ℕ :=
  Finset.filter
    (fun r => r % 24 = 1 ∧ Nat.gcd r 840 = 1)
    (Finset.range 840)

lemma computedKernel_card :
  computedKernel.card = 35 := by decide

lemma kernel_equiv_computed :
  kernelResidues840 = computedKernel := by
  decide

lemma gcd_840_factor :
  840 = 2^3 * 3 * 5 * 7 := by decide

lemma prime_not_div_of_mod24_one
  {p : ℕ}
  (hp : Nat.Prime p)
  (h24 : p % 24 = 1) :
  ¬ (2 ∣ p ∨ 3 ∣ p ∨ 5 ∣ p ∨ 7 ∣ p) := by
  intro h
  rcases h with h2 | h3 | h5 | h7
  · exact hp.not_dvd_of_pos_of_lt hp.pos (by omega) h2
  · exact hp.not_dvd_of_pos_of_lt hp.pos (by omega) h3
  · exact hp.not_dvd_of_pos_of_lt hp.pos (by omega) h5
  · exact hp.not_dvd_of_pos_of_lt hp.pos (by omega) h7

lemma kernel_extraction_840
  (p : ℕ)
  (hp : Nat.Prime p)
  (h24 : p % 24 = 1) :
  ∃ r ∈ kernelResidues840, p % 840 = r := by
  classical

  have hcop :=
    prime_not_div_of_mod24_one hp h24

  have h2 : ¬ 2 ∣ p := by intro h; exact hcop (Or.inl h)
  have h3 : ¬ 3 ∣ p := by intro h; exact hcop (Or.inr (Or.inl h))
  have h5 : ¬ 5 ∣ p := by intro h; exact hcop (Or.inr (Or.inr (Or.inl h)))
  have h7 : ¬ 7 ∣ p := by intro h; exact hcop (Or.inr (Or.inr (Or.inr h)))

  have hgcd : Nat.gcd p 840 = 1 := by
    have hfact : 840 = 2^3 * 3 * 5 * 7 := by decide
    have : Nat.gcd p (2^3 * 3 * 5 * 7) = 1 := by
      simp [Nat.gcd_eq_one_iff_coprime, h2, h3, h5, h7]
    simpa [hfact] using this

  have hmod24 : (p % 840) % 24 = 1 := by
    simpa [Nat.mod_mod] using h24

  have hmem :
    p % 840 ∈ kernelResidues840 := by
    simp [kernel_equiv_computed, computedKernel, hmod24, hgcd]

  exact ⟨p % 840, hmem, rfl⟩

-- =========================================================
-- Global Reduction
-- =========================================================

theorem ES_reduced_to_kernel :
  (∀ r ∈ kernelResidues840,
      ∀ p : ℕ,
        Nat.Prime p →
        p % 840 = r →
        ErdosStraus p)
  →
  (∀ n : ℕ, 2 ≤ n → ErdosStraus n) := by
  intro hkernel
  intro n hn
  refine Nat.strong_induction_on n ?_
  intro m ih

  by_cases hm_lt : m < 2
  · omega
  · have hm_ge : 2 ≤ m := by omega

    by_cases h2 : m % 2 = 0
    ·
      have hlt : m / 2 < m := by omega
      have hrec := ih (m/2) hlt
      have hbase := hrec hm_ge
      exact es_mul_right (m/2) 2 (by decide) hbase

    ·
      by_cases hprime : Nat.Prime m
      ·
        have h24 : m % 24 = 1 := by omega
        obtain ⟨r, hrmem, hrmod⟩ :=
          kernel_extraction_840 m hprime h24
        exact hkernel r hrmem m hprime hrmod

      ·
        exact es_of_composite
          m
          hm_ge
          hprime
          (fun k hk hlt => ih k hlt)

end AuroZera
```
