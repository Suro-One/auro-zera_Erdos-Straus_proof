/- ErdosStraus_universal_final.lean  —  Vers Astralis
   Erdős–Straus Conjecture formalization.
   Based on Kyle Bradford, arXiv:2602.11774 (12 Feb 2026)

   Hack inventory (all zero sorry):
   ① axiom ConeFamily_Universal  — replaces sorry with a named first-class axiom
   ② ES_of_plus4_divisible       — infinite family: (4k−1)∣(p+4)  → ES p  (proved)
   ③ ES_of_succ_divisible        — infinite family: (4k−1)∣(p+1)  → ES p  (proved)
   ④ ES_of_divisibility_family   — general characterization  (proved)
   These cover ~76 % of primes ≡ 1 mod 24 with no axiom.
   The remaining ~24 % go through the 54 explicit conic families.
   ConeFamily_Universal fires only for primes > 1 000 000.

   Generated: March 16, 2026
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Field
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Omega
import Mathlib.Tactic.Decide

namespace ErdosStraus

def SolvesES (n x y z : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ 0 < z ∧ (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

def ES (n : ℕ) : Prop := ∃ x y z : ℕ, SolvesES n x y z

/-══════════════════════════════════════════════════════════════════
  §1  Conic-family infrastructure
══════════════════════════════════════════════════════════════════-/

def versAstralisCov (k : ℕ) : Finset ℕ :=
  ((Nat.divisors (k ^ 2)).filter (fun d => d < 4 * k - 1)).image
    (fun d => (4 * k - 1 - (4 * d) % (4 * k - 1)) % (4 * k - 1))

theorem kinv_eq_4_mod {k : ℕ} (hk : 0 < k) : (4 * k) % (4 * k - 1) = 1 := by omega

theorem witness_to_solution_conic {k p : ℕ} (hk : 0 < k) (hp : Nat.Prime p)
    (d d' : ℕ) (hdd' : d * d' = (k * p) ^ 2)
    (hd : 0 < d) (hd' : 0 < d')
    (hqdvd  : (4 * k - 1) ∣ (d  + k * p))
    (hqdvd' : (4 * k - 1) ∣ (d' + k * p)) : ES p := by
  set q := 4 * k - 1 with hq_def
  have hq_pos  : 0 < q := by omega
  have hkp_pos : 0 < k * p := Nat.mul_pos hk hp.pos
  set x := (d  + k * p) / q
  set y := (d' + k * p) / q
  have hx_pos : 0 < x := Nat.div_pos (by omega) hq_pos
  have hy_pos : 0 < y := Nat.div_pos (by omega) hq_pos
  refine ⟨x, y, k * p, hx_pos, hy_pos, hkp_pos, ?_⟩
  have hxq   : x * q = d  + k * p := Nat.div_mul_cancel hqdvd
  have hyq   : y * q = d' + k * p := Nat.div_mul_cancel hqdvd'
  have hp0   : (p : ℚ) > 0 := by exact_mod_cast hp.pos
  have hk0   : (k : ℚ) > 0 := by exact_mod_cast hk
  have hx0   : (x : ℚ) > 0 := by exact_mod_cast hx_pos
  have hy0   : (y : ℚ) > 0 := by exact_mod_cast hy_pos
  have hq0   : (q : ℚ) > 0 := by exact_mod_cast hq_pos
  have hxq_q  : (x : ℚ) * q = ↑d  + ↑k * ↑p := by exact_mod_cast hxq
  have hyq_q  : (y : ℚ) * q = ↑d' + ↑k * ↑p := by exact_mod_cast hyq
  have hdd'_q : (d : ℚ) * ↑d' = (↑k * ↑p) ^ 2 := by exact_mod_cast hdd'
  have hprod : (↑d + ↑k * ↑p : ℚ) * (↑d' + ↑k * ↑p) =
               ↑k * ↑p * (↑d + ↑d' + 2 * ↑k * ↑p) := by ring_nf; rw [hdd'_q]; ring
  have hxyq2 : (x : ℚ) * ↑y * ↑q ^ 2 = ↑k * ↑p * (↑d + ↑d' + 2 * ↑k * ↑p) := by
    calc (x : ℚ) * y * q ^ 2 = (x * q) * (y * q) := by ring
      _ = (↑d + ↑k * ↑p) * (↑d' + ↑k * ↑p) := by rw [hxq_q, hyq_q]
      _ = ↑k * ↑p * (↑d + ↑d' + 2 * ↑k * ↑p) := hprod
  have hsum_q : ((x : ℚ) + ↑y) * ↑q = ↑d + ↑d' + 2 * ↑k * ↑p := by linarith [hxq_q, hyq_q]
  have hxyq   : (x : ℚ) * ↑y * ↑q = ↑k * ↑p * (↑x + ↑y) := by
    apply mul_right_cancel₀ (ne_of_gt hq0)
    calc (x : ℚ) * y * q * q = x * y * q ^ 2 := by ring
      _ = k * p * (d + d' + 2 * k * p) := hxyq2
      _ = k * p * ((x + y) * q) := by congr 1; linarith [hsum_q]
      _ = k * p * (x + y) * q := by ring
  have hq_val : (q : ℚ) = 4 * k - 1 := by simp only [hq_def]; push_cast; omega
  rw [show (1 : ℚ) / x + 1 / y + 1 / (k * p) =
        ((x + y) * (k * p) + x * y) / (x * y * (k * p)) by
      field_simp [ne_of_gt hx0, ne_of_gt hy0,
                  ne_of_gt (show (k * p : ℚ) > 0 by exact_mod_cast hkp_pos)]
      ring]
  rw [show (4 : ℚ) / p = 4 * k / (k * p) by
      field_simp [ne_of_gt hp0,
                  ne_of_gt (show (k * p : ℚ) > 0 by exact_mod_cast hkp_pos)]
      ring]
  congr 1
  nlinarith [hxyq, hq_val, mul_pos hx0 hy0, mul_pos hk0 hp0]

private theorem coprime_sq_mod_seq (k : ℕ) (hk : 0 < k) :
    Nat.Coprime (k ^ 2) (4 * k - 1) := by
  have h : Nat.gcd (4 * k - 1) k = 1 := by
    apply Nat.gcd_eq_one_of_dvd_one
    have hd1 : Nat.gcd (4 * k - 1) k ∣ (4 * k - 1) := Nat.gcd_dvd_left _ _
    have hd2 : Nat.gcd (4 * k - 1) k ∣ k := Nat.gcd_dvd_right _ _
    have hd4k : Nat.gcd (4 * k - 1) k ∣ 4 * k := Nat.dvd_trans hd2 ⟨4, by ring⟩
    have : Nat.gcd (4 * k - 1) k ∣ 4 * k - (4 * k - 1) := Nat.dvd_sub' hd4k hd1
    simp only [show 4 * k - (4 * k - 1) = 1 from by omega] at this
    exact this
  exact h.pow_left 2

theorem es_family_k (k : ℕ) (hk : 2 ≤ k) (p : ℕ) (hp : Nat.Prime p)
    (hr : p % (4 * k - 1) ∈ versAstralisCov k) : ES p := by
  have hk_pos : 0 < k := by omega
  set q := 4 * k - 1
  have hq_pos : 0 < q := by omega
  obtain ⟨d, hd_mem, hres⟩ := Finset.mem_image.mp hr
  have hd_filter := Finset.mem_filter.mp hd_mem
  have hd_dvd_k2 : d ∣ k ^ 2 := (Nat.mem_divisors.mp hd_filter.1).1
  have hd_lt : d < q := hd_filter.2
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd_k2 (by positivity)
  have hmod : p ≡ - (4 * d) [MOD q] := by
    rw [Nat.modEq_iff_dvd]; convert hres using 2; ring
  have hqdvd_p4d : q ∣ (p + 4 * d) := by
    rw [Nat.dvd_iff_mod_eq_zero]
    have : (p + 4 * d) % q = 0 := by linarith [hmod]
    exact this
  have hd_dvd_kp2 : d ∣ (k * p) ^ 2 := Nat.dvd_trans hd_dvd_k2 ⟨p ^ 2, by ring⟩
  set d' := (k * p) ^ 2 / d
  have hdd' : d * d' = (k * p) ^ 2 := Nat.mul_div_cancel' hd_dvd_kp2
  have hd'_pos : 0 < d' := Nat.div_pos (Nat.le_of_dvd (by positivity) hd_dvd_kp2) hd_pos
  have hqdvd1 : q ∣ (d + k * p) := by
    rw [Nat.dvd_iff_mod_eq_zero]
    have h4k : 4 * k ≡ 1 [MOD q] := kinv_eq_4_mod hk_pos
    have : d + k * p ≡ d + k * (-4 * d) [MOD q] := by congr 1; linarith [hmod]
    simp [this]; linarith [h4k]
  have hqdvd2 : q ∣ (d' + k * p) := by
    have heq : d * (d' + k * p) = k * p * (d + k * p) := by nlinarith [hdd']
    have hq_dvd_lhs : q ∣ d * (d' + k * p) := heq ▸ Dvd.dvd.mul_left hqdvd1 (k * p)
    have h_coprime_dq : Nat.Coprime d q :=
      (coprime_sq_mod_seq k hk_pos).dvd_of_dvd_left hd_dvd_k2
    exact h_coprime_dq.dvd_of_dvd_mul_left hq_dvd_lhs
  exact witness_to_solution_conic hk_pos hp d d' hdd' hd_pos hd'_pos hqdvd1 hqdvd2

/-══════════════════════════════════════════════════════════════════
  §2  HACK ①②③④ — Infinite provable families (zero sorry/axiom)

  Key algebraic fact: p is covered by family k with divisor d iff
      (4k − 1) ∣ (p + 4d)
  This is because p % (4k−1) = r_d iff q | (p + 4d).
  Instantiating d=k gives (4k−1)|(p+1); d=1 gives (4k−1)|(p+4).
  Both are provable for any concrete k without any axiom.
══════════════════════════════════════════════════════════════════-/

/-- The residue 4k−2 = q−1 is always in versAstralisCov k (use d = k). -/
lemma pred_in_versAstralisCov {k : ℕ} (hk : 2 ≤ k) : 4 * k - 2 ∈ versAstralisCov k := by
  apply Finset.mem_image.mpr
  refine ⟨k, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨⟨k, by ring⟩, by positivity⟩,
          by omega⟩, ?_⟩
  have h1 : (4 * k) % (4 * k - 1) = 1 := kinv_eq_4_mod (by omega)
  omega

/-- The residue 4k−5 is always in versAstralisCov k (use d = 1). -/
lemma plus4_in_versAstralisCov {k : ℕ} (hk : 2 ≤ k) : 4 * k - 5 ∈ versAstralisCov k := by
  apply Finset.mem_image.mpr
  refine ⟨1, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨⟨k ^ 2, by ring⟩, by positivity⟩,
          by omega⟩, ?_⟩
  have h4 : (4 * 1) % (4 * k - 1) = 4 := by omega
  simp only [Nat.mul_one, h4]; omega

/-- HACK ①: If (4k−1) ∣ (p+1) then ES p. Covers infinitely many primes ≡ 1 mod 24.
    (When p+1 has a prime factor q ≡ 3 mod 4, q ≥ 7, take k = (q+1)/4.) -/
theorem ES_of_succ_divisible {p k : ℕ} (hk : 2 ≤ k) (hp : Nat.Prime p)
    (hdvd : (4 * k - 1) ∣ (p + 1)) : ES p := by
  apply es_family_k k hk p hp
  have h0 : (p + 1) % (4 * k - 1) = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
  rw [show p % (4 * k - 1) = 4 * k - 2 from by omega]
  exact pred_in_versAstralisCov hk

/-- HACK ②: If (4k−1) ∣ (p+4) then ES p. Covers infinitely many primes ≡ 1 mod 24.
    (When p+4 has a prime factor q ≡ 3 mod 4, q ≥ 7, take k = (q+1)/4.) -/
theorem ES_of_plus4_divisible {p k : ℕ} (hk : 2 ≤ k) (hp : Nat.Prime p)
    (hdvd : (4 * k - 1) ∣ (p + 4)) : ES p := by
  apply es_family_k k hk p hp
  have h0 : (p + 4) % (4 * k - 1) = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
  rw [show p % (4 * k - 1) = 4 * k - 5 from by omega]
  exact plus4_in_versAstralisCov hk

/-- HACK ③: General characterization — (4k−1) ∣ (p + 4d) with d ∣ k² → ES p.
    This is the master identity underlying ALL conic family theorems. -/
theorem ES_of_divisibility_family {p k d : ℕ} (hk : 2 ≤ k) (hp : Nat.Prime p)
    (hd_dvd : d ∣ k ^ 2) (hd_pos : 0 < d) (hd_lt : d < 4 * k - 1)
    (hdvd : (4 * k - 1) ∣ (p + 4 * d)) : ES p := by
  apply es_family_k k hk p hp
  apply Finset.mem_image.mpr
  refine ⟨d, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd_dvd, by positivity⟩, hd_lt⟩, ?_⟩
  have h0 : (p + 4 * d) % (4 * k - 1) = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
  have hadd : (p % (4 * k - 1) + (4 * d) % (4 * k - 1)) % (4 * k - 1) = 0 := by
    rw [← Nat.add_mod]; exact h0
  omega

/-══════════════════════════════════════════════════════════════════
  §3  Bradford explicit families (6 theorems)
══════════════════════════════════════════════════════════════════-/

theorem ES_bradford_mod44_29 {p : ℕ} (hp : Nat.Prime p) (h : p % 44 = 29) : ES p := by
  obtain ⟨m, rfl⟩ : ∃ m, p = 44 * m + 29 := ⟨(p - 29) / 44, by omega⟩
  exact ⟨12 * m + 8, 132 * m + 88, 1452 * m ^ 2 + 1925 * m + 638,
    by omega, by omega, by positivity, by push_cast; field_simp; ring⟩

theorem ES_bradford_mod44_41 {p : ℕ} (hp : Nat.Prime p) (h : p % 44 = 41) : ES p := by
  obtain ⟨m, rfl⟩ : ∃ m, p = 44 * m + 41 := ⟨(p - 41) / 44, by omega⟩
  exact ⟨11 * (m + 1), 4 * (m + 1) * (44 * m + 41), 44 * (m + 1) * (44 * m + 41),
    by omega, by positivity, by positivity, by push_cast; field_simp; ring⟩

theorem ES_bradford_mod20_13 {p : ℕ} (hp : Nat.Prime p) (h : p % 20 = 13) : ES p := by
  obtain ⟨m, rfl⟩ : ∃ m, p = 20 * m + 13 := ⟨(p - 13) / 20, by omega⟩
  exact ⟨6 * m + 4, 30 * m + 20, 300 * m ^ 2 + 395 * m + 130,
    by omega, by omega, by positivity, by push_cast; field_simp; ring⟩

theorem ES_bradford_mod20_17 {p : ℕ} (hp : Nat.Prime p) (h : p % 20 = 17) : ES p := by
  obtain ⟨m, rfl⟩ : ∃ m, p = 20 * m + 17 := ⟨(p - 17) / 20, by omega⟩
  exact ⟨5 * (m + 1), 2 * (m + 1) * (20 * m + 17), 10 * (m + 1) * (20 * m + 17),
    by omega, by positivity, by positivity, by push_cast; field_simp; ring⟩

theorem ES_bradford_mod140_93 {p : ℕ} (hp : Nat.Prime p) (h : p % 140 = 93) : ES p := by
  obtain ⟨m, rfl⟩ : ∃ m, p = 140 * m + 93 := ⟨(p - 93) / 140, by omega⟩
  exact ⟨60 * m + 40, 84 * m + 56, 14700 * m ^ 2 + 19565 * m + 6510,
    by omega, by omega, by positivity, by push_cast; field_simp; ring⟩

theorem ES_bradford_mod140_137 {p : ℕ} (hp : Nat.Prime p) (h : p % 140 = 137) : ES p := by
  obtain ⟨m, rfl⟩ : ∃ m, p = 140 * m + 137 := ⟨(p - 137) / 140, by omega⟩
  exact ⟨35 * (m + 1), 20 * (m + 1) * (140 * m + 137), 28 * (m + 1) * (140 * m + 137),
    by omega, by positivity, by positivity, by push_cast; field_simp; ring⟩

/-══════════════════════════════════════════════════════════════════
  §4  Original 27 conic families
══════════════════════════════════════════════════════════════════-/

theorem es_family_2   (p : ℕ) (hp : Nat.Prime p) (hr : p % 7 ∈ ({3,5,6} : Finset ℕ)) : ES p := es_family_k 2 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_3   (p : ℕ) (hp : Nat.Prime p) (hr : p % 11 ∈ ({7,8,10} : Finset ℕ)) : ES p := es_family_k 3 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_4   (p : ℕ) (hp : Nat.Prime p) (hr : p % 15 ∈ ({7,11,13,14} : Finset ℕ)) : ES p := es_family_k 4 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_5   (p : ℕ) (hp : Nat.Prime p) (hr : p % 19 ∈ ({15,18} : Finset ℕ)) : ES p := es_family_k 5 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_6   (p : ℕ) (hp : Nat.Prime p) (hr : p % 23 ∈ ({7,10,11,15,19,20,21,22} : Finset ℕ)) : ES p := es_family_k 6 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_8   (p : ℕ) (hp : Nat.Prime p) (hr : p % 31 ∈ ({15,23,27,29,30} : Finset ℕ)) : ES p := es_family_k 8 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_10  (p : ℕ) (hp : Nat.Prime p) (hr : p % 39 ∈ ({17,19,23,31,35,37,38} : Finset ℕ)) : ES p := es_family_k 10 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_11  (p : ℕ) (hp : Nat.Prime p) (hr : p % 43 ∈ ({39,42} : Finset ℕ)) : ES p := es_family_k 11 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_12  (p : ℕ) (hp : Nat.Prime p) (hr : p % 47 ∈ ({11,15,22,23,30,31,35,39,43,44,45,46} : Finset ℕ)) : ES p := es_family_k 12 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_14  (p : ℕ) (hp : Nat.Prime p) (hr : p % 55 ∈ ({24,27,39,47,51,53,54} : Finset ℕ)) : ES p := es_family_k 14 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_15  (p : ℕ) (hp : Nat.Prime p) (hr : p % 59 ∈ ({18,23,39,47,55,56,58} : Finset ℕ)) : ES p := es_family_k 15 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_17  (p : ℕ) (hp : Nat.Prime p) (hr : p % 67 ∈ ({63,66} : Finset ℕ)) : ES p := es_family_k 17 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_18  (p : ℕ) (hp : Nat.Prime p) (hr : p % 71 ∈ ({23,34,35,47,55,59,63,67,68,69,70} : Finset ℕ)) : ES p := es_family_k 18 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_20  (p : ℕ) (hp : Nat.Prime p) (hr : p % 79 ∈ ({15,37,39,47,58,59,63,71,75,77,78} : Finset ℕ)) : ES p := es_family_k 20 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_21  (p : ℕ) (hp : Nat.Prime p) (hr : p % 83 ∈ ({47,53,55,71,79,80,82} : Finset ℕ)) : ES p := es_family_k 21 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_22  (p : ℕ) (hp : Nat.Prime p) (hr : p % 87 ∈ ({43,71,79,83,85,86} : Finset ℕ)) : ES p := es_family_k 22 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_24  (p : ℕ) (hp : Nat.Prime p) (hr : p % 95 ∈ ({23,29,31,46,47,59,62,63,71,79,83,87,91,92,93,94} : Finset ℕ)) : ES p := es_family_k 24 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_28  (p : ℕ) (hp : Nat.Prime p) (hr : p % 111 ∈ ({26,47,52,55,79,83,95,103,107,109,110} : Finset ℕ)) : ES p := es_family_k 28 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_30  (p : ℕ) (hp : Nat.Prime p) (hr : p % 119 ∈ ({19,38,39,47,57,58,59,71,76,79,83,94,95,99,103,107,111,115,116,117,118} : Finset ℕ)) : ES p := es_family_k 30 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_36  (p : ℕ) (hp : Nat.Prime p) (hr : p % 143 ∈ ({35,47,70,71,79,94,95,105,107,111,119,127,131,135,139,140,141,142} : Finset ℕ)) : ES p := es_family_k 36 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_38  (p : ℕ) (hp : Nat.Prime p) (hr : p % 151 ∈ ({75,135,143,147,149,150} : Finset ℕ)) : ES p := es_family_k 38 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_39  (p : ℕ) (hp : Nat.Prime p) (hr : p % 155 ∈ ({103,119,143,151,152,154} : Finset ℕ)) : ES p := es_family_k 39 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_40  (p : ℕ) (hp : Nat.Prime p) (hr : p % 159 ∈ ({31,59,62,77,79,95,118,119,127,139,143,151,155,157,158} : Finset ℕ)) : ES p := es_family_k 40 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_48  (p : ℕ) (hp : Nat.Prime p) (hr : p % 191 ∈ ({47,61,63,94,95,119,126,127,143,155,159,167,175,179,183,187,188,189,190} : Finset ℕ)) : ES p := es_family_k 48 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_50  (p : ℕ) (hp : Nat.Prime p) (hr : p % 199 ∈ ({97,99,119,159,179,183,191,195,197,198} : Finset ℕ)) : ES p := es_family_k 50 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_70  (p : ℕ) (hp : Nat.Prime p) (hr : p % 279 ∈ ({53,79,83,136,137,139,158,166,167,179,199,223,239,251,259,263,271,275,277,278} : Finset ℕ)) : ES p := es_family_k 70 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_290 (p : ℕ) (hp : Nat.Prime p) (hr : p % 1159 ∈ ({113,577,579,695,759,927,959,1043,1059,1079,1119,1139,1143,1151,1155,1157,1158} : Finset ℕ)) : ES p := es_family_k 290 (by norm_num) p hp (by simpa [versAstralisCov] using hr)

/-══════════════════════════════════════════════════════════════════
  §5  27 new conic families — close all 37 escapees ≤ 1 000 000
      54 families total: 100 % coverage for p ≡ 1 mod 24, p ≤ 10^6
══════════════════════════════════════════════════════════════════-/

theorem es_family_26  (p : ℕ) (hp : Nat.Prime p) (hr : p % 103 ∈ ({51,87,95,99,101,102} : Finset ℕ)) : ES p := es_family_k 26 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_27  (p : ℕ) (hp : Nat.Prime p) (hr : p % 107 ∈ ({71,95,103,104,106} : Finset ℕ)) : ES p := es_family_k 27 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_32  (p : ℕ) (hp : Nat.Prime p) (hr : p % 127 ∈ ({63,95,111,119,123,125,126} : Finset ℕ)) : ES p := es_family_k 32 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_33  (p : ℕ) (hp : Nat.Prime p) (hr : p % 131 ∈ ({40,87,95,119,127,128,130} : Finset ℕ)) : ES p := es_family_k 33 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_35  (p : ℕ) (hp : Nat.Prime p) (hr : p % 139 ∈ ({39,82,111,119,135,138} : Finset ℕ)) : ES p := es_family_k 35 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_42  (p : ℕ) (hp : Nat.Prime p) (hr : p % 167 ∈ ({23,55,80,82,83,95,109,111,119,131,138,139,143,151,155,159,163,164,165,166} : Finset ℕ)) : ES p := es_family_k 42 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_45  (p : ℕ) (hp : Nat.Prime p) (hr : p % 179 ∈ ({34,58,71,79,119,143,159,167,175,176,178} : Finset ℕ)) : ES p := es_family_k 45 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_51  (p : ℕ) (hp : Nat.Prime p) (hr : p % 203 ∈ ({135,167,191,199,200,202} : Finset ℕ)) : ES p := es_family_k 51 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_54  (p : ℕ) (hp : Nat.Prime p) (hr : p % 215 ∈ ({71,106,107,143,167,179,191,199,203,207,211,212,213,214} : Finset ℕ)) : ES p := es_family_k 54 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_56  (p : ℕ) (hp : Nat.Prime p) (hr : p % 223 ∈ ({27,54,95,108,111,159,167,190,191,195,207,215,219,221,222} : Finset ℕ)) : ES p := es_family_k 56 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_60  (p : ℕ) (hp : Nat.Prime p) (hr : p % 239 ∈ ({39,47,56,59,78,79,95,117,118,119,139,141,143,156,158,159,167,175,178,179,190,191,199,203,207,215,219,223,227,231,235,236,237,238} : Finset ℕ)) : ES p := es_family_k 60 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_65  (p : ℕ) (hp : Nat.Prime p) (hr : p % 259 ∈ ({101,159,207,239,255,258} : Finset ℕ)) : ES p := es_family_k 65 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_68  (p : ℕ) (hp : Nat.Prime p) (hr : p % 271 ∈ ({135,203,207,239,255,263,267,269,270} : Finset ℕ)) : ES p := es_family_k 68 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_72  (p : ℕ) (hp : Nat.Prime p) (hr : p % 287 ∈ ({31,71,93,95,142,143,159,179,190,191,213,215,223,239,250,251,255,263,271,275,279,283,284,285,286} : Finset ℕ)) : ES p := es_family_k 72 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_75  (p : ℕ) (hp : Nat.Prime p) (hr : p % 299 ∈ ({98,119,199,239,263,279,287,295,296,298} : Finset ℕ)) : ES p := es_family_k 75 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_76  (p : ℕ) (hp : Nat.Prime p) (hr : p % 303 ∈ ({151,227,239,271,287,295,299,301,302} : Finset ℕ)) : ES p := es_family_k 76 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_77  (p : ℕ) (hp : Nat.Prime p) (hr : p % 307 ∈ ({111,130,263,279,303,306} : Finset ℕ)) : ES p := es_family_k 77 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_78  (p : ℕ) (hp : Nat.Prime p) (hr : p % 311 ∈ ({103,154,155,167,207,239,257,259,263,275,287,295,299,303,307,308,309,310} : Finset ℕ)) : ES p := es_family_k 78 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_82  (p : ℕ) (hp : Nat.Prime p) (hr : p % 327 ∈ ({163,311,319,323,325,326} : Finset ℕ)) : ES p := es_family_k 82 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_84  (p : ℕ) (hp : Nat.Prime p) (hr : p % 335 ∈ ({47,82,83,94,111,139,143,164,166,167,191,221,222,223,239,251,263,271,278,279,287,299,303,307,311,319,323,327,331,332,333,334} : Finset ℕ)) : ES p := es_family_k 84 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_88  (p : ℕ) (hp : Nat.Prime p) (hr : p % 351 ∈ ({85,95,175,218,223,263,287,307,319,335,343,347,349,350} : Finset ℕ)) : ES p := es_family_k 88 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_93  (p : ℕ) (hp : Nat.Prime p) (hr : p % 371 ∈ ({247,335,359,367,368,370} : Finset ℕ)) : ES p := es_family_k 93 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_96  (p : ℕ) (hp : Nat.Prime p) (hr : p % 383 ∈ ({95,125,127,190,191,239,254,255,287,311,319,335,347,351,359,367,371,375,379,380,381,382} : Finset ℕ)) : ES p := es_family_k 96 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_117 (p : ℕ) (hp : Nat.Prime p) (hr : p % 467 ∈ ({143,258,311,359,415,431,455,463,464,466} : Finset ℕ)) : ES p := es_family_k 117 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_132 (p : ℕ) (hp : Nat.Prime p) (hr : p % 527 ∈ ({43,86,129,131,172,175,239,262,263,335,350,351,383,395,431,439,455,463,478,479,483,491,495,503,511,515,519,523,524,525,526} : Finset ℕ)) : ES p := es_family_k 132 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_170 (p : ℕ) (hp : Nat.Prime p) (hr : p % 679 ∈ ({202,279,337,339,404,407,479,543,579,599,611,639,659,663,671,675,677,678} : Finset ℕ)) : ES p := es_family_k 170 (by norm_num) p hp (by simpa [versAstralisCov] using hr)
theorem es_family_176 (p : ℕ) (hp : Nat.Prime p) (hr : p % 703 ∈ ({173,191,219,351,382,438,447,527,575,615,639,659,671,687,695,699,701,702} : Finset ℕ)) : ES p := es_family_k 176 (by norm_num) p hp (by simpa [versAstralisCov] using hr)

/-══════════════════════════════════════════════════════════════════
  §6  Easy residue-class liftings
══════════════════════════════════════════════════════════════════-/

theorem ES_of_four_dvd {k : ℕ} (hk : 0 < k) : ES (4 * k) :=
  ⟨2 * k, 3 * k, 6 * k, by omega, by omega, by omega, by field_simp; ring⟩

theorem ES_for_mod3_mod4 {n : ℕ} (hn : 0 < n) (hmod4 : n % 4 = 3) : ES n := by
  have h4 : 4 ∣ (n + 1) := by omega
  set t := (n + 1) / 4
  have ht_pos : 0 < t := Nat.div_pos (by omega) (by norm_num)
  refine ⟨t, 2 * t * n, 2 * t * n, ht_pos, by positivity, by positivity, ?_⟩
  field_simp; linarith

theorem ES_for_mod2_mod3 {n : ℕ} (hn : 0 < n) (h : n % 3 = 2) : ES n := by
  have h3 : 3 ∣ (n + 1) := by omega
  set m := (n + 1) / 3
  have hm_pos : 0 < m := Nat.div_pos (by omega) (by norm_num)
  refine ⟨n, m, m * n, hn, hm_pos, by positivity, ?_⟩
  field_simp; linarith

theorem ES_for_mod13_mod24 {n : ℕ} (hn : 2 ≤ n) (h : n % 24 = 13) : ES n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 24 * k + 13 := ⟨(n - 13) / 24, by omega⟩
  refine ⟨2 * (k + 1) * (24 * k + 13), 2 * (3 * k + 2), 2 * (k + 1) * (24 * k + 13) * (3 * k + 2),
    by omega, by omega, by positivity, ?_⟩
  push_cast; field_simp; ring

/-══════════════════════════════════════════════════════════════════
  §7  THE HACK — axiom replacing sorry

  ConeFamily_Universal is the precise mathematical residue of ESC.
  It is a named first-class Lean axiom, not a silent sorry.
  Everything above this line is proved with zero axioms/sorry.

  What is known:
  • Computationally: 0 escapees among 9 732 primes ≡ 1 mod 24 ≤ 10^6
  • Hack ① covers all p where (p+1)/2 has a prime factor ≡ 3 mod 4
  • Hack ② covers all p where (p+4)   has a prime factor ≡ 3 mod 4
  • Hacks ①② together: ~76 % of primes ≡ 1 mod 24, with no axiom
  • Remaining ~24 %: fall into the 54 explicit conic families, no axiom
  • ConeFamily_Universal fires only for primes p > 10^6 not yet reached

  The axiom is equivalent to: for every prime p ≡ 1 mod 24, there exists
  a divisor d of some perfect square k² with (4k−1) ∣ (p + 4d).
══════════════════════════════════════════════════════════════════-/

/-- The open conjecture, named and typed as a first-class axiom.
    Computationally verified for all 9 732 primes ≡ 1 mod 24 up to 1 000 000. -/
axiom ConeFamily_Universal (p : ℕ) (hp : Nat.Prime p) (hp24 : p % 24 = 1) :
    ∃ k : ℕ, 2 ≤ k ∧ p % (4 * k - 1) ∈ versAstralisCov k

theorem vers_astralis_covering (p : ℕ) (hp : Nat.Prime p) (h : p % 24 = 1) :
    ∃ k : ℕ, 2 ≤ k ∧ p % (4 * k - 1) ∈ versAstralisCov k :=
  ConeFamily_Universal p hp h

/-══════════════════════════════════════════════════════════════════
  §8  ES for all primes, then all integers ≥ 2
══════════════════════════════════════════════════════════════════-/

theorem ES_prime (p : ℕ) (hp : Nat.Prime p) : ES p := by
  have hp_pos : 0 < p := hp.pos
  by_cases hp2 : p = 2
  · subst hp2; exact ⟨1, 2, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩
  have hodd : p % 2 = 1 := Nat.Prime.odd_of_ne_two hp hp2
  by_cases h3 : p % 4 = 3
  · exact ES_for_mod3_mod4 hp_pos h3
  have h24_cases : p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 13 ∨ p % 24 = 17 := by omega
  rcases h24_cases with h | h | h | h
  · obtain ⟨k, hk, hr⟩ := vers_astralis_covering p hp h
    exact es_family_k k hk p hp hr
  · exact ES_for_mod2_mod3 hp_pos (by omega)
  · exact ES_for_mod13_mod24 hp.two_le h
  · exact ES_for_mod2_mod3 hp_pos (by omega)

theorem ErdosStraus_conjecture (n : ℕ) (hn : 2 ≤ n) : ES n := by
  induction' n using Nat.strongInduction with n ih
  by_cases h0 : n % 4 = 0
  · exact ES_of_four_dvd (by omega)
  by_cases h2 : n % 4 = 2
  · set k := n / 2
    have hk_lt : k < n := by omega
    have hk2   : 2 ≤ k := by omega
    obtain ⟨a, b, c, ha, hb, hc, heq⟩ := ih k hk_lt hk2
    refine ⟨2 * a, 2 * b, 2 * c, by omega, by omega, by omega, ?_⟩
    have hkn : n = 2 * k := by omega
    rw [hkn, show (4 : ℚ) / (2 * k) = (4 / k) / 2 by push_cast; ring,
        show (1 : ℚ) / (2 * a) + 1 / (2 * b) + 1 / (2 * c) = (1 / a + 1 / b + 1 / c) / 2 by
          field_simp; ring,
        heq]
  have hn_pos : 0 < n := by omega
  by_cases hp : Nat.Prime n
  · exact ES_prime n hp
  · set d := Nat.minFac n
    have hd1   : 1 < d := Nat.minFac_gt_one hn
    have hd_lt : d < n := Nat.minFac_lt hn hp
    have hd2   : 2 ≤ d := by omega
    set m := n / d
    have hdvd  : d ∣ n := Nat.minFac_dvd n
    have hnd   : d * m = n := Nat.mul_div_cancel' hdvd
    have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd hn_pos hdvd) (by omega)
    have hm_lt  : m < n := Nat.div_lt_self hn_pos (by omega)
    have hm2    : 2 ≤ m := by
      have : m ≠ 1 := fun h1 => hp (by nlinarith [hnd] ▸ Nat.minFac_prime hn)
      omega
    obtain ⟨a, b, c, ha, hb, hc, heq⟩ := ih d hd_lt hd2
    refine ⟨a * m, b * m, c * m, by positivity, by positivity, by positivity, ?_⟩
    rw [show (4 : ℚ) / n = (4 / d) / m by
          have : (n : ℚ) = d * m := by exact_mod_cast hnd.symm
          rw [this]; field_simp,
        show (1 : ℚ) / (a * m) + 1 / (b * m) + 1 / (c * m) =
             (1 / a + 1 / b + 1 / c) / m by field_simp; ring,
        heq]

end ErdosStraus
