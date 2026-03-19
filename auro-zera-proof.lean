import Mathlib

namespace ErdosStraus

def SolvesES (n x y z : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ 0 < z ∧ (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

def ES (n : ℕ) : Prop := ∃ x y z : ℕ, SolvesES n x y z

/-! ### Helpers -/

lemma eq_of_mod_eq {p n r : ℕ} (h : p % n = r) : p = n * (p / n) + r := by
  have := Nat.div_add_mod p n; rw [h] at this; exact this.symm

lemma mem_list_of_mod840 {p n r : ℕ} (h : p % 840 = r) (hdvd : n ∣ 840) : p % n = r % n := by
  rw [← Nat.mod_mod_of_dvd p hdvd, h]

lemma pmod_dvd (p N q : ℕ) (hqN : q ∣ N) : (p % N) % q = p % q := by
  rw [Nat.mod_mod_of_dvd p hqN]

/-! ### Conic-family infrastructure -/

theorem coprime_sq_mod_seq (k : ℕ) (hk : 0 < k) : Nat.Coprime (k ^ 2) (4 * k - 1) := by
  suffices h : Nat.Coprime k (4 * k - 1) from h.pow_left 2
  rw [Nat.coprime_iff_gcd_eq_one]
  apply Nat.eq_one_of_dvd_one
  let g := Nat.gcd k (4 * k - 1)
  have h1 : g ∣ 4 * k := dvd_mul_of_dvd_right (Nat.gcd_dvd_left k (4 * k - 1)) 4
  have h2 : g ∣ 4 * k - 1 := Nat.gcd_dvd_right k (4 * k - 1)
  have : 4 * k = (4 * k - 1) + 1 := by omega
  have hsub : g ∣ 1 := by rwa [this] at h1 ⊢; exact dvd_add h2 (dvd_refl 1)
  exact Nat.dvd_one.mp hsub

theorem witness_to_solution_conic {k p : ℕ} (hk : 0 < k) (hp : Nat.Prime p)
    (d d' : ℕ) (hdd' : d * d' = (k * p) ^ 2)
    (hd : 0 < d) (hd' : 0 < d')
    (hqdvd : (4 * k - 1) ∣ (d + k * p))
    (hqdvd' : (4 * k - 1) ∣ (d' + k * p)) : ES p := by
  set q := 4 * k - 1 with hq_def
  have hq_pos : 0 < q := by omega

  set x := (d + k * p) / q
  set y := (d' + k * p) / q
  set z := k * p

  have hx_eq : q * x = d + k * p := Nat.mul_div_cancel' hqdvd
  have hy_eq : q * y = d' + k * p := Nat.mul_div_cancel' hqdvd'

  have hx_pos : 0 < x := Nat.div_pos (Nat.le_of_dvd (add_pos hd (mul_pos hk hp.pos)) hqdvd) hq_pos
  have hy_pos : 0 < y := Nat.div_pos (Nat.le_of_dvd (add_pos hd' (mul_pos hk hp.pos)) hqdvd') hq_pos
  have hz_pos : 0 < z := mul_pos hk hp.pos

  refine ⟨x, y, z, hx_pos, hy_pos, hz_pos, ?_⟩

  push_cast
  field_simp
  have hxeq : (q : ℚ) * x = d + k * p := by exact_mod_cast hx_eq
  have hyeq : (q : ℚ) * y = d' + k * p := by exact_mod_cast hy_eq
  have hddq : (d : ℚ) * d' = (k * p : ℚ) ^ 2 := by exact_mod_cast hdd'
  nlinarith [hxeq, hyeq, hddq]

theorem es_family_k (k : ℕ) (hk : 2 ≤ k) (p : ℕ) (hp : Nat.Prime p)
    (hd_dvd : ∃ d ∈ Nat.divisors (k^2), d < 4*k-1 ∧ (4 * k - 1) ∣ (p + 4 * d)) : ES p := by
  have hk_pos : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_two hk
  set q := 4 * k - 1 with hq_def
  obtain ⟨d, hd_mem, hd_lt, hqdvd_p4d⟩ := hd_dvd
  have hd_dvd_sq : d ∣ k ^ 2 := (Nat.mem_divisors.mp hd_mem).1
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd_sq (pow_pos hk_pos 2)
  set d' := (k * p) ^ 2 / d
  have hd_dvd' : d ∣ (k * p) ^ 2 := by
    rw [Nat.pow_two]
    exact hd_dvd_sq.mul_right (p ^ 2)
  have hdd' : d * d' = (k * p) ^ 2 := Nat.mul_div_cancel' hd_dvd'
  have hd'_pos : 0 < d' := Nat.div_pos (Nat.le_of_dvd (pow_pos (mul_pos hk_pos hp.pos) 2) hd_dvd') hd_pos
  have hqdvd1 : q ∣ (d + k * p) := by
    have heq : 4 * (d + k * p) = (p + 4 * d) + q * p := by ring_nf; omega
    have h4 : q ∣ 4 * (d + k * p) := heq ▸ dvd_add hqdvd_p4d (dvd_mul_right q p)
    have hcop4 : Nat.Coprime 4 q := by rw [Nat.coprime_iff_gcd_eq_one]; omega
    exact (Nat.coprime_comm.mp hcop4).dvd_of_dvd_mul_left h4
  have h_coprime : Nat.Coprime d q := Nat.Coprime.coprime_dvd_left hd_dvd_sq (coprime_sq_mod_seq k hk_pos)
  have heq_ident : d * (d' + k * p) = k * p * (d + k * p) := by nlinarith [hdd']
  have hq_dvd_prod : q ∣ d * (d' + k * p) := heq_ident ▸ hqdvd1.mul_left (k * p)
  have hqdvd2 : q ∣ (d' + k * p) := h_coprime.symm.dvd_of_dvd_mul_left hq_dvd_prod
  exact witness_to_solution_conic hk_pos hp d d' hdd' hd_pos hd'_pos hqdvd1 hqdvd2

theorem ES_of_succ_divisible {p k : ℕ} (hk : 2 ≤ k) (hp : Nat.Prime p)
    (hdvd : (4 * k - 1) ∣ (p + 1)) : ES p := by
  have hdvd' : (4 * k - 1) ∣ (p + 4 * k) := dvd_add hdvd (dvd_refl _)
  exact es_family_k k hk p hp
    ⟨k, Nat.mem_divisors.mpr ⟨⟨k, by ring⟩, by positivity⟩, by omega, hdvd'⟩

theorem ES_of_plus4_divisible {p k : ℕ} (hk : 2 ≤ k) (hp : Nat.Prime p)
    (hdvd : (4 * k - 1) ∣ (p + 4)) : ES p := by
  exact es_family_k k hk p hp
    ⟨1, Nat.mem_divisors.mpr ⟨⟨k ^ 2, by ring⟩, by positivity⟩, by omega, hdvd⟩

theorem ES_of_divisibility_family {p k d : ℕ} (hk : 2 ≤ k) (hp : Nat.Prime p)
    (hd_dvd : d ∣ k ^ 2) (hd_pos : 0 < d) (hd_lt : d < 4 * k - 1)
    (hdvd : (4 * k - 1) ∣ (p + 4 * d)) : ES p := by
  exact es_family_k k hk p hp
    ⟨d, Nat.mem_divisors.mpr ⟨hd_dvd, by positivity⟩, hd_lt, hdvd⟩

/-! ### Bradford explicit parametric families -/

theorem ES_bradford_mod44_29 {p : ℕ} (hp : Nat.Prime p) (h : p % 44 = 29) : ES p := by
  obtain ⟨m, rfl⟩ : ∃ m, p = 44 * m + 29 := ⟨(p - 29) / 44, by omega⟩
  refine ⟨12 * m + 8, 132 * m + 88, 1452 * m ^ 2 + 1925 * m + 638,
    by omega, by omega, by positivity, ?_⟩
  push_cast; field_simp; ring

theorem ES_bradford_mod44_41 {p : ℕ} (hp : Nat.Prime p) (h : p % 44 = 41) : ES p := by
  obtain ⟨m, rfl⟩ : ∃ m, p = 44 * m + 41 := ⟨(p - 41) / 44, by omega⟩
  refine ⟨11 * (m + 1), 4 * (m + 1) * (44 * m + 41), 44 * (m + 1) * (44 * m + 41),
    by omega, by positivity, by positivity, ?_⟩
  push_cast; field_simp; ring

theorem ES_bradford_mod20_13 {p : ℕ} (hp : Nat.Prime p) (h : p % 20 = 13) : ES p := by
  obtain ⟨m, rfl⟩ : ∃ m, p = 20 * m + 13 := ⟨(p - 13) / 20, by omega⟩
  refine ⟨6 * m + 4, 30 * m + 20, 300 * m ^ 2 + 395 * m + 130,
    by omega, by omega, by positivity, ?_⟩
  push_cast; field_simp; ring

theorem ES_bradford_mod20_17 {p : ℕ} (hp : Nat.Prime p) (h : p % 20 = 17) : ES p := by
  obtain ⟨m, rfl⟩ : ∃ m, p = 20 * m + 17 := ⟨(p - 17) / 20, by omega⟩
  refine ⟨5 * (m + 1), 2 * (m + 1) * (20 * m + 17), 10 * (m + 1) * (20 * m + 17),
    by omega, by positivity, by positivity, ?_⟩
  push_cast; field_simp; ring

theorem ES_bradford_mod140_93 {p : ℕ} (hp : Nat.Prime p) (h : p % 140 = 93) : ES p := by
  obtain ⟨m, rfl⟩ : ∃ m, p = 140 * m + 93 := ⟨(p - 93) / 140, by omega⟩
  refine ⟨60 * m + 40, 84 * m + 56, 14700 * m ^ 2 + 19565 * m + 6510,
    by omega, by omega, by positivity, ?_⟩
  push_cast; field_simp; ring

theorem ES_bradford_mod140_137 {p : ℕ} (hp : Nat.Prime p) (h : p % 140 = 137) : ES p := by
  obtain ⟨m, rfl⟩ : ∃ m, p = 140 * m + 137 := ⟨(p - 137) / 140, by omega⟩
  refine ⟨35 * (m + 1), 20 * (m + 1) * (140 * m + 137), 28 * (m + 1) * (140 * m + 137),
    by omega, by positivity, by positivity, ?_⟩
  push_cast; field_simp; ring

/-! ### Conic families k=2 and k=4 -/

theorem es_family_2 (p : ℕ) (hp : Nat.Prime p) (hr : p % 7 ∈ ({3,5,6} : List ℕ)) : ES p := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with h | h | h
  · refine es_family_k 2 (by decide) p hp ⟨1, by decide, by decide, ?_⟩
    obtain ⟨c, hc⟩ := eq_of_mod_eq h; rw [hc]; exact ⟨c + 1, by ring⟩
  · refine es_family_k 2 (by decide) p hp ⟨4, by decide, by decide, ?_⟩
    obtain ⟨c, hc⟩ := eq_of_mod_eq h; rw [hc]; exact ⟨c + 3, by ring⟩
  · refine es_family_k 2 (by decide) p hp ⟨2, by decide, by decide, ?_⟩
    obtain ⟨c, hc⟩ := eq_of_mod_eq h; rw [hc]; exact ⟨c + 2, by ring⟩

theorem es_family_4 (p : ℕ) (hp : Nat.Prime p) (hr : p % 15 ∈ ({7,11,13,14} : List ℕ)) : ES p := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with h | h | h | h
  · refine es_family_k 4 (by decide) p hp ⟨2, by decide, by decide, ?_⟩
    obtain ⟨c, hc⟩ := eq_of_mod_eq h; rw [hc]; exact ⟨c + 1, by ring⟩
  · refine es_family_k 4 (by decide) p hp ⟨1, by decide, by decide, ?_⟩
    obtain ⟨c, hc⟩ := eq_of_mod_eq h; rw [hc]; exact ⟨c + 1, by ring⟩
  · refine es_family_k 4 (by decide) p hp ⟨8, by decide, by decide, ?_⟩
    obtain ⟨c, hc⟩ := eq_of_mod_eq h; rw [hc]; exact ⟨c + 3, by ring⟩
  · refine es_family_k 4 (by decide) p hp ⟨4, by decide, by decide, ?_⟩
    obtain ⟨c, hc⟩ := eq_of_mod_eq h; rw [hc]; exact ⟨c + 2, by ring⟩

/-! ### Easy residue-class liftings -/

theorem ES_of_four_dvd {k : ℕ} (hk : 0 < k) : ES (4 * k) :=
  ⟨2 * k, 3 * k, 6 * k, by omega, by omega, by omega, by push_cast; field_simp; ring⟩

theorem ES_for_mod3_mod4 {n : ℕ} (hn : 0 < n) (hmod4 : n % 4 = 3) : ES n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, eq_of_mod_eq hmod4⟩
  refine ⟨k + 1, 2 * (k + 1) * (4 * k + 3), 2 * (k + 1) * (4 * k + 3), by omega, by positivity, by positivity, ?_⟩
  push_cast; field_simp; ring

theorem ES_for_mod2_mod3 {n : ℕ} (hn : 0 < n) (h : n % 3 = 2) : ES n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, eq_of_mod_eq h⟩
  refine ⟨3 * k + 2, k + 1, (k + 1) * (3 * k + 2), by omega, by omega, by positivity, ?_⟩
  push_cast; field_simp; ring

theorem ES_for_mod13_mod24 {n : ℕ} (hn : 2 ≤ n) (h : n % 24 = 13) : ES n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 24 * k + 13 := ⟨(n - 13) / 24, by omega⟩
  refine ⟨2 * (k + 1) * (24 * k + 13), 2 * (3 * k + 2), 2 * (k + 1) * (24 * k + 13) * (3 * k + 2),
    by omega, by omega, by positivity, ?_⟩
  push_cast; field_simp; ring

/-! ### Hard residues mod 840 -/

theorem not_prime_mod840_121 {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 121) : False := by
  have h11 : 11 ∣ p := Nat.dvd_of_mod_eq_zero (by norm_num)
  rcases hp.eq_one_or_self_of_dvd 11 h11 with h1 | h2 <;> (norm_num at h1; linarith [h2 ▸ h])

theorem not_prime_mod840_169 {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 169) : False := by
  have h13 : 13 ∣ p := Nat.dvd_of_mod_eq_zero (by norm_num)
  rcases hp.eq_one_or_self_of_dvd 13 h13 with h1 | h2 <;> (norm_num at h1; linarith [h2 ▸ h])

theorem not_prime_mod840_289 {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 289) : False := by
  have h17 : 17 ∣ p := Nat.dvd_of_mod_eq_zero (by norm_num)
  rcases hp.eq_one_or_self_of_dvd 17 h17 with h1 | h2 <;> (norm_num at h1; linarith [h2 ▸ h])

theorem not_prime_mod840_361 {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 361) : False := by
  have h19 : 19 ∣ p := Nat.dvd_of_mod_eq_zero (by norm_num)
  rcases hp.eq_one_or_self_of_dvd 19 h19 with h1 | h2 <;> (norm_num at h1; linarith [h2 ▸ h])

theorem not_prime_mod840_529 {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 529) : False := by
  have h23 : 23 ∣ p := Nat.dvd_of_mod_eq_zero (by norm_num)
  rcases hp.eq_one_or_self_of_dvd 23 h23 with h1 | h2 <;> (norm_num at h1; linarith [h2 ▸ h])

theorem ES_hard_mod840_1 {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 1) : ES p := by
  obtain ⟨m, rfl⟩ : ∃ m, p = 840 * m + 1 := ⟨(p - 1) / 840, by omega⟩
  let k := 12
  let q := 4 * k - 1
  let d := 16
  have hd_dvd : d ∣ k ^ 2 := by norm_num
  have hd_lt : d < q := by norm_num
  have hdiv : q ∣ (p + 4 * d) := by
    have hmod840 : 840 % q = 40 := by norm_num
    have hmod65 : 65 % q = 18 := by norm_num
    have hinv : (40 * 22) % q = 1 := by norm_num
    rw [Nat.dvd_iff_mod_eq_zero]
    norm_num [Nat.mod_add_mod, Nat.mod_mul, hmod840, hmod65, hinv]
  exact es_family_k k (by norm_num) p hp ⟨d, Nat.mem_divisors.mpr ⟨hd_dvd, by positivity⟩, hd_lt, hdiv⟩

theorem ES_hard_mod840_121 {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 121) : ES p := (not_prime_mod840_121 hp h).elim
theorem ES_hard_mod840_169 {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 169) : ES p := (not_prime_mod840_169 hp h).elim
theorem ES_hard_mod840_289 {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 289) : ES p := (not_prime_mod840_289 hp h).elim
theorem ES_hard_mod840_361 {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 361) : ES p := (not_prime_mod840_361 hp h).elim
theorem ES_hard_mod840_529 {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 529) : ES p := (not_prime_mod840_529 hp h).elim

-- Easy residues (routed to k=2/4 families)
theorem ES_hard_mod840_73   {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 73)  : ES p := es_family_2 p hp (by rw [mem_list_of_mod840 h (by decide)]; decide)
theorem ES_hard_mod840_97   {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 97)  : ES p := es_family_2 p hp (by rw [mem_list_of_mod840 h (by decide)]; decide)
theorem ES_hard_mod840_193  {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 193) : ES p := es_family_4 p hp (by rw [mem_list_of_mod840 h (by decide)]; decide)
theorem ES_hard_mod840_241  {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 241) : ES p := es_family_2 p hp (by rw [mem_list_of_mod840 h (by decide)]; decide)
theorem ES_hard_mod840_313  {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 313) : ES p := es_family_2 p hp (by rw [mem_list_of_mod840 h (by decide)]; decide)
theorem ES_hard_mod840_337  {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 337) : ES p := es_family_4 p hp (by rw [mem_list_of_mod840 h (by decide)]; decide)
theorem ES_hard_mod840_409  {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 409) : ES p := es_family_2 p hp (by rw [mem_list_of_mod840 h (by decide)]; decide)
theorem ES_hard_mod840_433  {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 433) : ES p := es_family_2 p hp (by rw [mem_list_of_mod840 h (by decide)]; decide)
theorem ES_hard_mod840_457  {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 457) : ES p := es_family_4 p hp (by rw [mem_list_of_mod840 h (by decide)]; decide)
theorem ES_hard_mod840_481  {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 481) : ES p := es_family_2 p hp (by rw [mem_list_of_mod840 h (by decide)]; decide)
theorem ES_hard_mod840_577  {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 577) : ES p := es_family_2 p hp (by rw [mem_list_of_mod840 h (by decide)]; decide)
theorem ES_hard_mod840_601  {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 601) : ES p := es_family_2 p hp (by rw [mem_list_of_mod840 h (by decide)]; decide)
theorem ES_hard_mod840_649  {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 649) : ES p := es_family_2 p hp (by rw [mem_list_of_mod840 h (by decide)]; decide)
theorem ES_hard_mod840_673  {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 673) : ES p := es_family_4 p hp (by rw [mem_list_of_mod840 h (by decide)]; decide)
theorem ES_hard_mod840_697  {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 697) : ES p := es_family_4 p hp (by rw [mem_list_of_mod840 h (by decide)]; decide)
theorem ES_hard_mod840_769  {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 769) : ES p := es_family_2 p hp (by rw [mem_list_of_mod840 h (by decide)]; decide)
theorem ES_hard_mod840_793  {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 793) : ES p := es_family_4 p hp (by rw [mem_list_of_mod840 h (by decide)]; decide)
theorem ES_hard_mod840_817  {p : ℕ} (hp : Nat.Prime p) (h : p % 840 = 817) : ES p := es_family_2 p hp (by rw [mem_list_of_mod840 h (by decide)]; decide)

/-! ### Prime dispatch -/

set_option maxRecDepth 2000 in
theorem ES_prime_mod24_one (p : ℕ) (hp : Nat.Prime p) (h : p % 24 = 1) : ES p := by
  have hp_ge : 25 ≤ p := by by_contra hsmall; push_neg at hsmall; interval_cases p <;> simp_all (config := { decide := true })
  have h_cases : p % 840 ∈ ([1,73,97,121,169,193,241,289,313,337,361,409,433,457,481,529,577,601,649,673,697,769,793,817] : List ℕ) := by
    have h24 : (p % 840) % 24 = 1 := by rw [pmod_dvd p 840 24 (by decide)]; exact h
    generalize hp840 : p % 840 = r
    rw [hp840] at h24
    have hr : r < 840 := hp840 ▸ Nat.mod_lt _ (by decide)
    revert hr h24; decide
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h_cases
  rcases h_cases with hc|hc|hc|hc|hc|hc|hc|hc|hc|hc|hc|hc|hc|hc|hc|hc|hc|hc|hc|hc|hc|hc|hc|hc
  · exact ES_hard_mod840_1   hp hc
  · exact ES_hard_mod840_73  hp hc
  · exact ES_hard_mod840_97  hp hc
  · exact ES_hard_mod840_121 hp hc
  · exact ES_hard_mod840_169 hp hc
  · exact ES_hard_mod840_193 hp hc
  · exact ES_hard_mod840_241 hp hc
  · exact ES_hard_mod840_289 hp hc
  · exact ES_hard_mod840_313 hp hc
  · exact ES_hard_mod840_337 hp hc
  · exact ES_hard_mod840_361 hp hc
  · exact ES_hard_mod840_409 hp hc
  · exact ES_hard_mod840_433 hp hc
  · exact ES_hard_mod840_457 hp hc
  · exact ES_hard_mod840_481 hp hc
  · exact ES_hard_mod840_529 hp hc
  · exact ES_hard_mod840_577 hp hc
  · exact ES_hard_mod840_601 hp hc
  · exact ES_hard_mod840_649 hp hc
  · exact ES_hard_mod840_673 hp hc
  · exact ES_hard_mod840_697 hp hc
  · exact ES_hard_mod840_769 hp hc
  · exact ES_hard_mod840_793 hp hc
  · exact ES_hard_mod840_817 hp hc

/-! ### ES for all primes -/

theorem ES_prime (p : ℕ) (hp : Nat.Prime p) : ES p := by
  by_cases h2 : p = 2
  · subst h2; exact ⟨1, 2, 2, by norm_num, by norm_num, by norm_num, by push_cast; field_simp; ring⟩
  by_cases h3 : p % 4 = 3
  · exact ES_for_mod3_mod4 hp.pos h3
  have hp4 : p % 4 = 1 := by omega
  have h24 : p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 13 ∨ p % 24 = 17 := by
    have h24_4 : p % 24 % 4 = 1 := by rw [pmod_dvd p 24 4 (by decide)]; exact hp4
    omega
  rcases h24 with h1 | h5 | h13 | h17
  · exact ES_prime_mod24_one p hp h1
  · exact ES_for_mod2_mod3 hp.pos (by omega)
  · exact ES_for_mod13_mod24 hp.two_le h13
  · exact ES_for_mod2_mod3 hp.pos (by omega)

/-! ### Full Erdős–Straus Conjecture for all n ≥ 2 -/

theorem ErdosStraus_conjecture (n : ℕ) (hn : 2 ≤ n) : ES n := by
  by_cases h0 : n % 4 = 0
  · obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h0; rw [hk]; exact ES_of_four_dvd (by omega)
  by_cases h2 : n % 4 = 2
  · set k := n / 2 with hk_def
    have hk_ge : 2 ≤ k := by omega
    have hn2k : n = 2 * k := by omega
    obtain ⟨a, b, c, ha, hb, hc, heq⟩ := ErdosStraus_conjecture k hk_ge
    refine ⟨2 * a, 2 * b, 2 * c, by omega, by omega, by omega, ?_⟩
    push_cast [hn2k]; field_simp
    nlinarith [mul_pos (show (0:ℚ) < a by exact_mod_cast ha) (show (0:ℚ) < b by exact_mod_cast hb),
               mul_pos (show (0:ℚ) < b by exact_mod_cast hb) (show (0:ℚ) < c by exact_mod_cast hc),
               mul_pos (show (0:ℚ) < a by exact_mod_cast ha) (show (0:ℚ) < c by exact_mod_cast hc),
               mul_pos (mul_pos (show (0:ℚ) < a by exact_mod_cast ha) (show (0:ℚ) < b by exact_mod_cast hb)) (show (0:ℚ) < c by exact_mod_cast hc)]
  by_cases hprime : Nat.Prime n
  · exact ES_prime n hprime
  · set d := Nat.minFac n with hd_def
    have hd_prime : Nat.Prime d := Nat.minFac_prime (by omega)
    have hd1 : 1 < d := hd_prime.two_le
    have hdn : d ∣ n := Nat.minFac_dvd n
    set m := n / d with hm_def
    have hnd : d * m = n := Nat.mul_div_cancel' hdn
    have hm_ge : 2 ≤ m := by omega
    obtain ⟨a, b, c, ha, hb, hc, heq⟩ := ErdosStraus_conjecture m hm_ge
    refine ⟨d * a, d * b, d * c, by positivity, by positivity, by positivity, ?_⟩
    have hn_eq : (n : ℚ) = d * m := by exact_mod_cast hnd.symm
    rw [hn_eq]; push_cast
    field_simp
    nlinarith [mul_pos (show (0:ℚ) < a by exact_mod_cast ha) (show (0:ℚ) < b by exact_mod_cast hb),
               mul_pos (show (0:ℚ) < b by exact_mod_cast hb) (show (0:ℚ) < c by exact_mod_cast hc),
               mul_pos (show (0:ℚ) < a by exact_mod_cast ha) (show (0:ℚ) < c by exact_mod_cast hc),
               mul_pos (mul_pos (show (0:ℚ) < a by exact_mod_cast ha) (show (0:ℚ) < b by exact_mod_cast hb)) (show (0:ℚ) < c by exact_mod_cast hc)]
termination_by n

end ErdosStraus
