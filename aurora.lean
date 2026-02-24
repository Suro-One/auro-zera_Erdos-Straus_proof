import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Omega
import Mathlib.Tactic.Nlinarith

-- Core definitions (minimal)
def SolvesES (n x y z : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ 0 < z ∧
  (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

def ErdosStraus (n : ℕ) : Prop :=
  ∃ x y z : ℕ, SolvesES n x y z

-- The Kernel: Mordell residues (squares mod 840 that resist polynomial identities)
def IsMordellResidue (r : ℕ) : Prop :=
  r = 1 ∨ r = 121 ∨ r = 169 ∨ r = 289 ∨ r = 361 ∨ r = 529

-- The single key theorem: full equivalence
-- (Your framework proves all other cases via families, multiplication, induction;
--  this states the whole conjecture ⇔ it holds on these kernel primes >3)
theorem ES_equiv_kernel :
  (∀ n ≥ 2, ErdosStraus n) ↔
  (∀ p, Nat.Prime p → 3 < p → IsMordellResidue (p % 840) → ErdosStraus p) := by
  -- ⇒ direction: if full conjecture true, then obviously true on subset
  constructor
  · intro hfull p hp hp3 _
    exact hfull p (by omega)
  · -- ⇐ direction: assume kernel holds → prove for all n ≥ 2
    intro hkernel n hn
    induction n using Nat.strongRecOn with
    | _ n ih =>
      interval_cases n <;> [exact ⟨1,4,4,by norm_num⟩; exact ⟨1,4,6,by norm_num⟩]
      by_cases hprime : Nat.Prime n
      · exact es_prime_reduction n hprime (by omega) (hkernel n hprime (by omega))
      · -- composite case: reduce via a prime factor (your es_of_prime_factor logic)
        have h1 : 1 < n := by omega
        obtain ⟨q, hq, hdvd⟩ := Nat.exists_prime_and_dvd h1
        have hq_lt : q < n := Nat.lt_of_le_of_ne (Nat.le_of_dvd (by omega) hdvd)
          (by intro; apply hprime; simpa using hq)
        obtain ⟨m, rfl⟩ := hdvd
        have hq_two_le : 2 ≤ q := Nat.Prime.two_le hq
        have hm_one_le : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr
          (by intro h; simp [h] at hn)
        exact es_mul_right q m hq_two_le hm_one_le (ih q hq_lt hq_two_le)
