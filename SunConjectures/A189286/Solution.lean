/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Varun-Dudipala.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib

/-!
# OEIS A189286, Sun's conjecture on divisibility by 8

For every $n \ge 1$, $a(n)$ is an integer divisible by $8$, and $a(n)/8$ is odd if and only if
$n$ is a power of two (Zhi-Wei Sun, 2011). The proof shows $v_2(a(n)) = s_2(n) + s_2(3n)$.

Steps: termwise divisibility of the numerator sum by the denominator; a three-term recurrence
for the numerator sum by telescoping; induction on the $2$-adic valuation. A prose account is
in `README.md` in this directory.
-/

@[expose] public section

namespace OeisA189286

/-- The term $\binom{6k}{3k}\binom{3k}{k}$ appearing in the sum. -/
def tTerm (k : ℕ) : ℚ := ((6 * k).choose (3 * k) * (3 * k).choose k : ℕ)

/--
The sequence $a(n)$ given by
$\frac{\sum_{k=0}^n \binom{6k}{3k}\binom{3k}{k}
  \binom{6(n-k)}{3(n-k)}\binom{3(n-k)}{n-k}}{(2n-1)\binom{3n}{n}}$.
-/
def a (n : ℕ) : ℚ :=
  (∑ k ∈ Finset.range (n + 1), tTerm k * tTerm (n - k)) /
    (((2 * (n : ℚ)) - 1) * ((3 * n).choose n : ℚ))

end OeisA189286

namespace Solutions.OeisA189286

open scoped BigOperators
open _root_.OeisA189286

/- Part 1: Natural numerator/denominator definitions and factorial identities -/

def TNat (k : ℕ) : ℕ := (6 * k).choose (3 * k) * (3 * k).choose k

def numNat (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), TNat k * TNat (n - k)

def denNat (n : ℕ) : ℕ := (2 * n - 1) * (3 * n).choose n

lemma TNat_pos (k : ℕ) : 0 < TNat k := by
  unfold TNat
  exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))

lemma numNat_pos (n : ℕ) : 0 < numNat n := by
  unfold numNat
  rw [Finset.sum_range_succ, Nat.sub_self]
  exact Nat.add_pos_right _ (Nat.mul_pos (TNat_pos n) (TNat_pos 0))

lemma denNat_pos {n : ℕ} (hn : 0 < n) : 0 < denNat n := by
  unfold denNat
  exact Nat.mul_pos (by omega) (Nat.choose_pos (by omega))

lemma TNat_mul_factorials (k : ℕ) :
    TNat k * (3 * k).factorial * k.factorial * (2 * k).factorial = (6 * k).factorial := by
  unfold TNat
  have h1 : (6 * k).choose (3 * k) * (3 * k).factorial * (3 * k).factorial = (6 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show 3 * k ≤ 6 * k by omega)
    simpa [show 6 * k - 3 * k = 3 * k by omega] using this
  have h2 : (3 * k).choose k * k.factorial * (2 * k).factorial = (3 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show k ≤ 3 * k by omega)
    simpa [show 3 * k - k = 2 * k by omega] using this
  calc
    (6 * k).choose (3 * k) * (3 * k).choose k * (3 * k).factorial * k.factorial * (2 * k).factorial
        = (6 * k).choose (3 * k) * (3 * k).factorial *
            ((3 * k).choose k * k.factorial * (2 * k).factorial) := by ring
    _ = (6 * k).choose (3 * k) * (3 * k).factorial * (3 * k).factorial := by rw [h2]
    _ = (6 * k).factorial := h1

lemma two_mul_sub_one_dvd_centralBinom {n : ℕ} (hn : 0 < n) :
    (2 * n - 1) ∣ (2 * n).choose n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h1 : (m + 1) * (2 * m).choose (m + 1) = m * (2 * m).choose m := by
    by_cases hm : m = 0
    · subst hm; simp
    · have hf1 := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
      have hf2 := Nat.choose_mul_factorial_mul_factorial (show m + 1 ≤ 2 * m by omega)
      have hsub1 : 2 * m - m = m := by omega
      have hsub2 : 2 * m - (m + 1) = m - 1 := by omega
      have hmf : m * (m - 1).factorial = m.factorial := Nat.mul_factorial_pred hm
      rw [hsub1] at hf1
      rw [hsub2, Nat.factorial_succ] at hf2
      have hpos : 0 < m.factorial * (m - 1).factorial :=
        Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
      apply Nat.mul_right_cancel hpos
      calc
        (m + 1) * (2 * m).choose (m + 1) * (m.factorial * (m - 1).factorial)
            = (2 * m).choose (m + 1) * ((m + 1) * m.factorial) * (m - 1).factorial := by ring
        _ = (2 * m).factorial := hf2
        _ = (2 * m).choose m * m.factorial * m.factorial := hf1.symm
        _ = (2 * m).choose m * m.factorial * (m * (m - 1).factorial) := by rw [hmf]
        _ = m * (2 * m).choose m * (m.factorial * (m - 1).factorial) := by ring
  have hle : (2 * m).choose (m + 1) ≤ (2 * m).choose m := by
    by_cases hm : m = 0
    · subst hm; simp
    · nlinarith
  have hdiff : (m + 1) * ((2 * m).choose m - (2 * m).choose (m + 1)) = (2 * m).choose m := by
    zify [hle] at h1 ⊢
    linarith
  have hcentral : (m + 1) * (2 * (m + 1)).choose (m + 1) = 2 * (2 * m + 1) * (2 * m).choose m := by
    have hf1 := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
    have hf2 := Nat.choose_mul_factorial_mul_factorial (show m + 1 ≤ 2 * (m + 1) by omega)
    have hsub1 : 2 * m - m = m := by omega
    have hsub2 : 2 * (m + 1) - (m + 1) = m + 1 := by omega
    rw [hsub1] at hf1
    rw [hsub2, show 2 * (m + 1) = 2 * m + 2 by omega, Nat.factorial_succ (2 * m + 1),
      Nat.factorial_succ (2 * m), Nat.factorial_succ m] at hf2
    have hpos : 0 < m.factorial * m.factorial * (m + 1) := by positivity
    apply Nat.mul_right_cancel hpos
    calc
      (m + 1) * (2 * (m + 1)).choose (m + 1) * (m.factorial * m.factorial * (m + 1))
          = (2 * (m + 1)).choose (m + 1) * ((m + 1) * m.factorial) * ((m + 1) * m.factorial) := by
              ring
      _ = (2 * m + 2) * ((2 * m + 1) * (2 * m).factorial) := hf2
      _ = (2 * m + 2) * (2 * m + 1) * ((2 * m).choose m * m.factorial * m.factorial) := by
            rw [hf1]; ring
      _ = 2 * (2 * m + 1) * (2 * m).choose m * (m.factorial * m.factorial * (m + 1)) := by ring
  have hcat : (2 * (m + 1)).choose (m + 1) =
      2 * (2 * m + 1) * ((2 * m).choose m - (2 * m).choose (m + 1)) := by
    apply Nat.mul_left_cancel (show 0 < m + 1 by omega)
    calc
      (m + 1) * (2 * (m + 1)).choose (m + 1) = 2 * (2 * m + 1) * (2 * m).choose m := hcentral
      _ = 2 * (2 * m + 1) * ((m + 1) * ((2 * m).choose m - (2 * m).choose (m + 1))) := by
            rw [hdiff]
      _ = (m + 1) * (2 * (2 * m + 1) * ((2 * m).choose m - (2 * m).choose (m + 1))) := by ring
  rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega, hcat]
  exact ⟨2 * ((2 * m).choose m - (2 * m).choose (m + 1)), by ring⟩

/- Part 2: Termwise integrality (`denNat n ∣ TNat k * TNat (n - k)`) -/

lemma digits_mul_base_sum {p : ℕ} (hp : 2 ≤ p) (m : ℕ) :
    (Nat.digits p (p * m)).sum = (Nat.digits p m).sum := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [Nat.digits_def' hp (by positivity), Nat.mul_div_right m (by omega)]
    simp

lemma padicValNat_three_TNat (k : ℕ) :
    padicValNat 3 (TNat k) = (Nat.digits 3 k).sum := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hf := TNat_mul_factorials k
  have hv : 2 * padicValNat 3 (TNat k * (3 * k).factorial * k.factorial * (2 * k).factorial) =
      2 * padicValNat 3 (6 * k).factorial := congrArg (fun x => 2 * padicValNat 3 x) hf
  have hT0 : TNat k ≠ 0 := Nat.ne_of_gt (TNat_pos k)
  rw [padicValNat.mul (mul_ne_zero (mul_ne_zero hT0 (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _),
    padicValNat.mul (mul_ne_zero hT0 (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _),
    padicValNat.mul hT0 (Nat.factorial_ne_zero _)] at hv
  have l1 := sub_one_mul_padicValNat_factorial (p := 3) (3 * k)
  have l2 := sub_one_mul_padicValNat_factorial (p := 3) k
  have l3 := sub_one_mul_padicValNat_factorial (p := 3) (2 * k)
  have l4 := sub_one_mul_padicValNat_factorial (p := 3) (6 * k)
  simp only [show 3 - 1 = 2 from rfl] at l1 l2 l3 l4
  have d3 : (Nat.digits 3 (3 * k)).sum = (Nat.digits 3 k).sum := digits_mul_base_sum (by omega) k
  have d6 : (Nat.digits 3 (6 * k)).sum = (Nat.digits 3 (2 * k)).sum := by
    rw [show 6 * k = 3 * (2 * k) by omega]
    exact digits_mul_base_sum (by omega) (2 * k)
  have s1 : (Nat.digits 3 k).sum ≤ k := Nat.digit_sum_le 3 k
  have s2 : (Nat.digits 3 (2 * k)).sum ≤ 2 * k := Nat.digit_sum_le 3 (2 * k)
  omega

lemma padicValNat_three_den_le {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    padicValNat 3 (denNat n) ≤ padicValNat 3 (TNat k * TNat (n - k)) := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hdvd : denNat n ∣ (2 * n).choose n * (3 * n).choose n :=
    mul_dvd_mul_right (two_mul_sub_one_dvd_centralBinom hn) _
  have hprod_pos : 0 < (2 * n).choose n * (3 * n).choose n :=
    Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
  have hle1 : padicValNat 3 (denNat n) ≤ padicValNat 3 ((2 * n).choose n * (3 * n).choose n) := by
    rw [← padicValNat_dvd_iff_le (Nat.ne_of_gt hprod_pos)]
    exact dvd_trans pow_padicValNat_dvd hdvd
  have hfact : (2 * n).choose n * (3 * n).choose n * n.factorial * n.factorial * n.factorial =
      (3 * n).factorial := by
    have f1 := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    have f2 := Nat.choose_mul_factorial_mul_factorial (show n ≤ 3 * n by omega)
    rw [show 2 * n - n = n by omega] at f1
    rw [show 3 * n - n = 2 * n by omega] at f2
    calc
      (2 * n).choose n * (3 * n).choose n * n.factorial * n.factorial * n.factorial
          = (3 * n).choose n * n.factorial * ((2 * n).choose n * n.factorial * n.factorial) := by
              ring
      _ = (3 * n).choose n * n.factorial * (2 * n).factorial := by rw [f1]
      _ = (3 * n).factorial := f2
  have hv : 2 * padicValNat 3
      ((2 * n).choose n * (3 * n).choose n * n.factorial * n.factorial * n.factorial) =
      2 * padicValNat 3 (3 * n).factorial := congrArg (fun x => 2 * padicValNat 3 x) hfact
  have hp0 : (2 * n).choose n * (3 * n).choose n ≠ 0 := Nat.ne_of_gt hprod_pos
  rw [padicValNat.mul (mul_ne_zero (mul_ne_zero hp0 (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _),
    padicValNat.mul (mul_ne_zero hp0 (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _),
    padicValNat.mul hp0 (Nat.factorial_ne_zero _)] at hv
  have ln := sub_one_mul_padicValNat_factorial (p := 3) n
  have l3n := sub_one_mul_padicValNat_factorial (p := 3) (3 * n)
  simp only [show 3 - 1 = 2 from rfl] at ln l3n
  have d3n : (Nat.digits 3 (3 * n)).sum = (Nat.digits 3 n).sum := digits_mul_base_sum (by omega) n
  have sn : (Nat.digits 3 n).sum ≤ n := Nat.digit_sum_le 3 n
  have hval_prod : padicValNat 3 ((2 * n).choose n * (3 * n).choose n) = (Nat.digits 3 n).sum := by
    omega
  have hsub_digits : (Nat.digits 3 n).sum ≤
      (Nat.digits 3 k).sum + (Nat.digits 3 (n - k)).sum := by
    have hnk := Nat.choose_mul_factorial_mul_factorial hk
    have hv' : 2 * padicValNat 3 (n.choose k * k.factorial * (n - k).factorial) =
        2 * padicValNat 3 n.factorial := congrArg (fun x => 2 * padicValNat 3 x) hnk
    have hc0 : n.choose k ≠ 0 := Nat.ne_of_gt (Nat.choose_pos hk)
    rw [padicValNat.mul (mul_ne_zero hc0 (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _),
      padicValNat.mul hc0 (Nat.factorial_ne_zero _)] at hv'
    have lk := sub_one_mul_padicValNat_factorial (p := 3) k
    have lnk := sub_one_mul_padicValNat_factorial (p := 3) (n - k)
    simp only [show 3 - 1 = 2 from rfl] at lk lnk
    have sk : (Nat.digits 3 k).sum ≤ k := Nat.digit_sum_le 3 k
    have snk : (Nat.digits 3 (n - k)).sum ≤ n - k := Nat.digit_sum_le 3 (n - k)
    omega
  rw [padicValNat.mul (Nat.ne_of_gt (TNat_pos k)) (Nat.ne_of_gt (TNat_pos (n - k))),
    padicValNat_three_TNat k, padicValNat_three_TNat (n - k)]
  omega

def fStep (m k : ℕ) : ℕ :=
  (if m ≤ (3 * k) % m + (3 * k) % m then 1 else 0) +
  (if m ≤ k % m + (2 * k) % m then 1 else 0)

lemma mul_mod_eq_mul_mod_mod (c k m : ℕ) : (c * k) % m = (c * (k % m)) % m := by
  rw [Nat.mul_mod, Nat.mul_mod c (k % m), Nat.mod_mod]

lemma fStep_ge_one_of_six_mod_ge {m k : ℕ} (hm : 0 < m) (h : m ≤ 6 * (k % m)) :
    1 ≤ fStep m k := by
  unfold fStep
  set r := k % m
  have hr : r < m := Nat.mod_lt k hm
  have h2 : (2 * k) % m = (2 * r) % m := mul_mod_eq_mul_mod_mod 2 k m
  have h3 : (3 * k) % m = (3 * r) % m := mul_mod_eq_mul_mod_mod 3 k m
  rw [h2, h3]
  by_cases c1 : 3 * r < m
  · have e3 : (3 * r) % m = 3 * r := Nat.mod_eq_of_lt c1
    rw [e3]; split_ifs <;> omega
  · by_cases c2 : 2 * r < m
    · have e2 : (2 * r) % m = 2 * r := Nat.mod_eq_of_lt c2
      rw [e2]; split_ifs <;> omega
    · by_cases c3 : 3 * r < 2 * m
      · have e3 : (3 * r) % m = 3 * r - m := by
          have heq : 3 * r = m * 1 + (3 * r - m) := by omega
          conv_lhs => rw [heq]
          rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by omega)]
        rw [e3]; split_ifs <;> omega
      · have e2 : (2 * r) % m = 2 * r - m := by
          have heq : 2 * r = m * 1 + (2 * r - m) := by omega
          conv_lhs => rw [heq]
          rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by omega)]
        rw [e2]; split_ifs <;> omega

lemma step_ineq_non_three {m n k : ℕ} (hm : 2 ≤ m) (hn : 0 < n) (hk : k ≤ n)
    (hm3 : m ∣ 2 * n - 1 → 5 ≤ m) :
    (if m ∣ 2 * n - 1 then 1 else 0) + (if m ≤ n % m + (2 * n) % m then 1 else 0) ≤
      fStep m k + fStep m (n - k) := by
  have hm_pos : 0 < m := by omega
  set r1 := k % m
  set r2 := (n - k) % m
  set rn := n % m
  have hr1 : r1 < m := Nat.mod_lt _ hm_pos
  have hr2 : r2 < m := Nat.mod_lt _ hm_pos
  have hrn : rn < m := Nat.mod_lt _ hm_pos
  have hsum_mod : (r1 + r2) % m = rn := by
    dsimp [r1, r2, rn]
    rw [← Nat.add_mod, Nat.add_sub_of_le hk]
  have hr_ge : rn ≤ r1 + r2 := by
    have := Nat.mod_le (r1 + r2) m
    omega
  have h2n_mod : (2 * n) % m = (2 * rn) % m := mul_mod_eq_mul_mod_mod 2 n m
  by_cases hdvd : m ∣ 2 * n - 1
  · have hm5 : 5 ≤ m := hm3 hdvd
    obtain ⟨q, hq⟩ := hdvd
    have hq_pos : 0 < q := by
      rcases eq_or_ne q 0 with rfl | hq0
      · simp at hq; omega
      · omega
    have hm_odd : m % 2 = 1 := by
      by_contra hme
      have hm0 : m % 2 = 0 := by omega
      have hprod0 : (m * q) % 2 = 0 := by rw [Nat.mul_mod, hm0]; simp
      omega
    have hq_odd : q % 2 = 1 := by
      by_contra hqe
      have hq0 : q % 2 = 0 := by omega
      have hprod0 : (m * q) % 2 = 0 := by rw [Nat.mul_mod, hq0]; simp
      omega
    set um := m / 2
    set uq := q / 2
    have hm_rep : m = 2 * um + 1 := by omega
    have hq_rep : q = 2 * uq + 1 := by omega
    have hmq_eq : 2 * n - 1 = 2 * (m * uq + um) + 1 := by
      calc 2 * n - 1 = m * q := hq
      _ = m * (2 * uq + 1) := by rw [hq_rep]
      _ = 2 * (m * uq) + m := by ring
      _ = 2 * (m * uq) + (2 * um + 1) := by rw [hm_rep]
      _ = 2 * (m * uq + um) + 1 := by ring
    have hn_eq : n = m * uq + (um + 1) := by omega
    have hrn_eq : rn = um + 1 := by
      dsimp [rn]
      rw [hn_eq, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have h2rn_eq : (2 * rn) % m = 1 := by
      rw [hrn_eq, show 2 * (um + 1) = m * 1 + 1 by omega,
        Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have hsecond_false : ¬ (m ≤ rn + (2 * n) % m) := by
      rw [h2n_mod, h2rn_eq, hrn_eq]; omega
    rw [if_pos ⟨q, hq⟩, if_neg hsecond_false]
    have h6 : 2 * m < 6 * (r1 + r2) := by omega
    by_cases hleft : m ≤ 6 * r1
    · have := fStep_ge_one_of_six_mod_ge hm_pos hleft; omega
    · have hright : m ≤ 6 * r2 := by omega
      have := fStep_ge_one_of_six_mod_ge hm_pos hright; omega
  · rw [if_neg hdvd]
    by_cases hsec : m ≤ rn + (2 * n) % m
    · rw [if_pos hsec]
      have h3rn : m ≤ 3 * rn := by
        by_contra hlt
        have e2 : (2 * rn) % m = 2 * rn := Nat.mod_eq_of_lt (by omega)
        rw [h2n_mod, e2] at hsec
        omega
      by_cases hleft : m ≤ 6 * r1
      · have := fStep_ge_one_of_six_mod_ge hm_pos hleft; omega
      · have hright : m ≤ 6 * r2 := by omega
        have := fStep_ge_one_of_six_mod_ge hm_pos hright; omega
    · rw [if_neg hsec]; omega

lemma padicValNat_eq_sum_dvd {p a b : ℕ} [hp : Fact p.Prime] (ha : 0 < a) (hb : a < b) :
    padicValNat p a = ∑ i ∈ Finset.Ico 1 b, if p ^ i ∣ a then 1 else 0 := by
  set v := padicValNat p a
  have hv_lt : v < b := by
    have hpow_le : p ^ v ≤ a := Nat.le_of_dvd ha pow_padicValNat_dvd
    have h2 : v < 2 ^ v := Nat.lt_two_pow_self
    have hp2 : 2 ^ v ≤ p ^ v := Nat.pow_le_pow_left hp.out.two_le v
    omega
  have hfilter : (∑ i ∈ Finset.Ico 1 b, if p ^ i ∣ a then 1 else 0) =
      (Finset.Ico 1 (v + 1)).card := by
    rw [← Finset.card_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_Ico, padicValNat_dvd_iff_le (Nat.ne_of_gt ha)]
    omega
  rw [hfilter, Nat.card_Ico]
  omega

lemma padicValNat_choose_eq_sum {p n k b : ℕ} [hp : Fact p.Prime] (hkn : k ≤ n) (hnb : n < b) :
    padicValNat p (n.choose k) =
      ∑ i ∈ Finset.Ico 1 b, if p ^ i ≤ k % p ^ i + (n - k) % p ^ i then 1 else 0 := by
  have hlog : Nat.log p n < b := lt_of_le_of_lt (Nat.log_le_self p n) hnb
  rw [padicValNat_choose hkn hlog, Finset.card_filter]

lemma padicValNat_non_three_den_le {p n k : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hn : 0 < n) (hk : k ≤ n) :
    padicValNat p (denNat n) ≤ padicValNat p (TNat k * TNat (n - k)) := by
  have : Fact p.Prime := ⟨hp⟩
  set b := 6 * n + 2
  unfold denNat
  rw [padicValNat.mul (by omega) (Nat.ne_of_gt (Nat.choose_pos (by omega))),
    padicValNat_eq_sum_dvd (b := b) (by omega) (by omega),
    padicValNat_choose_eq_sum (b := b) (by omega) (by omega),
    ← Finset.sum_add_distrib]
  have hT : ∀ j ≤ n, padicValNat p (TNat j) = ∑ i ∈ Finset.Ico 1 b, fStep (p ^ i) j := by
    intro j hj
    unfold TNat fStep
    rw [padicValNat.mul (Nat.ne_of_gt (Nat.choose_pos (by omega)))
        (Nat.ne_of_gt (Nat.choose_pos (by omega))),
      padicValNat_choose_eq_sum (b := b) (by omega) (by omega),
      padicValNat_choose_eq_sum (b := b) (by omega) (by omega),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show 6 * j - 3 * j = 3 * j by omega, show 3 * j - j = 2 * j by omega]
  rw [padicValNat.mul (Nat.ne_of_gt (TNat_pos k)) (Nat.ne_of_gt (TNat_pos (n - k))),
    hT k hk, hT (n - k) (by omega), ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [Finset.mem_Ico] at hi
  rw [show 3 * n - n = 2 * n by omega]
  have hm2 : 2 ≤ p ^ i := by
    calc 2 ≤ p ^ 1 := by simpa using hp.two_le
    _ ≤ p ^ i := Nat.pow_le_pow_right hp.pos hi.1
  refine step_ineq_non_three hm2 hn hk fun hdvd => ?_
  have hp_dvd : p ∣ 2 * n - 1 := dvd_trans (dvd_pow_self p (by omega : i ≠ 0)) hdvd
  have hp2 : p ≠ 2 := by
    intro h2; subst h2
    obtain ⟨q, hq⟩ := hp_dvd; omega
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    by_contra hlt
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
    · exact absurd hp (by decide)
  calc 5 ≤ p ^ 1 := by simpa using hp5
  _ ≤ p ^ i := Nat.pow_le_pow_right hp.pos hi.1

lemma denNat_dvd_term {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    denNat n ∣ TNat k * TNat (n - k) := by
  have hd : denNat n ≠ 0 := Nat.ne_of_gt (denNat_pos hn)
  have hm : TNat k * TNat (n - k) ≠ 0 :=
    Nat.ne_of_gt (Nat.mul_pos (TNat_pos k) (TNat_pos (n - k)))
  rw [← Nat.factorization_le_iff_dvd hd hm]
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
    by_cases hp3 : p = 3
    · subst hp3; exact padicValNat_three_den_le hn hk
    · exact padicValNat_non_three_den_le hp hp3 hn hk
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

lemma denNat_dvd_numNat {n : ℕ} (hn : 0 < n) : denNat n ∣ numNat n := by
  unfold numNat
  refine Finset.dvd_sum fun k hk => ?_
  rw [Finset.mem_range] at hk
  exact denNat_dvd_term hn (by omega)

/- Part 3: Three-term recurrence for `numNat` via WZ polynomial telescoper -/

lemma TNat_succ (k : ℕ) :
    (k + 1) ^ 2 * TNat (k + 1) = 12 * (6 * k + 1) * (6 * k + 5) * TNat k := by
  have hf0 := TNat_mul_factorials k
  have hf1 := TNat_mul_factorials (k + 1)
  have f6 : (6 * (k + 1)).factorial =
      (6 * k + 6) * (6 * k + 5) * (6 * k + 4) * (6 * k + 3) * (6 * k + 2) * (6 * k + 1) *
        (6 * k).factorial := by
    rw [show 6 * (k + 1) = 6 * k + 6 by omega]
    simp only [Nat.factorial_succ]; ring
  have f3 : (3 * (k + 1)).factorial =
      (3 * k + 3) * (3 * k + 2) * (3 * k + 1) * (3 * k).factorial := by
    rw [show 3 * (k + 1) = 3 * k + 3 by omega]
    simp only [Nat.factorial_succ]; ring
  have f1' : (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
  have f2 : (2 * (k + 1)).factorial = (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := by
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    simp only [Nat.factorial_succ]; ring
  rw [f6, f3, f1', f2] at hf1
  set F := (3 * k).factorial * k.factorial * (2 * k).factorial
  have hF_pos : 0 < F := by positivity
  have hstep1 : (TNat (k + 1) *
      ((3 * k + 3) * (3 * k + 2) * (3 * k + 1) * (k + 1) * (2 * k + 2) * (2 * k + 1))) * F =
      ((6 * k + 6) * (6 * k + 5) * (6 * k + 4) * (6 * k + 3) * (6 * k + 2) * (6 * k + 1) *
        TNat k) * F := by
    calc
      (TNat (k + 1) * ((3 * k + 3) * (3 * k + 2) * (3 * k + 1) * (k + 1) *
          (2 * k + 2) * (2 * k + 1))) * F
          = TNat (k + 1) * ((3 * k + 3) * (3 * k + 2) * (3 * k + 1) * (3 * k).factorial) *
              ((k + 1) * k.factorial) * ((2 * k + 2) * (2 * k + 1) * (2 * k).factorial) := by
              dsimp [F]; ring
      _ = (6 * k + 6) * (6 * k + 5) * (6 * k + 4) * (6 * k + 3) * (6 * k + 2) * (6 * k + 1) *
            (6 * k).factorial := hf1
      _ = (6 * k + 6) * (6 * k + 5) * (6 * k + 4) * (6 * k + 3) * (6 * k + 2) * (6 * k + 1) *
            (TNat k * F) := by
              have hf0' : TNat k * F = (6 * k).factorial := by dsimp [F]; linarith
              rw [hf0']
      _ = ((6 * k + 6) * (6 * k + 5) * (6 * k + 4) * (6 * k + 3) * (6 * k + 2) * (6 * k + 1) *
            TNat k) * F := by ring
  have hstep2 := Nat.mul_right_cancel hF_pos hstep1
  have hcancel_pos : 0 < 6 * (k + 1) * (3 * k + 2) * (3 * k + 1) * (2 * k + 1) := by positivity
  apply Nat.mul_right_cancel hcancel_pos
  calc
    (k + 1) ^ 2 * TNat (k + 1) * (6 * (k + 1) * (3 * k + 2) * (3 * k + 1) * (2 * k + 1))
        = TNat (k + 1) * ((3 * k + 3) * (3 * k + 2) * (3 * k + 1) * (k + 1) *
            (2 * k + 2) * (2 * k + 1)) := by ring
    _ = (6 * k + 6) * (6 * k + 5) * (6 * k + 4) * (6 * k + 3) * (6 * k + 2) * (6 * k + 1) *
          TNat k := hstep2
    _ = 12 * (6 * k + 1) * (6 * k + 5) * TNat k *
          (6 * (k + 1) * (3 * k + 2) * (3 * k + 1) * (2 * k + 1)) := by ring

def TInt (m : ℤ) : ℤ := if 0 ≤ m then (TNat m.toNat : ℤ) else 0

lemma TInt_succ (m : ℤ) :
    (m + 1) ^ 2 * TInt (m + 1) = 12 * (6 * m + 1) * (6 * m + 5) * TInt m := by
  by_cases hm : 0 ≤ m
  · lift m to ℕ using hm
    unfold TInt
    rw [if_pos (by omega), if_pos (by omega)]
    have h1 : ((m : ℤ) + 1).toNat = m + 1 := by omega
    have h0 : (m : ℤ).toNat = m := by omega
    rw [h1, h0]
    exact_mod_cast TNat_succ m
  · by_cases hm1 : m = -1
    · subst hm1; unfold TInt; norm_num
    · unfold TInt
      rw [if_neg hm, if_neg (by omega)]
      ring

def wzCert (n k : ℤ) : ℤ :=
  (2 * k - 3 * (n + 2)) * k ^ 2 * TInt k * TInt (n + 2 - k) +
    432 * (3 * n + 4 - 2 * k) * k ^ 2 * TInt k * TInt (n + 1 - k)

lemma wz_pointwise (n k : ℤ) :
    (n + 2) ^ 3 * TInt k * TInt (n + 2 - k) -
        24 * (2 * n + 3) * (18 * n ^ 2 + 54 * n + 41) * TInt k * TInt (n + 1 - k) +
        20736 * (n + 1) * (3 * n + 1) * (3 * n + 5) * TInt k * TInt (n - k) =
      wzCert n (k + 1) - wzCert n k := by
  unfold wzCert
  rw [show n + 2 - (k + 1) = n + 1 - k by ring,
    show n + 1 - (k + 1) = n - k by ring]
  have hX : (k + 1) ^ 2 * TInt (k + 1) - 12 * (6 * k + 1) * (6 * k + 5) * TInt k = 0 := by
    linarith [TInt_succ k]
  have hY1 : (n + 1 - k) ^ 2 * TInt (n + 1 - k) -
      12 * (6 * (n - k) + 1) * (6 * (n - k) + 5) * TInt (n - k) = 0 := by
    have := TInt_succ (n - k)
    rw [show n - k + 1 = n + 1 - k by ring] at this
    linarith
  have hY2 : (n + 2 - k) ^ 2 * TInt (n + 2 - k) -
      12 * (6 * (n + 1 - k) + 1) * (6 * (n + 1 - k) + 5) * TInt (n + 1 - k) = 0 := by
    have := TInt_succ (n + 1 - k)
    rw [show n + 1 - k + 1 = n + 2 - k by ring] at this
    linarith
  linear_combination
    -((2 * (k + 1) - 3 * (n + 2)) * TInt (n + 1 - k) +
        432 * (3 * n + 4 - 2 * (k + 1)) * TInt (n - k)) * hX +
      (TInt k * (2 * k + n + 2)) * hY2 -
      (432 * TInt k * (2 * k + n + 2)) * hY1

lemma sum_TInt_conv {m B : ℕ} (hB : m < B) :
    (∑ k ∈ Finset.range B, TInt k * TInt ((m : ℤ) - k)) = (numNat m : ℤ) := by
  have hsplit : Finset.range B = Finset.range (m + 1) ∪ Finset.Ico (m + 1) B := by
    ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  rw [hsplit, Finset.sum_union (by
    rw [Finset.disjoint_left]; intro k hk1 hk2
    simp only [Finset.mem_range, Finset.mem_Ico] at hk1 hk2; omega)]
  have hzero : ∑ k ∈ Finset.Ico (m + 1) B, TInt k * TInt ((m : ℤ) - k) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    unfold TInt
    rw [if_neg (show ¬ (0 ≤ (m : ℤ) - k) by omega), mul_zero]
  rw [hzero, add_zero]
  unfold numNat
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  unfold TInt
  rw [if_pos (by omega), if_pos (by omega)]
  have h1 : (k : ℤ).toNat = k := by omega
  have h2 : ((m : ℤ) - k).toNat = m - k := by omega
  rw [h1, h2]

lemma numNat_recurrence (n : ℕ) :
    (n + 2) ^ 3 * numNat (n + 2) +
        20736 * (n + 1) * (3 * n + 1) * (3 * n + 5) * numNat n =
      24 * (2 * n + 3) * (18 * n ^ 2 + 54 * n + 41) * numNat (n + 1) := by
  zify
  have hsum : ∑ k ∈ Finset.range (n + 3),
      (((n : ℤ) + 2) ^ 3 * TInt k * TInt ((n : ℤ) + 2 - k) -
        24 * (2 * (n : ℤ) + 3) * (18 * (n : ℤ) ^ 2 + 54 * (n : ℤ) + 41) * TInt k *
          TInt ((n : ℤ) + 1 - k) +
        20736 * ((n : ℤ) + 1) * (3 * (n : ℤ) + 1) * (3 * (n : ℤ) + 5) * TInt k *
          TInt ((n : ℤ) - k)) =
      wzCert n ((n : ℤ) + 3) - wzCert n 0 := by
    have htel := Finset.sum_range_sub (fun k : ℕ => wzCert n k) (n + 3)
    push_cast at htel ⊢
    rw [← htel]
    refine Finset.sum_congr rfl fun k _ => ?_
    simpa [Nat.cast_add, Nat.cast_one] using wz_pointwise n k
  have hc0 : wzCert n 0 = 0 := by unfold wzCert; ring
  have hcN : wzCert n ((n : ℤ) + 3) = 0 := by
    unfold wzCert TInt
    rw [if_neg (show ¬ (0 ≤ (n : ℤ) + 2 - ((n : ℤ) + 3)) by omega),
      if_neg (show ¬ (0 ≤ (n : ℤ) + 1 - ((n : ℤ) + 3)) by omega)]
    ring
  rw [hc0, hcN, sub_self] at hsum
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum] at hsum
  have s2 := sum_TInt_conv (m := n + 2) (B := n + 3) (by omega)
  have s1 := sum_TInt_conv (m := n + 1) (B := n + 3) (by omega)
  have s0 := sum_TInt_conv (m := n) (B := n + 3) (by omega)
  push_cast at s2 s1 s0
  rw [s2, s1, s0] at hsum
  linarith

/- Part 4: Exact 2-adic valuation of `numNat` and final theorem -/

lemma padicValNat_two_pow_mul_odd (r u : ℕ) (hu : u % 2 = 1) :
    padicValNat 2 (2 ^ r * u) = r := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  rw [padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by omega), add_zero]

lemma padicValNat_eq_of_add_eq_of_lt {p x b a : ℕ} [hp : Fact p.Prime]
    (hx : x ≠ 0) (hb : b ≠ 0) (ha : a ≠ 0)
    (hadd : x + b = a) (hlt : padicValNat p a < padicValNat p b) :
    padicValNat p x = padicValNat p a := by
  set va := padicValNat p a
  have hdvd_a : p ^ va ∣ a := pow_padicValNat_dvd
  have hdvd_b1 : p ^ (va + 1) ∣ b := by
    rw [padicValNat_dvd_iff_le hb]; omega
  have hdvd_b : p ^ va ∣ b := dvd_trans (pow_dvd_pow p (by omega)) hdvd_b1
  have hdvd_x : p ^ va ∣ x := by
    have : x = a - b := by omega
    rw [this]
    exact Nat.dvd_sub hdvd_a hdvd_b
  have hle : va ≤ padicValNat p x := (padicValNat_dvd_iff_le hx).mp hdvd_x
  by_contra hne
  have hge1 : va + 1 ≤ padicValNat p x := by omega
  have hdvd_x1 : p ^ (va + 1) ∣ x := (padicValNat_dvd_iff_le hx).mpr hge1
  have hdvd_a1 : p ^ (va + 1) ∣ a := hadd ▸ dvd_add hdvd_x1 hdvd_b1
  exact pow_succ_padicValNat_not_dvd ha hdvd_a1

lemma digits_two_succ_add_val (m : ℕ) :
    (Nat.digits 2 (m + 1)).sum + padicValNat 2 (m + 1) = (Nat.digits 2 m).sum + 1 := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have l1 := sub_one_mul_padicValNat_factorial (p := 2) m
  have l2 := sub_one_mul_padicValNat_factorial (p := 2) (m + 1)
  simp only [show 2 - 1 = 1 from rfl, one_mul] at l1 l2
  rw [Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero m)] at l2
  have s1 : (Nat.digits 2 m).sum ≤ m := Nat.digit_sum_le 2 m
  have s2 : (Nat.digits 2 (m + 1)).sum ≤ m + 1 := Nat.digit_sum_le 2 (m + 1)
  omega

lemma padicValNat_two_numNat :
    ∀ n : ℕ, 0 < n → padicValNat 2 (numNat n) = 3 * (Nat.digits 2 n).sum
  | 1, _ => by
    have h1 : numNat 1 = 2 ^ 3 * 15 := by decide
    have hs1 : 3 * (Nat.digits 2 1).sum = 3 := by decide
    rw [h1, hs1]
    exact padicValNat_two_pow_mul_odd 3 15 (by decide)
  | 2, _ => by
    have h2 : numNat 2 = 2 ^ 3 * 3915 := by decide
    have hs2 : 3 * (Nat.digits 2 2).sum = 3 := by decide
    rw [h2, hs2]
    exact padicValNat_two_pow_mul_odd 3 3915 (by decide)
  | n + 3, _ => by
    have : Fact (Nat.Prime 2) := ⟨by decide⟩
    set m := n + 1
    have hm : 0 < m := by omega
    have ih0 := padicValNat_two_numNat m hm
    have ih1 := padicValNat_two_numNat (m + 1) (by omega)
    have hrec := numNat_recurrence m
    set X := (m + 2) ^ 3 * numNat (m + 2)
    set B := 20736 * (m + 1) * (3 * m + 1) * (3 * m + 5) * numNat m
    set A := 24 * (2 * m + 3) * (18 * m ^ 2 + 54 * m + 41) * numNat (m + 1)
    have hX0 : X ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (by positivity) (numNat_pos _))
    have hB0 : B ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (by positivity) (numNat_pos _))
    have hA0 : A ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (by positivity) (numNat_pos _))
    have hvA : padicValNat 2 A = 3 + 3 * (Nat.digits 2 (m + 1)).sum := by
      dsimp [A]
      rw [padicValNat.mul (by positivity) (Nat.ne_of_gt (numNat_pos _)),
        padicValNat.mul (by positivity) (by positivity),
        padicValNat.mul (by positivity) (by positivity), ih1]
      have v24 : padicValNat 2 24 = 3 :=
        padicValNat_two_pow_mul_odd 3 3 (by decide)
      have vodd1 : padicValNat 2 (2 * m + 3) = 0 :=
        padicValNat.eq_zero_of_not_dvd (by omega)
      have vodd2 : padicValNat 2 (18 * m ^ 2 + 54 * m + 41) = 0 :=
        padicValNat.eq_zero_of_not_dvd (by
          intro hdvd; obtain ⟨q, hq⟩ := hdvd
          have : (18 * m ^ 2 + 54 * m + 41) % 2 = (2 * q) % 2 := congrArg (· % 2) hq
          omega)
      omega
    have hvB : 8 + padicValNat 2 (m + 1) + 3 * (Nat.digits 2 m).sum ≤ padicValNat 2 B := by
      dsimp [B]
      rw [padicValNat.mul (by positivity) (Nat.ne_of_gt (numNat_pos _)),
        padicValNat.mul (by positivity) (by positivity),
        padicValNat.mul (by positivity) (by positivity),
        padicValNat.mul (by positivity) (by positivity), ih0]
      have v20736 : padicValNat 2 20736 = 8 :=
        padicValNat_two_pow_mul_odd 8 81 (by decide)
      omega
    have hd0 := digits_two_succ_add_val m
    have hd1 := digits_two_succ_add_val (m + 1)
    rw [show m + 1 + 1 = m + 2 by omega] at hd1
    have hlt : padicValNat 2 A < padicValNat 2 B := by omega
    have hvX := padicValNat_eq_of_add_eq_of_lt hX0 hB0 hA0 hrec hlt
    dsimp [X] at hvX
    rw [padicValNat.mul (by positivity) (Nat.ne_of_gt (numNat_pos _)),
      padicValNat.pow] at hvX
    change padicValNat 2 (numNat (m + 2)) = 3 * (Nat.digits 2 (m + 2)).sum
    omega

lemma digits_two_sum_pos_and_eq_one :
    ∀ m : ℕ, 0 < m → 1 ≤ (Nat.digits 2 m).sum ∧ ((Nat.digits 2 m).sum = 1 ↔ ∃ k : ℕ, m = 2 ^ k)
  | 1, _ => by
    refine ⟨by decide, ⟨fun _ => ⟨0, rfl⟩, fun _ => by decide⟩⟩
  | m + 2, _ => by
    by_cases hpar : (m + 2) % 2 = 0
    · set j := (m + 2) / 2
      have hj_eq : m + 2 = 2 * j := by omega
      have hj_pos : 0 < j := by omega
      have hj_lt : j < m + 2 := by omega
      have ih := digits_two_sum_pos_and_eq_one j hj_pos
      have hsum : (Nat.digits 2 (m + 2)).sum = (Nat.digits 2 j).sum := by
        rw [hj_eq]; exact digits_mul_base_sum (by omega) j
      rw [hsum]
      refine ⟨ih.1, ⟨fun h1 => ?_, fun ⟨k, hk⟩ => ?_⟩⟩
      · obtain ⟨k, hk⟩ := ih.2.mp h1
        exact ⟨k + 1, by rw [hj_eq, hk, pow_succ']⟩
      · rcases k with _ | k
        · omega
        · exact ih.2.mpr ⟨k, by rw [pow_succ'] at hk; omega⟩
    · set j := (m + 2) / 2
      have hj_eq : m + 2 = 2 * j + 1 := by omega
      have hj_pos : 0 < j := by omega
      have hj_lt : j < m + 2 := by omega
      have ih := digits_two_sum_pos_and_eq_one j hj_pos
      have hsum : (Nat.digits 2 (m + 2)).sum = 1 + (Nat.digits 2 j).sum := by
        rw [Nat.digits_def' (by omega) (by omega),
          show (m + 2) % 2 = 1 by omega]
        rfl
      rw [hsum]
      refine ⟨by omega, ⟨fun h1 => by omega, fun ⟨k, hk⟩ => ?_⟩⟩
      rcases k with _ | k
      · omega
      · rw [pow_succ'] at hk; omega

lemma digits_two_mul_pow (m : ℕ) : ∀ k : ℕ, (Nat.digits 2 (m * 2 ^ k)).sum = (Nat.digits 2 m).sum
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, ← mul_assoc, mul_comm (m * 2 ^ k) 2,
      digits_mul_base_sum (by omega), digits_two_mul_pow m k]

lemma a_eq_numNat_div_denNat (n : ℕ) (hn : 0 < n) :
    a n = (numNat n : ℚ) / (denNat n : ℚ) := by
  unfold a tTerm numNat denNat TNat
  have hcast : (((2 * (n : ℚ)) - 1) * ((3 * n).choose n : ℚ)) =
      (((2 * n - 1) * (3 * n).choose n : ℕ) : ℚ) := by
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
    push_cast
    ring
  rw [hcast]
  congr 1
  push_cast
  rfl

/-- Unconditional proof of Zhi-Wei Sun's Conjecture (ii) on OEIS A189286. -/
theorem conjecture_3 (n : ℕ) (hn : 0 < n) :
    ∃ m : ℤ, a n = 8 * m ∧ (Odd m ↔ ∃ k : ℕ, n = 2 ^ k) := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨q, hq⟩ := denNat_dvd_numNat hn
  have hq_pos : 0 < q := by
    rcases eq_or_ne q 0 with rfl | hq0
    · have := numNat_pos n; omega
    · omega
  have hv_num := padicValNat_two_numNat n hn
  have hv_prod : padicValNat 2 (numNat n) = padicValNat 2 (denNat n) + padicValNat 2 q := by
    rw [hq, padicValNat.mul (Nat.ne_of_gt (denNat_pos hn)) (Nat.ne_of_gt hq_pos)]
  have hv_den : padicValNat 2 (denNat n) + (Nat.digits 2 (3 * n)).sum =
      2 * (Nat.digits 2 n).sum := by
    unfold denNat
    rw [padicValNat.mul (by omega) (Nat.ne_of_gt (Nat.choose_pos (by omega))),
      padicValNat.eq_zero_of_not_dvd (by omega : ¬ 2 ∣ 2 * n - 1), zero_add]
    have hch := sub_one_mul_padicValNat_choose_eq_sub_sum_digits
      (p := 2) (show n ≤ 3 * n by omega)
    simp only [show 2 - 1 = 1 from rfl, one_mul, show 3 * n - n = 2 * n by omega] at hch
    have hd2 : (Nat.digits 2 (2 * n)).sum = (Nat.digits 2 n).sum :=
      digits_mul_base_sum (by omega) n
    have hle : (Nat.digits 2 (3 * n)).sum ≤ (Nat.digits 2 n).sum + (Nat.digits 2 (2 * n)).sum := by
      have hnk := Nat.choose_mul_factorial_mul_factorial (show n ≤ 3 * n by omega)
      have hv' : padicValNat 2 ((3 * n).choose n * n.factorial * (3 * n - n).factorial) =
          padicValNat 2 (3 * n).factorial := congrArg (padicValNat 2) hnk
      have hc0 : (3 * n).choose n ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (by omega))
      rw [padicValNat.mul (mul_ne_zero hc0 (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _),
        padicValNat.mul hc0 (Nat.factorial_ne_zero _),
        show 3 * n - n = 2 * n by omega] at hv'
      have l1 := sub_one_mul_padicValNat_factorial (p := 2) n
      have l2 := sub_one_mul_padicValNat_factorial (p := 2) (2 * n)
      have l3 := sub_one_mul_padicValNat_factorial (p := 2) (3 * n)
      simp only [show 2 - 1 = 1 from rfl, one_mul] at l1 l2 l3
      have s1 := Nat.digit_sum_le 2 n
      have s2 := Nat.digit_sum_le 2 (2 * n)
      have s3 := Nat.digit_sum_le 2 (3 * n)
      omega
    omega
  have hv_q : padicValNat 2 q = (Nat.digits 2 n).sum + (Nat.digits 2 (3 * n)).sum := by omega
  have hdn := digits_two_sum_pos_and_eq_one n hn
  have hd3n := digits_two_sum_pos_and_eq_one (3 * n) (by omega)
  have h3n_not_pow : ¬ ∃ j : ℕ, 3 * n = 2 ^ j := by
    rintro ⟨j, hj⟩
    have h3 : 3 ∣ 2 ^ j := ⟨n, hj.symm⟩
    have h32 : 3 ∣ 2 := (by decide : Nat.Prime 3).dvd_of_dvd_pow h3
    omega
  have hd3n_ge2 : 2 ≤ (Nat.digits 2 (3 * n)).sum := by
    have hne1 : (Nat.digits 2 (3 * n)).sum ≠ 1 := mt hd3n.2.mp h3n_not_pow
    omega
  have hv_q_ge3 : 3 ≤ padicValNat 2 q := by omega
  have h8_dvd : 8 ∣ q := by
    change 2 ^ 3 ∣ q
    exact (padicValNat_dvd_iff_le (Nat.ne_of_gt hq_pos)).mpr hv_q_ge3
  obtain ⟨mNat, hmNat⟩ := h8_dvd
  have hmNat_pos : 0 < mNat := by omega
  refine ⟨(mNat : ℤ), ?_, ?_⟩
  · rw [a_eq_numNat_div_denNat n hn, hq, hmNat]
    have hden_ne : (denNat n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (denNat_pos hn))
    push_cast
    field_simp [hden_ne]
  · have hodd_iff : Odd (mNat : ℤ) ↔ padicValNat 2 q = 3 := by
      have hv_split : padicValNat 2 q = 3 + padicValNat 2 mNat := by
        rw [hmNat, padicValNat.mul (by omega) (Nat.ne_of_gt hmNat_pos)]
        have : padicValNat 2 8 = 3 := padicValNat_two_pow_mul_odd 3 1 (by decide)
        omega
      rw [Int.odd_coe_nat, Nat.odd_iff]
      constructor
      · intro hmod
        have h0 : padicValNat 2 mNat = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
        omega
      · intro hv3
        have h0 : padicValNat 2 mNat = 0 := by omega
        by_contra hmod
        have hdvd2 : 2 ∣ mNat := by omega
        have := one_le_padicValNat_of_dvd (Nat.ne_of_gt hmNat_pos) hdvd2
        omega
    rw [hodd_iff]
    constructor
    · intro hv3
      have hs1 : (Nat.digits 2 n).sum = 1 := by omega
      exact hdn.2.mp hs1
    · rintro ⟨k, rfl⟩
      have hs1 : (Nat.digits 2 (2 ^ k)).sum = 1 := hdn.2.mpr ⟨k, rfl⟩
      have hs3 : (Nat.digits 2 (3 * 2 ^ k)).sum = 2 := by
        rw [digits_two_mul_pow 3 k]
        decide
      omega

end Solutions.OeisA189286

namespace OeisA189286

theorem conjecture_3 (n : ℕ) (hn : 0 < n) :
    ∃ m : ℤ, a n = 8 * m ∧ (Odd m ↔ ∃ k : ℕ, n = 2 ^ k) :=
  Solutions.OeisA189286.conjecture_3 n hn

end OeisA189286

end
