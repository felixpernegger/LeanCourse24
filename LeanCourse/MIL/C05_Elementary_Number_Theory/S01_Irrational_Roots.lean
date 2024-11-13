import LeanCourse.Common
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic

#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num

#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three

#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul
#check dvd_def

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h

#check even_of_even_sqr
#check Nat.dvd_gcd

example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have p1: 2 ∣ m := by
    have : 2 ∣ m^2 := by
      rw[sqr_eq]
      exact Nat.dvd_mul_right 2 (n ^ 2)
    apply even_of_even_sqr this
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp p1
  have p2: 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have p3: 2 * k ^ 2 = n ^ 2 := by
    by_contra p
    by_cases l: 2*k^2 > n^2
    linarith
    have : 2*k^2 < n^2 := by simp at l; exact Nat.lt_of_le_of_ne l p
    linarith
  have p4: 2 ∣ n := by
    apply even_of_even_sqr
    rw[← p3]
    exact Nat.dvd_mul_right 2 (k ^ 2)
  have p5: 2 ∣ m.gcd n := by
    apply Nat.dvd_gcd
    exact p1
    exact p4
  have p6: 2 ∣ 1 := by
    rw[← coprime_mn]
    assumption
  norm_num at p6

example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have p1: p ∣ m := by
    have : p ∣ m^2 := by
      rw[sqr_eq]
      exact Nat.dvd_mul_right p (n ^ 2)

    rw [pow_two, prime_p.dvd_mul] at this
    tauto
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp p1
  have p2: p * (p * k ^ 2) = p * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have p3: p * k ^ 2 = n ^ 2 := by
    by_contra q
    by_cases l: p* k ^ 2 > n^2
    have : p * (p * k ^ 2) > p * n ^ 2 := by
      refine Nat.mul_lt_mul_of_pos_left l ?hk
      apply Nat.Prime.two_le at prime_p
      linarith
    linarith
    have : p*k^2 < n^2 := by simp at l; exact Nat.lt_of_le_of_ne l q
    have : p * (p * k ^ 2) < p * n ^ 2 := by
      apply Nat.mul_lt_mul_of_pos_left this
      apply Nat.Prime.two_le at prime_p
      linarith
    linarith
  have p4: p ∣ n := by
    have : p ∣ n^2 := by
      rw[← p3]
      exact Nat.dvd_mul_right p (k ^ 2)
    rw [pow_two, prime_p.dvd_mul] at this
    tauto
  have p5: p ∣ m.gcd n := by
    apply Nat.dvd_gcd
    exact p1
    exact p4
  have p6: p ∣ 1 := by
    rw[← coprime_mn]
    assumption
  norm_num at p6
  apply Nat.Prime.two_le at prime_p
  linarith

#check Nat.primeFactorsList
#check Nat.prime_of_mem_primeFactorsList
#check Nat.prod_primeFactorsList
#check Nat.primeFactorsList_unique

theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have pnz: p ≠ 0 := by
    by_contra _
    apply Nat.Prime.two_le at prime_p
    linarith
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    apply factorization_pow'
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    calc
      (p * n ^ 2).factorization p = p.factorization p + (n^2).factorization p := by
          exact factorization_mul' pnz nsqr_nez p
        _= 1+ (n^2).factorization p := by
          congr
          exact Nat.Prime.factorization' prime_p
           --apply Nat.Prime.factorization prime_p
        _=1+ 2* n.factorization p := by
          congr
          exact factorization_pow' n 2 p
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (pow_eq_zero npowz)
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
    exact factorization_pow' m k p
  have eq2 : ((r + 1) * n ^ k).factorization p =
      k * n.factorization p + (r + 1).factorization p := by
    calc
       ((r + 1) * n ^ k).factorization p = (r+1).factorization p + (n^k).factorization p := by
            apply factorization_mul'
            exact Ne.symm (Nat.zero_ne_add_one r)
          _= (r+1).factorization p + k* n.factorization p := by
            congr
            exact factorization_pow' n k p
          _= k * n.factorization p + (r+1).factorization p := by ring
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
  have t: k * (m.factorization p - n.factorization p) = k * m.factorization p - k* n.factorization p := by exact Nat.mul_sub_left_distrib k (m.factorization p) (n.factorization p)
  rw[← t]
  exact Nat.dvd_mul_right k (m.factorization p - n.factorization p)
#check multiplicity
