import LeanCourse.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  rw[abs_of_nonneg h]
  rw[abs_of_neg]
  linarith
  exact h

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  rw[abs_of_nonneg h]
  linarith
  rw[abs_of_neg]
  exact h

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x+y) with h | h
  rw[abs_of_nonneg h]
  apply add_le_add; apply le_abs_self; apply le_abs_self

  rw[abs_of_neg]
  rw[neg_add]
  apply add_le_add; apply neg_le_abs_self; apply neg_le_abs_self
  exact h

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  intro h'
  rcases le_or_gt 0 y with h | h
  rw[abs_of_nonneg] at h'
  left
  assumption
  assumption
  rw[abs_of_neg h] at h'
  right
  exact h'

  intro h'
  rcases le_or_gt 0 y with h|h
  rw[abs_of_nonneg]
  rcases h' with u|v; exact u
  calc
    x < -y := by exact v
     _≤ y := by linarith
  exact h

  rw[abs_of_neg h]
  rcases h' with u|v
  calc
    x<y := by exact u
    _≤ -y := by linarith
  exact v









theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  intro a
  constructor
  rcases le_or_gt 0 x with h|h
  rw[abs_of_nonneg] at a
  linarith
  exact h

  rw[abs_of_neg] at a
  linarith
  exact h

  calc
   x≤ abs x := by apply le_abs_self
   _< y := by exact a

  intro a
  rcases le_or_gt 0 x with h|h
  rw[abs_of_nonneg]
  exact a.2
  exact h

  rw[abs_of_neg]
  obtain ⟨a1,a2⟩ := a
  linarith
  exact h



end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  obtain ⟨x, y, h⟩ := h; rcases h with a|a; rw[a]; rw[← zero_add 0]; apply add_le_add;
  exact sq_nonneg x; exact sq_nonneg y; rw[a];
  calc
    x^2+y^2+1≥ x^2+y^2 := by norm_num
            _≥ 0 +0 := by apply add_le_add;exact sq_nonneg x; exact sq_nonneg y
            _= 0 := by ring



example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have fac: (x-1)*(x+1)=0 := by
    ring
    linarith
  apply eq_zero_or_eq_zero_of_mul_eq_zero at fac
  rcases fac with f1|f2
  left
  linarith
  right
  linarith


example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have fac: (x-y)*(x+y)=0 := by
    ring
    linarith
  apply eq_zero_or_eq_zero_of_mul_eq_zero at fac
  rcases fac with f1|f2
  left
  linarith
  right
  linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have fac: (x-1)*(x+1)=0 := by
    ring
    rw[h]
    ring
  apply eq_zero_or_eq_zero_of_mul_eq_zero at fac
  rcases fac with f1|f2
  left
  calc
    x=x-1 + 1 := by ring
    _=0 +1 := by rw[f1]
    _=1 := by ring
  right
  calc
    x=x+1 - 1 := by ring
    _=0 -1 := by rw[f2]
    _=-1 := by ring

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have fac: (x-y)*(x+y)=0 := by
    ring
    rw[h]
    ring
  apply eq_zero_or_eq_zero_of_mul_eq_zero at fac
  rcases fac with f1|f2
  left
  calc
    x=x-y + y := by ring
    _=0 +y := by rw[f1]
    _=y := by ring
  right
  calc
    x=x+y - y := by ring
    _=0 -y := by rw[f2]
    _=-y := by ring

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  intro h
  by_cases h': P
  right
  apply h h'
  left
  exact h'

  intro u v
  rcases u with a|b
  contradiction
  exact b
