import LeanCourse.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro m mge
  calc
    |s m + t m - (a + b)|= abs ((s m - a) + (t m -b)) := by ring
      _≤ abs (s m -a) + abs (t m - b) := by apply abs_add
      _< ε / 2 + ε / 2 := by
          apply add_lt_add
          apply hs
          exact le_of_max_le_left mge
          apply ht
          exact le_of_max_le_right mge
      _=ε := by norm_num


theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  unfold ConvergesTo
  intro ε εpos
  have εcpos : 0 < ε / abs c := by exact div_pos εpos acpos
  rcases cs (ε / abs c) εcpos with ⟨Nt, ht⟩
  use Nt
  intro m mge
  simp
  calc
    abs (c * (s m) - (c * a)) = abs (c * (s m - a)) := by ring
    _= abs (c) * abs (s m -a) := by apply abs_mul
    _< abs (c) * (ε / abs c) := by exact (mul_lt_mul_left acpos).mpr (ht m mge)
    _= ε := by rw[mul_div_left_comm, div_self, mul_one]; exact abs_ne_zero.mpr h




theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n nge
  calc
    abs (s n) = abs ((s n -a) +a) := by ring
      _≤ abs ( s n -a) + abs (a) := by apply abs_add
      _= abs a + abs (s n -a) := by ring
      _< abs a + 1 := by
         apply add_lt_add_left
         apply h n nge

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro m mbig
  simp
  simp at h₁
  calc
    abs (s m * t m) = abs (s m) * abs (t m) := by apply abs_mul
      _≤ B * abs ( t m) := by
        gcongr
        apply le_of_lt
        apply h₀
        exact le_of_max_le_left mbig
      _< B * (ε/B) := by
        gcongr
        apply h₁
        exact le_of_max_le_right mbig
      _= ε := by field_simp




theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by apply abs_pos.2; exact sub_ne_zero_of_ne abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by apply hNa; exact Nat.le_max_left Na Nb
  have absb : |s N - b| < ε := by apply hNb; exact Nat.le_max_right Na Nb
  have : |a - b| < |a - b| := by
    calc
      abs (a-b) = abs ((s N - b) - (s N - a)) := by ring
        _≤ abs (s N - b) + abs (s N - a) := by exact abs_sub (s N - b) (s N - a)
        _< ε + ε := by apply add_lt_add; exact absb; exact absa
        _=abs (a-b) / 2 + abs (a-b)/2 := by rfl
        _=abs (a-b) := by linarith
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
