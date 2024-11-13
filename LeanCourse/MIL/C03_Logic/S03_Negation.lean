import LeanCourse.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro fnlb
  obtain ⟨u,ulb⟩ := fnlb
  obtain ⟨x,xleu⟩ := h u
  specialize ulb x
  have : u < u := by
    calc
      u≤ f x := by exact ulb
      _< u := by exact xleu
  apply lt_irrefl u this

example : ¬FnHasUb fun x ↦ x := by
  intro as
  rcases as with ⟨u, uub⟩
  have h': u+1≤ u := by apply uub (u+1)
  linarith

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro n
  have u0: f b < f b := by
    calc
      f b ≤ f a := by apply h n
        _< f b := by exact h'
  linarith

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro as
  have : f a ≤ f b := by
    apply as h
  linarith

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro a b zmo
    apply le_refl _
  have h' : f 1 ≤ f 0 := le_refl _
  have z: (1 : ℝ)  ≤ 0 := h monof h'
  linarith


example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro xgezero
  specialize h x
  have t: x < x := h xgezero
  linarith


end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro r pro
  apply h
  use r

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro ex
  rcases ex with ⟨a, ap⟩
  specialize h a
  apply h
  exact ap

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  by_contra h''
  exact h' ⟨x, h''⟩



example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro fall
  rcases h with ⟨a, anp⟩
  apply anp
  apply fall a

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  by_contra h'
  apply h
  exact h'

example (h : Q) : ¬¬Q := by
  intro q
  apply q
  exact h

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra h'
  have z: ∀ x, ¬ f x > a := by
    intro x
    by_contra h''
    exact h' ⟨x,h''⟩
  have asup: ∀ x, f x ≤ a := by
    intro y
    specialize z y
    apply le_of_not_gt z
  apply h
  use a
  intro r
  specialize asup r
  exact asup


example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  dsimp [Monotone] at h
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end
