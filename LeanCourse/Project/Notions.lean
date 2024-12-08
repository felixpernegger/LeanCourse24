import LeanCourse.Project.Circles
import Mathlib

open Function Set Classical

noncomputable section

/- we want to introduce the notion of a point being on the same side
as another of a line.
We say two points lie on the same side of a line iff the segment between them
does interesect the line:-/

def same_side(L : Line)(a b : Point): Prop :=
  ∀(t : ℝ), (0 ≤ t)∧(t ≤ 1) → ¬Lies_on (padd (p_scal_mul t a) (p_scal_mul (1-t) b)) L

/-For this two make sense, a and b cannot lie on L. If this is
the case, we have an equivalence relation (we techincally only need it for reflexivity):-/

lemma same_side_refl{L : Line}{a : Point}(ha: ¬Lies_on a L): same_side L a a := by{
  unfold same_side
  intro t ⟨ht0, ht1⟩
  unfold padd p_scal_mul
  simp at *
  have : ({ x := ↑t * a.x + (1 - ↑t) * a.x } : Point)= a := by{
    ext
    simp
    ring
  }
  rw[this]
  assumption
}

lemma same_side_symm{L : Line}{a b : Point}(h : same_side L a b): same_side L b a := by{
  unfold same_side at *
  intro t ht1
  have : 0 ≤ 1-t ∧ 1-t ≤ 1 := by{
    constructor
    linarith
    linarith
  }
  specialize h (1-t) this
  simp at h
  rwa[padd_comm (p_scal_mul (↑t) b) (p_scal_mul (1 - ↑t) a)]
}

lemma same_side_trans{L : Line}{a b c : Point}(ab : same_side L a b)(bc : same_side L b c): same_side L a c := by{
  unfold same_side
}
