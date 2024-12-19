import LeanCourse.Project.Angles
import Mathlib

open Function Set Classical

noncomputable section


--thales

/-In this section we prove thales theorem, first though, some notation:-/

def Thales_circle: Point → Point → CCircle :=
  fun a b ↦ Circle_through (pmidpoint a b) (⟨1/2 * point_abs a b, by{
    have : 0 ≤ point_abs a b := by{exact point_abs_pos a b}
    linarith
  }⟩)

lemma thales_center(a b : Point): Center (Thales_circle a b) = pmidpoint a b := by{
  unfold Thales_circle
  nth_rw 1[center_unique (pmidpoint a b) ⟨1 / 2 * point_abs a b, Thales_circle.proof_2 a b⟩]
}

lemma thales_radius(a b : Point): Radius (Thales_circle a b) = 1/2 * point_abs a b := by{
  unfold Thales_circle
  rw[radius_unique (pmidpoint a b) ⟨1 / 2 * point_abs a b, Thales_circle.proof_2 a b⟩]
}

lemma thales_radius'(a b : Point): Radius (Thales_circle a b) = ⟨1/2 * point_abs a b,by{have : 0 ≤ point_abs a b := by{exact point_abs_pos a b};linarith}⟩ := by{
  unfold Thales_circle
  exact radius_unique (pmidpoint a b) ⟨1 / 2 * point_abs a b, Thales_circle.proof_2 a b⟩
}

lemma thales_posrad{a b : Point}(ab : a ≠ b): PosRad (Thales_circle a b) := by{
  unfold PosRad
  rw[thales_radius' a b]
  suffices : 0 < point_abs a b
  sorry
  exact?
  simp
}
