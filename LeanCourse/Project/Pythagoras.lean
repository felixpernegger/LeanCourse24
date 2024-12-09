import LeanCourse.Project.Reflections
import Mathlib

open Function Set Classical

noncomputable section

/-In this section we introduce right angled triangles and prove the pythagorean theorem.-/

/-For simplicity RIGHT TRIANGLES HAVE THE RIGHT ANGLE IN A-/

def RightTriangle(T : Triangle): Prop :=
  Perpendicular (tri_ab T) (tri_ca T)

theorem pythagoras {T : Triangle}(h : RightTriangle T): (abs_tri_bc T)^2 = (abs_tri_ab T)^2 + (abs_tri_ca T)^2 := by{
  sorry
}
