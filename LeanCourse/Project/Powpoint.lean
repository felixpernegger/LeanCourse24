import LeanCourse.Project.CTangent
import Mathlib

open Function Set Classical

noncomputable section

/-In this section we introduce the power of a point respective a circle.
We will *not* prove the pretty central result that not matter how you intersect
the circle, the product/power of distances stays the same.

We instead focus on the formal definitions and the power line and and some results.
This will later be used for proving the existance of the orthocenter.-/

/-The power of a point is defined as followed:-/

def PowPoint : Point → CCircle → ℝ :=
  fun p C ↦ (point_abs p (Center C))^2- (Radius C)^2


/-Following observations are immediate:-/

lemma powpoint_lies_on(p : Point)(C : CCircle): Lies_on_circle p C ↔ PowPoint p C = 0 := by{
  unfold PowPoint
  constructor
  · intro h
    rw[point_abs_symm p (Center C), point_abs_point_lies_on_circle h,sub_self]
  intro h
  apply point_on_circle_simp
  rw[point_abs_symm]
  have s1: 0 ≤ point_abs p (Center C) := by{exact point_abs_pos p (Center C)}
  have s2: 0 ≤ Radius C := by{exact zero_le (Radius C)}
  have : point_abs p (Center C) ^ 2 = ↑(Radius C) ^ 2 := by{linarith}
  calc
    point_abs p (Center C) = √((point_abs p (Center C))^2) := by{simp [s1]}
      _=√((Radius C)^2) := by{rw[this]}
      _=Radius C := by{simp [s2]}
}

lemma powpoint_inside(p : Point)(C : CCircle): inside_circle p C ↔ PowPoint p C < 0 := by{
  have s1: 0 ≤ point_abs p (Center C) := by{exact point_abs_pos p (Center C)}
  have s2: 0 ≤ Radius C := by{exact zero_le (Radius C)}
  unfold inside_circle PowPoint
  simp [*]
  constructor
  · intro h
    nlinarith

  intro h
  exact lt_of_pow_lt_pow_left 2 s2 h
}

lemma powpoint_outside(p : Point)(C : CCircle): outside_circle p C ↔ 0 < PowPoint p C := by{

}
