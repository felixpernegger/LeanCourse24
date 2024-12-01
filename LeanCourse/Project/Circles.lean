import LeanCourse.Project.Triangles
import Mathlib

open Function Set Classical

noncomputable section

/-In this section we will define circles and prove some stuff about them.
One of the main goals is to prove that every Triangle has a unique circumcircle.-/

/-Because Circle is taken in mathlib...........
We use CCircle "Complex Circle"-/

/- Now introduce circles:-/
@[ext] structure CCircle where
  range : Set Point
  span := ∃ (z : Point) (R : ℝ), R ≥ 0 ∧ range = {p : Point | point_abs z p = R}

/-And tangents to circles-/
#check Tangential

def LineCircleTangent (C: CCircle) (L : Line) : Prop :=
  Tangential C.range L.range
