import LeanCourse.Project.qObject
import Mathlib

open Function Set Classical

noncomputable section

/-Here we prove a few things about tangents (on circles). Unfortunately, we cannot yet prove thales theorem
which is needed for constructing a tangents through a give point to a circle-/

/-As tangent inthe vast majority of cases actually means tangent line to circle, we just use the predicate Tangent-/

def Tangent(L : Line)(C : CCircle) : Prop :=
  Tangential L.range C.range

def Tangent_point{L : Line}{C : CCircle}(h : Tangent L C): Point := by{
  unfold Tangent at h
  exact (Tangential_point h)
}

/-This does what we want:-/

lemma tangent_point_on_line{L : Line}{C : CCircle}(h : Tangent L C): Lies_on (Tangent_point h) L := by{
  unfold Lies_on Tangent_point
  exact (tangential_point_in_sets h).1
}

lemma tangent_point_on_circle{L : Line}{C : CCircle}(h : Tangent L C): Lies_on_circle (Tangent_point h) C := by{
  unfold Lies_on_circle Tangent_point
  exact (tangential_point_in_sets h).2
}

/-And it's unique:-/

theorem tangent_point_unique{L : Line}{C : CCircle}(p : Point)(h : Tangent L C)(hp: Lies_on p L ∧ Lies_on_circle p C): p = Tangent_point h := by{
  unfold Lies_on Tangent_point Lies_on_circle Tangent at *
  exact tangential_point_unique h hp
}

/-therefore the distance on the tangent point is the radius of the circle to the center:-/

lemma point_abs_tangent_point{L : Line}{C : CCircle}(h : Tangent L C) : point_abs (Center C) (Tangent_point h) = Radius C := by{
  refine point_abs_point_lies_on_circle (Tangent_point h) ?h
  exact tangent_point_on_circle h
}

/-Also note:-/
lemma tangent_point_foot{L : Line}{C : CCircle}(h : Tangent L C) : Tangent_point h = foot (Center C) L := by{
  symm
  apply tangent_point_unique
  constructor
  · exact foot_on_line L (Center C)
  refine point_on_circle_simp ?hp.right.h
  sorry
}

/-Now an important theorem:

A line is tangent to a circle, iff the foot of the center of the Circle lies on the Circle: (if this isnt clear, draw a picture):-/

theorem line_tangent_iff(L : Line)(C : CCircle): Tangent L C ↔ Lies_on_circle (foot (Center C) L) C := by{
  constructor
  intro h
  refine point_on_circle_simp ?mp.h
  rw[← tangent_point_foot h]
  exact point_abs_tangent_point h

  intro h
  sorry
}
