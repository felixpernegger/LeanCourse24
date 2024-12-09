import LeanCourse.Project.Pythagoras
import LeanCourse.Project.Circles
import Mathlib

open Function Set Classical

noncomputable section

/-We prove the existence of the circumcircle purely geometrically now!
We do that via perpendicular bisectors:-/

def perp_bisector{a b : Point}(ab : a ≠ b) : Line :=
  perp_through (Line_through ab) (pmidpoint a b)

lemma perp_bisector_is_perp{a b : Point}(ab : a ≠ b): Perpendicular (Line_through ab) (perp_bisector ab) := by{
  unfold perp_bisector
  exact perp_through_is_perp (Line_through ab) (pmidpoint a b)
}

lemma pmidpoint_lies_on_perp_bisector{a b : Point}(ab : a ≠ b): Lies_on (pmidpoint a b) (perp_bisector ab) := by{
  unfold perp_bisector
  exact point_lies_on_perp_through (Line_through ab) (pmidpoint a b)
}

/-Now the universal property:-/

theorem perp_bisector_def (a b p : Point)(ab : a ≠ b): (point_abs p a = point_abs p b) ↔ (Lies_on p (perp_bisector ab)) := by{
  constructor
  intro h
  #check perp_points_foot a p (line_through_mem_left ab)
  #check perp_points_foot b p (line_through_mem_right ab)

  suffices goal: foot p (Line_through ab) = pmidpoint a b
  unfold perp_bisector
  rw[← goal]
  exact?
}
