import LeanCourse.Project.Pythagoras
import LeanCourse.Project.Circles
import Mathlib

open Function Set Classical

noncomputable section

/-We prove the existence of the circumcircle purely geometrically now!
We do that via perpendicular bisectors:-/

/-First though, we need some lemma for the midpoint of two points:-/

lemma pmidpoint_abs_left(a b : Point): point_abs a (pmidpoint a b) = 1/2 * (point_abs a b) := by{
  unfold pmidpoint point_abs
  obtain ⟨a1,a2⟩ := a
  obtain ⟨b1,b2⟩ := b
  simp
  unfold Complex.abs
  simp
  unfold Complex.normSq
  simp
  ring_nf
  calc
   √(a1 * b1 * (-1 / 2) + a1 ^ 2 * (1 / 4) + b1 ^ 2 * (1 / 4) + a2 * b2 * (-1 / 2) + a2 ^ 2 * (1 / 4) + b2 ^ 2 * (1 / 4)) = √((1/4)*((-(a1 * b1 * 2) + a1 ^ 2 + (b1 ^ 2 - a2 * b2 * 2) + a2 ^ 2 + b2 ^ 2))) := by{ring_nf}
    _= √(1/4) * √(-(a1 * b1 * 2) + a1 ^ 2 + (b1 ^ 2 - a2 * b2 * 2) + a2 ^ 2 + b2 ^ 2) := by{simp}
    _= 1/2 * √(-(a1 * b1 * 2) + a1 ^ 2 + (b1 ^ 2 - a2 * b2 * 2) + a2 ^ 2 + b2 ^ 2) := by{
      norm_num
      left
      simp
      refine (Real.sqrt_eq_iff_mul_self_eq_of_pos ?h.h).mpr ?h.a
      linarith
      ring
    }
    _= √(-(a1 * b1 * 2) + a1 ^ 2 + (b1 ^ 2 - a2 * b2 * 2) + a2 ^ 2 + b2 ^ 2) * (1 / 2) := by{ring}
}

lemma pmidpoint_abs_right(a b : Point): point_abs (pmidpoint a b) b = 1/2 * (point_abs a b) := by{
  unfold pmidpoint point_abs
  obtain ⟨a1,a2⟩ := a
  obtain ⟨b1,b2⟩ := b
  simp
  unfold Complex.abs
  simp
  unfold Complex.normSq
  simp
  ring_nf
  have : (a1 * b1 * (-1 / 2) + a1 ^ 2 * (1 / 4) + b1 ^ 2 * (1 / 4) + a2 * b2 * (-1 / 2) + a2 ^ 2 * (1 / 4) + b2 ^ 2 * (1 / 4)) = 1/4 * (-(a1 * b1 * 2) + a1 ^ 2 + (b1 ^ 2 - a2 * b2 * 2) + a2 ^ 2 + b2 ^ 2) := by{ring}
  rw[this]
  simp
  have : √4 = 2 := by{
    refine (Real.sqrt_eq_iff_mul_self_eq_of_pos ?h).mpr ?_
    linarith
    ring
  }
  rw[this]
  ring
}

lemma pmidpoint_in_between (a b : Point): in_between a b (pmidpoint a b) := by{
  unfold in_between
  rw[pmidpoint_abs_left, pmidpoint_abs_right]
  ring
}

lemma pmidpoint_colinear (a b : Point): colinear a b (pmidpoint a b) := by{
  exact in_between_imp_colinear (pmidpoint_in_between a b)
}

lemma pmidpoint_same_abs (a b : Point): point_abs a (pmidpoint a b) = point_abs (pmidpoint a b) b := by{
  rw[pmidpoint_abs_left, pmidpoint_abs_right]
}

/-The midpoint is the only point with the last two properties:-/

theorem pmidpoint_unique {a b p : Point}(h : colinear a b p)(hp : point_abs a p = point_abs p b): p = pmidpoint a b := by{
  by_cases ab: a=b

}

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

lemma perp_bisector_foot{a b p : Point}(ab : a ≠ b)(hp : Lies_on p (perp_bisector ab)) : foot p (Line_through ab) = pmidpoint a b := by{
  symm
  apply foot_unique
  constructor
  unfold Lies_on Line_through
  simp
  exact pmidpoint_colinear a b

  have : perp_through (Line_through ab) p = perp_bisector ab := by{
    symm
    apply perp_through_unique
    constructor
    exact perp_bisector_is_perp ab
    assumption
  }
  rw[this]
  exact pmidpoint_lies_on_perp_bisector ab
}

/-Now the universal property:-/

theorem perp_bisector_def (a b p : Point)(ab : a ≠ b): (point_abs p a = point_abs p b) ↔ (Lies_on p (perp_bisector ab)) := by{
  constructor
  intro h

  suffices goal: foot p (Line_through ab) = pmidpoint a b
  unfold perp_bisector
  rw[← goal]
  rw[foot_perp_through]
  exact point_lies_on_perp_through (Line_through ab) p

  have s2: point_abs (foot p (Line_through ab)) a = point_abs (foot p (Line_through ab)) b := by{
    have he: perp_points a (foot p (Line_through ab)) p (foot p (Line_through ab)) := by{exact perp_points_foot a p (line_through_mem_left ab)}
    apply perp_points_perm_front at he
    apply perp_points_perm_back at he
    rw[pythagoras_points_ab he]
    clear he

    have he: perp_points b (foot p (Line_through ab)) p (foot p (Line_through ab)) := by{exact perp_points_foot b p (line_through_mem_right ab)}
    apply perp_points_perm_front at he
    apply perp_points_perm_back at he
    rw[pythagoras_points_ab he]
    clear he

    rw[point_abs_symm p a, point_abs_symm p b] at h
    rw[h]
  }
  have : colinear a b (foot p (Line_through ab)):= by{
    have : Lies_on (foot p (Line_through ab)) (Line_through ab) := by{
      exact foot_on_line (Line_through ab) p
    }
    unfold Lies_on at this
    nth_rw 1 [Line_through] at this
    simp at this
    assumption
  }
  apply pmidpoint_unique this
  rw[point_abs_symm]
  assumption

  intro h

  have he: perp_points a (foot p (Line_through ab)) p (foot p (Line_through ab)) := by{exact perp_points_foot a p (line_through_mem_left ab)}
  apply perp_points_perm_front at he
  apply perp_points_perm_back at he
  rw[point_abs_symm p a]
  rw[pythagoras_points_bc he]
  clear he
  rw[perp_bisector_foot ab h]

  have he: perp_points b (foot p (Line_through ab)) p (foot p (Line_through ab)) := by{exact perp_points_foot b p (line_through_mem_right ab)}
  apply perp_points_perm_front at he
  apply perp_points_perm_back at he
  rw[point_abs_symm p b]
  rw[pythagoras_points_bc he]
  clear he
  rw[perp_bisector_foot ab h]
  rw[← pmidpoint_same_abs a b, point_abs_symm a (pmidpoint a b)]
}
