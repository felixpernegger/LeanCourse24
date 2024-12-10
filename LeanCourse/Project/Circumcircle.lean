import LeanCourse.Project.Pythagoras
import LeanCourse.Project.Circles
import LeanCourse.Project.Auxiliary
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

theorem pmidpoint_unique {a b p : Point}(ab : a ≠ b)(h : colinear a b p)(hp : point_abs a p = point_abs p b): p = pmidpoint a b := by{
  have : in_between a b p ∨ in_between b p a ∨ in_between p a b := by{exact colinear_imp_in_between2 a b p h}
  obtain h0|h0|h0 := this
  swap
  unfold in_between at *
  rw[hp] at h0
  rw[point_abs_symm p b] at h0
  simp at h0
  contrapose ab
  simp at *
  symm
  exact abs_zero_imp_same b a h0

  swap
  unfold in_between at *
  rw[point_abs_symm p a] at h0
  rw[hp] at h0
  rw[point_abs_symm p b] at h0
  simp at h0
  contrapose ab
  simp at *
  symm
  exact abs_zero_imp_same b a h0

  unfold in_between at h0
  have ap: point_abs a p = 1/2 * point_abs a b := by{
    rw[← hp] at h0
    linarith
  }
  have col2: colinear a p (pmidpoint a b) := by{
    have col1: colinear a b (pmidpoint a b) := by{exact pmidpoint_colinear a b}
    have ba: b ≠ a := by{exact id (Ne.symm ab)}
    apply colinear_perm12 at col1
    apply colinear_perm12 at h
    exact colinear_trans b a p (pmidpoint a b) h col1 ba
  }
  have : in_between a p (pmidpoint a b) ∨ in_between p (pmidpoint a b) a ∨ in_between (pmidpoint a b) a p := by{exact colinear_imp_in_between2 a p (pmidpoint a b) col2}
  obtain p0|p0|p0 := this
  unfold in_between at p0
  rw[ap, pmidpoint_abs_left] at p0
  simp at p0
  symm
  exact abs_zero_imp_same (pmidpoint a b) p p0

  unfold in_between at p0
  rw[point_abs_symm p a, ap, pmidpoint_abs_left] at p0
  obtain ⟨R,hR⟩ := colinear_go_along ab h
  have t1: point_abs a p = abs R := by{rw[hR];exact go_along_abs1 ab R}
  rw[ap] at t1
  obtain ⟨S,hS⟩ := colinear_go_along ab (pmidpoint_colinear a b)
  have t2: point_abs a (pmidpoint a b) = abs S := by{rw[hS]; exact go_along_abs1 ab S}
  rw[pmidpoint_abs_left] at t2
  rw[t1] at t2
  have q0: R = S ∨ R = -S := by{exact abs_eq_abs.mp t2}
  obtain q0|q0 := q0
  rw[hR,hS,q0]


  have : S = 1/2 * point_abs a b := by{
    unfold pmidpoint go_along p_scal_mul padd dir at hS
    simp at hS
    have ba: b ≠ a := by{exact id (Ne.symm ab)}
    have : b.x - a.x ≠ 0 := by{exact sub_neq_zero ba}
    have : (↑(point_abs a b):ℂ) ≠ 0 := by{
      contrapose ab
      simp at *
      exact abs_zero_imp_same a b ab
    }
    field_simp at hS
    have : (↑S * (b.x - a.x)) * 2 = (a.x + b.x) * ↑(point_abs a b) - (a.x * ↑(point_abs a b))*2 := by{

      calc
        (↑S * (b.x - a.x)) * 2 = - a.x * ↑(point_abs a b)*2 + (((a.x * ↑(point_abs a b)  + (↑S * (b.x - a.x))) * 2) ) := by{ring}
          _= - a.x * ↑(point_abs a b)*2 + (a.x + b.x) * ↑(point_abs a b) := by{rw[hS]}
          _= (a.x + b.x) * ↑(point_abs a b) - (a.x * ↑(point_abs a b))*2 := by{ring}
    }
    have tt: (↑S:ℂ) = 1/2 * (↑(point_abs a b) : ℂ) := by{
      calc
        (↑S:ℂ) = 1/2 * 1/(b.x-a.x) * (↑S * (b.x - a.x) * 2) := by{field_simp;ring}
          _= 1/2 * 1/(b.x-a.x) * ((a.x + b.x) * ↑(point_abs a b) - a.x * ↑(point_abs a b) * 2) := by{rw[this]}
          _= 1/2 * (↑(point_abs a b) : ℂ) := by{field_simp;ring}
    }
    field_simp at *
    norm_cast at tt
  }
  rw[this] at q0
  rw[q0] at hR
  rw[hp,point_abs_symm,hR,go_along_abs2 ab (-(1 / 2 * point_abs a b))] at ap
  have : 0 ≤ point_abs a b := by{exact point_abs_pos a b}
  have : |point_abs a b - -(1 / 2 * point_abs a b)| = point_abs a b - -(1 / 2 * point_abs a b) := by{
    simp
    ring_nf
    linarith
  }
  rw[this] at ap
  simp at ap
  contrapose ab
  simp at *
  exact abs_zero_imp_same a b ap

  unfold in_between at p0
  rw[point_abs_symm p a, ap, point_abs_symm (pmidpoint a b) a, pmidpoint_abs_left] at p0
  simp at p0
  symm
  exact abs_zero_imp_same (pmidpoint a b) p p0
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
  apply pmidpoint_unique ab this
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

/- perp bisectiors are Parallel iff the respective lines are parallel:-/

lemma perp_bisector_parallel{a b c d : Point}(ab : a ≠ b)(cd : c ≠ d): Parallel (perp_bisector ab) (perp_bisector cd) ↔ Parallel (Line_through ab) (Line_through cd) := by{
  have p1 : Perpendicular (perp_bisector ab) (Line_through ab) := by{
    apply perp_symm
    exact perp_bisector_is_perp ab
  }
  have p2: Perpendicular (perp_bisector cd) (Line_through cd) := by{
    apply perp_symm
    exact perp_bisector_is_perp cd
  }
  constructor
  intro h
  have s1: Perpendicular (perp_bisector ab) (Line_through cd) := by{
    apply parallel_symm at h
    exact parallel_perp (perp_bisector cd) h p2
  }
  exact perp_perp (perp_bisector ab) p1 s1

  intro h
  have s1: Perpendicular (perp_bisector ab) (Line_through cd) := by{
    apply perp_symm at p1
    exact perp_parallel (Line_through ab) p1 h
  }
  apply perp_symm at s1
  apply perp_symm at p2
  exact perp_perp (Line_through cd) s1 p2
}

/-From now on, we deal with Noncolinear points. As noncolinear points are basically triangles, we will
derive the respective results from triangles at the end.-/

/-First noncoliear points are pairwise different:-/

lemma noncolinear_imp_pairwise_different{a b c : Point}(h : noncolinear a b c): pairwise_different_point3 a b c := by{
  contrapose h
  unfold noncolinear pairwise_different_point3 at *
  simp at *
  apply colinear_self
  tauto
}

/-For simplicity sake, we want to grab them directly:-/

lemma noncolinear_imp_pairwise_different12{a b c : Point}(h : noncolinear a b c): a ≠ b := by{
  contrapose h
  unfold noncolinear
  simp at *
  apply colinear_self
  tauto
}

lemma noncolinear_imp_pairwise_different23{a b c : Point}(h : noncolinear a b c): b ≠ c := by{
  contrapose h
  unfold noncolinear
  simp at *
  apply colinear_self
  tauto
}

lemma noncolinear_imp_pairwise_different13{a b c : Point}(h : noncolinear a b c): a ≠ c := by{
  contrapose h
  unfold noncolinear
  simp at *
  apply colinear_self
  tauto
}

/-also you can permutate them:-/

lemma noncolinear_perm12{a b c : Point}(h : noncolinear a b c): noncolinear b a c := by{
  contrapose h
  unfold noncolinear at *
  simp at *
  apply colinear_perm12
  assumption
}

lemma noncolinear_perm13{a b c : Point}(h : noncolinear a b c): noncolinear c b a := by{
  contrapose h
  unfold noncolinear at *
  simp at *
  apply colinear_perm13
  assumption
}

lemma noncolinear_perm23{a b c : Point}(h : noncolinear a b c): noncolinear a c b := by{
  contrapose h
  unfold noncolinear at *
  simp at *
  apply colinear_perm23
  assumption
}

/-Secondly thefore the lines through them are not parallel: We only do this for the first, explicitly, rest follow with permutations:-/

lemma noncolinear_not_parallel1{a b c : Point}(h : noncolinear a b c): ¬Parallel (Line_through (noncolinear_imp_pairwise_different12 h)) (Line_through (noncolinear_imp_pairwise_different13 h)) := by{
  by_contra h0
  apply (parallel_def (Line_through (noncolinear_imp_pairwise_different12 h)) (Line_through (noncolinear_imp_pairwise_different13 h))).1 at h0
  obtain h0|h0 := h0
  have : a ∈ ∅ := by{
    rw[← h0]
    simp
    constructor
    have : Lies_on a (Line_through (noncolinear_imp_pairwise_different12 h)) := by{
      apply line_through_mem_left
    }
    unfold Lies_on at this
    assumption

    have : Lies_on a (Line_through (noncolinear_imp_pairwise_different13 h)) := by{
      apply line_through_mem_left
    }
    unfold Lies_on at this
    assumption
  }
  contradiction

  have : Lies_on b (Line_through (noncolinear_imp_pairwise_different13 h)) := by{
    unfold Lies_on
    rw[← h0]
    apply line_through_mem_right
  }
  unfold Lies_on Line_through at this
  simp at this
  apply colinear_perm23 at this
  unfold noncolinear at h
  contradiction
}

/-So the perp_bisectors arent parallel, and therefore have an intersection:-/
lemma perp_bisectors_noncolinear_not_parallel1{a b c : Point}(h : noncolinear a b c): ¬Parallel (perp_bisector (noncolinear_imp_pairwise_different12 h)) (perp_bisector (noncolinear_imp_pairwise_different13 h)) := by{
  by_contra h0
  have : Parallel (Line_through (noncolinear_imp_pairwise_different12 h)) (Line_through (noncolinear_imp_pairwise_different13 h)) := by{
    exact (perp_bisector_parallel (noncolinear_imp_pairwise_different12 h) (noncolinear_imp_pairwise_different13 h)).mp h0
  }
  have : ¬Parallel (Line_through (noncolinear_imp_pairwise_different12 h)) (Line_through (noncolinear_imp_pairwise_different13 h)) := by{
    exact noncolinear_not_parallel1 h
  }
  contradiction
}

/-We can now conclude they are copunctal by using the characterization of the perpendicular bisector:-/

theorem perp_bisectors_copunctal{a b c : Point}(h : noncolinear a b c): Copunctal (perp_bisector (noncolinear_imp_pairwise_different12 h)) (perp_bisector (noncolinear_imp_pairwise_different13 h)) (perp_bisector (noncolinear_imp_pairwise_different23 h)) := by{
  apply copunctal_simp
  apply lines_not_same_parallel
  exact perp_bisectors_noncolinear_not_parallel1 h

  use Intersection (perp_bisectors_noncolinear_not_parallel1 h)
  have h1: Lies_on (Intersection (perp_bisectors_noncolinear_not_parallel1 h)) (perp_bisector (noncolinear_imp_pairwise_different12 h)) := by{
    exact (intersection_mem (perp_bisectors_noncolinear_not_parallel1 h)).1
  }
  have h2: Lies_on (Intersection (perp_bisectors_noncolinear_not_parallel1 h)) (perp_bisector (noncolinear_imp_pairwise_different13 h)) := by{
    exact (intersection_mem (perp_bisectors_noncolinear_not_parallel1 h)).2
  }
  constructor
  · exact h1
  constructor
  · exact h2
  apply (perp_bisector_def a b (Intersection (perp_bisectors_noncolinear_not_parallel1 h)) (noncolinear_imp_pairwise_different12 h)).2 at h1
  apply (perp_bisector_def a c (Intersection (perp_bisectors_noncolinear_not_parallel1 h)) (noncolinear_imp_pairwise_different13 h)).2 at h2

  refine (perp_bisector_def b c (Intersection (perp_bisectors_noncolinear_not_parallel1 h)) (noncolinear_imp_pairwise_different23 h)).mp ?h.right.right.a
  rw[← h1,h2]
}

/-Once again by the characterization we can now conclude everything:-/

def pCenter {a b c : Point}(h : noncolinear a b c): Point :=
  Intersection (perp_bisectors_noncolinear_not_parallel1 h)

def pRadius {a b c : Point}(h : noncolinear a b c): ℝ :=
  point_abs (pCenter h) a

/-the pcenter lies on everything:-/

lemma pcenter_mem{a b c : Point}(h : noncolinear a b c): Lies_on (pCenter h) (perp_bisector (noncolinear_imp_pairwise_different12 h)) ∧ Lies_on (pCenter h) (perp_bisector (noncolinear_imp_pairwise_different13 h)) ∧ Lies_on (pCenter h) (perp_bisector (noncolinear_imp_pairwise_different23 h)) := by{
  let u := Line_center (perp_bisectors_copunctal h)
  have : pCenter h = u := by{
    symm
    unfold pCenter
    apply intersection_unique
    unfold u
    constructor
    exact line_center_on_line1 (perp_bisectors_copunctal h)
    exact line_center_on_line2 (perp_bisectors_copunctal h)
  }
  rw[this]
  unfold u
  exact line_center_on_line (perp_bisectors_copunctal h)
}

/-So the radii are all the same:-/

lemma pradius_is_radius{a b c : Point}(h : noncolinear a b c): point_abs (pCenter h) a = pRadius h ∧ point_abs (pCenter h) b = pRadius h ∧ point_abs (pCenter h) c = pRadius h := by{
  constructor
  unfold pRadius
  rfl

  constructor
  unfold pRadius
  symm
  refine (perp_bisector_def a b (pCenter h) (noncolinear_imp_pairwise_different12 h)).mpr ?right.left.a
  unfold pCenter
  apply intersection_mem_left

  unfold pRadius
  symm
  refine (perp_bisector_def a c (pCenter h) (noncolinear_imp_pairwise_different13 h)).mpr ?right.right.a
  exact (pcenter_mem h).2.1
}

lemma pradius_nonneg{a b c : Point}(h : noncolinear a b c): 0 ≤ pRadius h := by{
  unfold pRadius
  exact point_abs_pos (pCenter h) a
}

/-This finally justifies the Circumcircle. I want to save the predicate Circumcircle for triangles, so
in this case we call it "Circle_around":-/

def Circle_around{a b c : Point}(h : noncolinear a b c): CCircle :=
  Circle_through (pCenter h) (⟨pRadius h,pradius_nonneg h⟩)

/-This has raiuds pRadius and center pCenter-/

lemma circle_around_center{a b c : Point}(h : noncolinear a b c): Center (Circle_around h) = pCenter h := by{
  unfold Circle_around
  exact Eq.symm (center_unique (pCenter h) ⟨pRadius h, pradius_nonneg h⟩)
}

lemma circle_around_radius{a b c : Point}(h : noncolinear a b c): Radius (Circle_around h) = pRadius h := by{
  unfold Circle_around
  rw [← radius_unique]
}

/-And really contains all points:-/

lemma circle_around_lies_on{a b c : Point}(h : noncolinear a b c): Lies_on_circle a (Circle_around h) ∧ Lies_on_circle b (Circle_around h) ∧ Lies_on_circle c (Circle_around h) := by{
  unfold Circle_around
  constructor
  apply lies_on_circle_through
  constructor

}
