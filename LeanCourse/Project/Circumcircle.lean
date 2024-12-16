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

lemma pmidpoint_lies_on {a b : Point}(ab : a ≠ b): Lies_on (pmidpoint a b) (Line_through ab) := by{
  unfold Lies_on Line_through
  simp
  exact pmidpoint_colinear a b
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

/-In particular the vetrices of a Triagle are pairwise different:-/

lemma triangle_pairwise_different(T : Triangle): pairwise_different_point3 T.a T.b T.c := by{
  exact noncolinear_imp_pairwise_different T.noncolinear
}

lemma tri_diff_ab(T : Triangle): T.a ≠ T.b := by{
  exact (triangle_pairwise_different T).1
}

lemma tri_diff_ba(T : Triangle): T.b ≠ T.a := by{
  exact Ne.symm (tri_diff_ab T)
}

lemma tri_diff_bc(T : Triangle): T.b ≠ T.c := by{
  exact (triangle_pairwise_different T).2.1
}

lemma tri_diff_cb(T : Triangle): T.c ≠ T.b := by{
  exact Ne.symm (tri_diff_bc T)
}

lemma tri_diff_ca(T : Triangle): T.c ≠ T.a := by{
  exact (triangle_pairwise_different T).2.2
}

lemma tri_diff_ac(T : Triangle): T.a ≠ T.c := by{
  exact Ne.symm (tri_diff_ca T)
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

def pRadius {a b c : Point}(h : noncolinear a b c): PosReal :=
  ⟨point_abs (pCenter h) a, point_abs_pos (pCenter h) a⟩

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
  apply (lies_on_circle_through a (pCenter h) (pRadius h)).2
  simp
  exact (pradius_is_radius h).1

  constructor
  apply (lies_on_circle_through b (pCenter h) (pRadius h)).2
  simp
  exact (pradius_is_radius h).2.1

  apply (lies_on_circle_through c (pCenter h) (pRadius h)).2
  simp
  exact (pradius_is_radius h).2.2
}

/-The circle around is the only circle satisfying this!-/

theorem circle_around_unique{a b c : Point}{C : CCircle}(h : noncolinear a b c)(hC: Lies_on_circle a C ∧ Lies_on_circle b C ∧ Lies_on_circle c C): C = Circle_around h := by{
  let z := Center C
  let R := Radius C
  have zdef: z = Center C := rfl
  have Rdef: R = Radius C := rfl
  rw[circle_is_circle_through C] at hC
  rw[circle_is_circle_through C]
  rw[← zdef] at hC
  rw[← zdef]
  rw[← Rdef] at hC
  rw[← Rdef]
  clear zdef Rdef
  obtain ⟨hCa,hCb,hCc⟩ := hC
  have ab: a ≠ b := by{
    exact noncolinear_imp_pairwise_different12 h
  }
  have bc: b ≠ c := by{
    exact noncolinear_imp_pairwise_different23 h
  }
  have ac: a ≠ c := by{
    exact noncolinear_imp_pairwise_different13 h
  }
  have abperp: Lies_on z (perp_bisector ab) := by{
    apply (perp_bisector_def a b z ab).1
    have ah: point_abs z a = R := by{exact hCa}
    have bh: point_abs z b = R := by{exact hCb}
    rw[ah,bh]
  }
  have acperp: Lies_on z (perp_bisector ac) := by{
    apply (perp_bisector_def a c z ac).1
    have ah: point_abs z a = R := by{exact hCa}
    have ch: point_abs z c = R := by{exact hCc}
    rw[ah,ch]
  }
  have cent: z = pCenter h := by{
    unfold pCenter
    apply intersection_unique
    tauto
  }
  have t: Center (Circle_through z R) = Center (Circle_around h) := by{
    have : Center (Circle_through z R) = z := by{exact Eq.symm (center_unique z R)}
    rw[this, circle_around_center h]
    assumption
  }
  have ha : Lies_on_circle a (Circle_around h) := by{
    exact (circle_around_lies_on h).1
  }
  have : Radius (Circle_through z R) = Radius (Circle_around h) := by{
    exact same_center_point t hCa ha
  }
  exact circle_same_simp t this
}

/-Every circle of positive radius is a circumcircle/circle_around!-/
lemma posrad_is_circle_around{C : CCircle}(h : PosRad C): ∃(a b c : Point), (noncolinear a b c) ∧ (Lies_on_circle a C ∧ Lies_on_circle b C ∧ Lies_on_circle c C):= by{
  use Point.mk ((Center C).x + (Radius C))
  use Point.mk ((Center C).x - (Radius C))
  use Point.mk ((Center C).x + {re := 0, im := (Radius C)})
  constructor
  contrapose h
  unfold noncolinear PosRad at *
  simp at *
  unfold colinear det conj at *
  simp at *
  contrapose h
  ring_nf
  contrapose h --lol this works
  simp at *
  assumption

  constructor
  apply point_on_circle_simp
  unfold point_abs
  simp

  constructor
  apply point_on_circle_simp
  unfold point_abs
  simp

  apply point_on_circle_simp
  unfold point_abs
  simp
  unfold Complex.abs
  simp
}

lemma circle_around_is_posrad{a b c : Point}(h : noncolinear a b c): PosRad (Circle_around h) := by{
  apply posrad_point
  use a
  use b
  constructor
  have abc: pairwise_different_point3 a b c := by{
    exact noncolinear_imp_pairwise_different h
  }
  unfold pairwise_different_point3 at abc
  tauto

  constructor
  · exact (circle_around_lies_on h).1
  exact (circle_around_lies_on h).2.1
}

/-Quick interlude : If three disjoint points lie on a circle, they are noncolinear!-/
lemma pairwise_different_point_lie_on_circle{a b c : Point}{C : CCircle}(hp : pairwise_different_point3 a b c)(h : Lies_on_circle a C ∧ Lies_on_circle b C ∧ Lies_on_circle c C): noncolinear a b c := by{
  obtain ⟨ha,hb,hc⟩ := h
  by_contra h0
  unfold noncolinear at h0
  simp at h0
  unfold pairwise_different_point3 at hp
  obtain ⟨ab,bc,ca⟩ := hp
  have sab: Lies_on (Center C) (perp_bisector ab) := by{
    apply (perp_bisector_def a b (Center C) ab).1
    rw[point_abs_point_lies_on_circle ha, point_abs_point_lies_on_circle hb]
  }
  have sbc: Lies_on (Center C) (perp_bisector bc) := by{
    apply (perp_bisector_def b c (Center C) bc).1
    rw[point_abs_point_lies_on_circle hb, point_abs_point_lies_on_circle hc]
  }
  have cool: Parallel (perp_bisector ab) (perp_bisector bc) := by{
    refine (perp_bisector_parallel ab bc).mpr ?_
    refine (parallel_quot ab bc).mpr ?_
    apply colinear_perm12 at h0
    apply (colinear_alt b a c).1 at h0
    obtain ⟨a1,a2⟩ := a
    obtain ⟨b1,b2⟩ := b
    obtain ⟨c1,c2⟩ := c
    simp at *
    obtain h0|h0 := h0
    · left
      linarith
    right
    assumption
  }
  apply (parallel_def (perp_bisector ab) (perp_bisector bc)).1 at cool

  obtain p0|p0 := cool
  have : Center C ∈ (perp_bisector ab).range ∩ (perp_bisector bc).range := by{
    unfold Lies_on at *
    tauto
  }
  rw[p0] at this
  contradiction

  have hm: perp_bisector ab = perp_bisector bc := by{
    ext
    rw[p0]
  }
  unfold perp_bisector at hm
  have : Line_through bc = Line_through ab := by{
    apply line_through_unique
    unfold Line_through Lies_on
    simp
    constructor
    apply colinear_perm12; apply colinear_perm13
    assumption

    apply colinear_self
    tauto
  }
  rw[this] at hm
  clear this

  have mids: pmidpoint a b = pmidpoint b c := by{
    have t: ¬Parallel (Line_through ab) (perp_through (Line_through ab) (pmidpoint a b)) := by{exact perp_through_not_parallel (Line_through ab) (pmidpoint a b)}
    have s1: pmidpoint a b = Intersection t := by{
      apply intersection_unique
      constructor
      · exact pmidpoint_lies_on ab
      exact point_lies_on_perp_through (Line_through ab) (pmidpoint a b)
    }
    have s2: pmidpoint b c = Intersection t := by{
      apply intersection_unique
      have : Line_through bc = Line_through ab := by{
      apply line_through_unique
      unfold Line_through Lies_on
      simp
      constructor
      apply colinear_perm12; apply colinear_perm13
      assumption

      apply colinear_self
      tauto
      }
      nth_rw 1[← this]
      constructor
      · exact pmidpoint_lies_on bc
      nth_rw 2[← this] at hm
      rw[hm]
      exact point_lies_on_perp_through (Line_through bc) (pmidpoint b c)
    }
    rw[s1,s2]
  }
  have : c = a := by{
    ext
    unfold pmidpoint at mids
    simp at mids
    field_simp at mids
    calc
      c.x = -b.x + (b.x + c.x) := by{ring}
        _= -b.x + (a.x + b.x) := by{rw[mids]}
        _= a.x := by{ring}
  }
  contradiction
}

/-So two circles are already the same if they share three common points-/

lemma circle_eq_points{C O : CCircle}(a b c : Point)(h : pairwise_different_point3 a b c)(hC : Lies_on_circle a C ∧ Lies_on_circle b C ∧ Lies_on_circle c C)(hO : Lies_on_circle a O ∧ Lies_on_circle b O ∧ Lies_on_circle c O): C = O := by{
  have abc: noncolinear a b c := by{
    exact pairwise_different_point_lie_on_circle h hC
  }
  have s1: C = Circle_around abc := by{
    exact circle_around_unique abc hC
  }
  have s2: O = Circle_around abc := by{
    exact circle_around_unique abc hO
  }
  rw[s1,s2]
}

/-Now we state some of the presented theorems for triangles, starting with:-/

def Circumcircle: Triangle → CCircle :=
  fun T ↦ Circle_around T.noncolinear

/-We now restate some of the stuff we proved with the Circumcircle. Nothing too exciting.-/

lemma lies_on_circumcircle(T : Triangle): Lies_on_circle T.a (Circumcircle T) ∧ Lies_on_circle T.b (Circumcircle T) ∧ Lies_on_circle T.c (Circumcircle T):= by{
  unfold Circumcircle
  exact (circle_around_lies_on T.noncolinear)
}

lemma a_lies_on_circumcircle(T : Triangle): Lies_on_circle (T.a) (Circumcircle T) := by{
  unfold Circumcircle
  exact (circle_around_lies_on T.noncolinear).1
}

lemma b_lies_on_circumcircle(T : Triangle): Lies_on_circle (T.b) (Circumcircle T) := by{
  unfold Circumcircle
  exact (circle_around_lies_on T.noncolinear).2.1
}

lemma c_lies_on_circumcircle(T : Triangle): Lies_on_circle (T.c) (Circumcircle T) := by{
  unfold Circumcircle
  exact (circle_around_lies_on T.noncolinear).2.2
}

lemma circumcircle_unique{T : Triangle}{C : CCircle}(h: Lies_on_circle T.a C ∧ Lies_on_circle T.b C ∧ Lies_on_circle T.c C): C = Circumcircle T := by{
  apply circle_eq_points T.a T.b T.c
  exact triangle_pairwise_different T
  assumption
  exact lies_on_circumcircle T
}

def Circumcenter: Triangle → Point :=
  fun T ↦ Center (Circumcircle T)

def Circumradius: Triangle → PosReal :=
  fun T ↦ Radius (Circumcircle T)

lemma circumcircle_circle_through(T : Triangle): Circumcircle T = Circle_through (Circumcenter T) (Circumradius T) := by{
  unfold Circumcenter Circumradius
  exact circle_is_circle_through (Circumcircle T)
}

lemma point_abs_circumcenter(T : Triangle): point_abs (Circumcenter T) T.a = Circumradius T ∧ point_abs (Circumcenter T) T.b = Circumradius T ∧ point_abs (Circumcenter T) T.c = Circumradius T := by{
  unfold Circumcenter Circumradius
  constructor
  apply point_abs_point_lies_on_circle
  exact a_lies_on_circumcircle T

  constructor
  apply point_abs_point_lies_on_circle
  exact b_lies_on_circumcircle T

  apply point_abs_point_lies_on_circle
  exact c_lies_on_circumcircle T
}

lemma a_abs_circumcenter(T : Triangle): point_abs (Circumcenter T) T.a = Circumradius T := by{
  exact (point_abs_circumcenter T).1
}

lemma b_abs_circumcenter(T : Triangle): point_abs (Circumcenter T) T.b = Circumradius T := by{
  exact (point_abs_circumcenter T).2.1
}

lemma c_abs_circumcenter(T : Triangle): point_abs (Circumcenter T) T.c = Circumradius T := by{
  exact (point_abs_circumcenter T).2.2
}

lemma circumcircle_posrad(T : Triangle) : PosRad (Circumcircle T) := by{
  unfold Circumcircle
  exact circle_around_is_posrad T.noncolinear
}

lemma lies_on_circumcircle_iff(T : Triangle)(p : Point): Lies_on_circle p (Circumcircle T) ↔ point_abs (Circumcenter T) p = Circumradius T := by{
  rw[circumcircle_circle_through T]
  exact lies_on_circle_through p (Circumcenter T) (Circumradius T)
}

/-We finish off this section by introducing / defining the fuerbach / nine-point-circle:-/

def Nine_point_circle: Triangle → CCircle :=
  fun T ↦ Circumcircle (Midtriangle T)

--STATE THE MOST IMPORTANT AND BASIC STUFF; FINISH WITH FEUERBACH CIRCLE
