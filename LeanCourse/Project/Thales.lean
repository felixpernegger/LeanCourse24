import LeanCourse.Project.Angles
import Mathlib

open Function Set Classical

noncomputable section

set_option linter.unusedTactic false

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
  have : 0 < point_abs a b := by{exact point_abs_neq ab}
  have : 0 < 1 / 2 * point_abs a b := by{linarith}
  exact this
}

lemma thales_symm(a b : Point): Thales_circle b a = Thales_circle a b := by{
  unfold Thales_circle
  rw[pmidpoint_symm a b]
  have : (⟨1/2 * point_abs a b,by{have : 0 ≤ point_abs a b := by{exact point_abs_pos a b};linarith}⟩: PosReal) = ⟨1/2 * point_abs b a,by{have : 0 ≤ point_abs b a := by{exact point_abs_pos b a};linarith}⟩ := by{
    ext
    simp
    rw[point_abs_symm]
  }
  rw[this]
}

lemma thales_mem_left(a b : Point): Lies_on_circle a (Thales_circle a b) := by{
  unfold Thales_circle
  refine
    (lies_on_circle_through a (pmidpoint a b)
          ⟨1 / 2 * point_abs a b, Thales_circle.proof_2 a b⟩).mpr
      ?_
  rw[point_abs_symm,point_abs_pmidpoint]
}

lemma thales_mem_right(a b : Point): Lies_on_circle b (Thales_circle a b) := by{
  rw[thales_symm]
  exact thales_mem_left b a
}

lemma thales_mem(a b p : Point): Lies_on_circle p (Thales_circle a b) ↔ point_abs (pmidpoint a b) p = 1/2 * point_abs a b := by{
  unfold Thales_circle Lies_on_circle Circle_through at *
  simp
}

/-Now we feel brave enough to have a go at the theorem:-/

lemma thales_neq_midpoint{a b p : Point}(ab: a ≠ b)(hp : Lies_on_circle p (Thales_circle a b)): p ≠ pmidpoint a b := by{
  rw[← thales_center]
  exact posrad_not_center (thales_posrad ab) hp
}

lemma thales_abs_left{a b p : Point}(hp : Lies_on_circle p (Thales_circle a b)): point_abs (pmidpoint a b) p = point_abs (pmidpoint a b) a := by{
  rw[(thales_mem a b p).1 hp, ← point_abs_pmidpoint, point_abs_symm]
}

lemma thales_abs_right{a b p : Point}(hp : Lies_on_circle p (Thales_circle a b)): point_abs (pmidpoint a b) p = point_abs (pmidpoint a b) b := by{
  rw[(thales_mem a b p).1 hp]
  nth_rw 2[point_abs_symm]
  rw[pmidpoint_symm, point_abs_pmidpoint, point_abs_symm]
}

lemma thales_self(a : Point): ¬PosRad (Thales_circle a a) := by{
  unfold PosRad
  simp
  rw[thales_radius']
  simp
  exact point_abs_self a
}

lemma thales_self_center(a : Point): Center (Thales_circle a a) = a := by{
  rw[thales_center, pmidpoint_self]
}

lemma thales_self_mem{a p : Point}(h : Lies_on_circle p (Thales_circle a a)): p = a := by{
  rw[lies_on_not_posrad (thales_self a) h, thales_self_center]
}

lemma thales_same_angles_left{a b p : Point}(hp : Lies_on_circle p (Thales_circle a b)): Angle (pmidpoint a b) a p = Angle a p (pmidpoint a b) := by{
  exact same_abs_angle (Eq.symm (thales_abs_left hp))
}

lemma thales_same_angles_right{a b p : Point}(hp : Lies_on_circle p (Thales_circle a b)): Angle (pmidpoint a b) b p = Angle b p (pmidpoint a b) := by{
  exact same_abs_angle (Eq.symm (thales_abs_right hp))
}

theorem thales_theorem{a b p : Point}(hp : Lies_on_circle p (Thales_circle a b)): perp_points p a p b := by{
  by_cases ab: a=b
  · rw[ab]
    rw[ab] at hp
    rw[thales_self_mem hp]
    apply perp_points_self
    tauto

  by_cases ah: a = p
  · apply perp_points_self
    tauto
  by_cases bh: b = p
  · apply perp_points_self
    tauto

  apply (angle_perp_points p a b ah bh).2
  have g: Angle a p b = Angle a p (pmidpoint a b) + Angle (pmidpoint a b) p b := by{
    rw[angle_add]
    assumption
    symm
    exact thales_neq_midpoint ab hp
    assumption
  }
  rw[← thales_same_angles_left hp] at g
  nth_rw 3[angle_symm] at g
  rw[← thales_same_angles_right hp] at g
  have t1: p ≠ pmidpoint a b := by{exact thales_neq_midpoint ab hp}
  rw[angle_pmidpoint_left ab ah] at g
  rw[angle_pmidpoint_right ab bh] at g
  nth_rw 3[angle_symm] at g
  simp at *
  have z: pairwise_different_point3 a p b := by{
    unfold pairwise_different_point3
    tauto
  }
  rw[add_comm] at g
  rw[← anglesum_point1' z] at g
  have u: Angle a p b + Angle a p b = Real.pi := by{
    nth_rw 1[g]
    simp
  }
  unfold Angle at *
  obtain u|u := half_arg u
  · left
    assumption
  right
  rw[u]
  refine Real.Angle.angle_eq_iff_two_pi_dvd_sub.mpr ?_
  use 1
  ring
}

/-The inverse also holds. We first show rectangles have same lengths in a specific way:-/

/-Note: The inverse can also be shown by sort of reversing the last angle chase, however we take a slightly more
involved approach which doesnt utilise angles and just cluclates lenghts.-/

lemma parallel_same_abs_foot{L R : Line}{a b : Point}(LR : Parallel L R)(ah : Lies_on a L)(bh : Lies_on b L): point_abs a (foot a R) = point_abs b (foot b R) ∧ point_abs a b = point_abs (foot a R) (foot b R) := by{
  have p1: perp_points a b a (foot a R) := by{
    nth_rw 1[← foot_parallel_twice LR ah]
    nth_rw 2[← foot_parallel_twice LR ah]
    rw[← foot_parallel_twice LR ah] at ah
    apply perp_points_perm_front
    apply perp_points_perm_back
    exact perp_points_foot b (foot a R) bh
  }
  have p2: perp_points b a b (foot b R) := by{
    nth_rw 1[← foot_parallel_twice LR bh]
    nth_rw 2[← foot_parallel_twice LR bh]
    rw[← foot_parallel_twice LR bh] at bh
    apply perp_points_perm_front
    apply perp_points_perm_back
    exact perp_points_foot a (foot b R) ah
  }
  have p3: perp_points (foot a R) a (foot a R) (foot b R) := by{
    apply perp_points_perm_front
    apply perp_points_perm_back
    apply perp_points_perm_switch
    exact perp_points_foot (foot b R) a (foot_on_line R b)
  }
  have p4: perp_points (foot b R) b (foot b R) (foot a R) := by{
    apply perp_points_perm_front
    apply perp_points_perm_back
    apply perp_points_perm_switch
    exact perp_points_foot (foot a R) b (foot_on_line R a)
  }
  have s1: point_abs a b ^ 2 + point_abs (foot a R) a ^ 2 = point_abs (foot b R) b ^ 2 + point_abs (foot a R) (foot b R) ^ 2 := by{
    rw[← pythagoras_points p1, ← pythagoras_points p4]
  }
  have s2: point_abs b a ^ 2 + point_abs (foot b R) b ^ 2 = point_abs (foot a R) a ^ 2 + point_abs (foot b R) (foot a R) ^ 2 := by{
    rw[← pythagoras_points p2, ← pythagoras_points p3]
  }
  rw[point_abs_symm b a, point_abs_symm (foot b R) (foot a R)] at s2
  constructor
  · apply point_abs_same_sq
    rw[point_abs_symm a (foot a R), point_abs_symm b (foot b R)]
    linarith
  apply point_abs_same_sq
  linarith
}

/-Another small thing we will use:-/
lemma perp_points_pmidpoint{a b p : Point}(h : perp_points p a p b): perp_points p (pmidpoint p a) p (pmidpoint p b) := by{
  by_cases ah: p = a
  · rw[ah, pmidpoint_self]
    apply perp_points_self
    tauto
  by_cases bh: p = b
  · rw[bh, pmidpoint_self]
    apply perp_points_self
    tauto
  unfold pmidpoint perp_points at *
  simp
  have s1: p.x - b.x ≠ 0 := by{exact sub_neq_zero bh}
  have : (p.x - (p.x + a.x) / 2) / (p.x - (p.x + b.x) / 2) = ((p.x-a.x)/(p.x-b.x)) := by{
    field_simp
    have : (p.x * 2 - (p.x + b.x)) = p.x-b.x := by{ring}
    rw[this]
    field_simp
    ring
  }
  rw[this, h]
}

/-We will need following lemma:-/
lemma perp_points_midpoint_center_diff{a b p : Point}(h : pairwise_different_point3 a b p)(h' : perp_points p a p b): (pmidpoint p a) ≠ (Center (Circle_around (perp_points_not_colinear h h'))) := by{
  by_contra h0
  have g: Thales_circle p a = Circle_around (perp_points_not_colinear h h') := by{
    apply same_center_point p
    · · rw[thales_center, h0]
    · exact thales_mem_left p a
    exact (circle_around_lies_on (perp_points_not_colinear h h')).2.2
  }
  have go: Lies_on_circle b (Thales_circle p a) := by{rw[g]; exact (circle_around_lies_on (perp_points_not_colinear h h')).2.1}
  have goa: perp_points b p b a := by{exact thales_theorem go}
  apply perp_points_perm_front at goa
  have goal: Parallel (Line_through h.2.2) (Line_through (Ne.symm h.1)) := by{
    apply perp_perp (Line_through h.2.1)
    · apply (perp_quot h.2.1 h.2.2).2
      apply perp_points_perm_front
      apply perp_points_perm_switch
      assumption
    apply (perp_quot h.2.1 (Ne.symm h.1)).2
    apply perp_points_perm_front
    assumption
  }
  have p0: (Line_through h.2.2).range ∩ (Line_through (Ne.symm h.1)).range = ∅ ∨ (Line_through h.2.2).range = (Line_through (Ne.symm h.1)).range := by{exact (parallel_def (Line_through h.right.right) (Line_through (Ne.symm h.left))).mp goal}
  obtain p0|p0 := p0
  have q0: a ∈ ∅ := by{
    rw[← p0]
    simp
    constructor
    · suffices: Lies_on a (Line_through h.2.2)
      · unfold Lies_on at this
        assumption
      exact line_through_mem_right h.2.2
    suffices : Lies_on a (Line_through (Ne.symm h.1))
    · unfold Lies_on at this
      assumption
    exact line_through_mem_right (Ne.symm h.1)
  }
  contradiction

  have u: noncolinear a b p := by{exact perp_points_not_colinear h h'}
  contrapose u
  unfold noncolinear
  simp
  have pn: (Line_through h.2.2) = (Line_through (Ne.symm h.1)) := by{
    ext
    rw[p0]
  }
  have oh: Lies_on p (Line_through (Ne.symm h.1)) := by{
    rw[← pn]
    exact line_through_mem_left h.2.2
  }
  unfold Lies_on Line_through at oh
  simp at oh
  apply colinear_perm12
  assumption
}

/-the central lemma is now the following:-/
lemma perp_points_center{a b p : Point}(h : pairwise_different_point3 a b p)(h' : perp_points p a p b): Center (Circle_around (perp_points_not_colinear h h')) = pmidpoint a b := by{
  have u: noncolinear a b p := by{exact perp_points_not_colinear h h'}
  suffices : point_abs (Center (Circle_around u)) a = 1/2 * point_abs a b ∧ point_abs (Center (Circle_around u)) b = 1/2 * point_abs a b
  · exact pmidpoint_simp this.1 this.2
  rw[← point_abs_pmidpoint_pmidpoint a b p, pythagoras_points_bc (perp_points_pmidpoint h')]
  rw[pmidpoint_abs_left, pmidpoint_symm b p, pmidpoint_abs_right]
  nth_rw 1[← pmidpoint_abs_right p a]
  nth_rw 2[← pmidpoint_abs_left b p]
  have p1: perp_points (pmidpoint a p) a (pmidpoint a p) (Center (Circle_around u)) := by{
    have ap: a ≠ p := by{
      unfold pairwise_different_point3 at h
      tauto
    }
    have ma: (pmidpoint a p) ≠ a := by{
      exact pmidpoint_diff_left ap
    }
    have : Perpendicular (Line_through ma) (perp_bisector ap) := by{
      have : Line_through ma = Line_through ap := by{
        apply line_through_unique
        constructor
        · exact line_through_mem_right ma
        unfold Lies_on Line_through
        simp
        apply colinear_perm13
        apply colinear_perm12
        exact pmidpoint_colinear a p
      }
      rw[this]
      exact perp_bisector_is_perp ap
    }
    have e: Lies_on (Center (Circle_around u)) (perp_bisector ap) := by{
      exact (center_circle_around_lies_on_perp_bisector u).2.2
    }
    exact perp_all this (line_through_mem_left ma) (line_through_mem_right ma) (pmidpoint_lies_on_perp_bisector ap) e
  }
  have p2: perp_points (pmidpoint b p) b (pmidpoint b p) (Center (Circle_around u)) := by{
    have bp: b ≠ p := by{
      unfold pairwise_different_point3 at h
      tauto
    }
    have mb: (pmidpoint b p) ≠ b := by{
      exact pmidpoint_diff_left bp
    }
    have : Perpendicular (Line_through mb) (perp_bisector bp) := by{
      have : Line_through mb = Line_through bp := by{
        apply line_through_unique
        constructor
        · exact line_through_mem_right mb
        unfold Lies_on Line_through
        simp
        apply colinear_perm13
        apply colinear_perm12
        exact pmidpoint_colinear b p
      }
      rw[this]
      exact perp_bisector_is_perp bp
    }
    have e: Lies_on (Center (Circle_around u)) (perp_bisector bp) := by{
      exact (center_circle_around_lies_on_perp_bisector u).2.1
    }
    exact perp_all this (line_through_mem_left mb) (line_through_mem_right mb) (pmidpoint_lies_on_perp_bisector bp) e
  }
  have s1: (1 / 2 * point_abs b p) = point_abs (pmidpoint a p) (Center (Circle_around u)) := by{
    have i1: Parallel (perp_bisector h.2.2) (Line_through h.2.1) := by{
      apply perp_perp (Line_through h.2.2)
      · exact perp_bisector_is_perp h.right.right
      exact (perp_quot h.2.2 h.2.1).2 (perp_points_perm_back h')
    }
    apply parallel_symm at i1
    have i0:  1 / 2 * point_abs b p = point_abs (pmidpoint b p) p := by{exact Eq.symm (pmidpoint_abs_right b p)}
    rw[i0]
    clear i0
    rw[point_abs_symm]
    rw[(parallel_same_abs_foot i1 (line_through_mem_right h.2.1) (pmidpoint_lies_on h.2.1)).2]
    have r: (pmidpoint p a) ≠ (Center (Circle_around u)) := by{
        exact perp_points_midpoint_center_diff h h'
      }
    have : (foot p (perp_bisector ((h.2.2)))) = pmidpoint a p := by{
      have mb: pmidpoint b p ≠ b := by{exact pmidpoint_diff_left h.2.1}
      have : perp_bisector h.2.2 = Line_through r := by{
        apply line_through_unique
        constructor
        · exact pmidpoint_lies_on_perp_bisector h.right.right
        rw[perp_bisector_symm]
        exact (center_circle_around_lies_on_perp_bisector u).2.2
      }
      rw[this]
      rw[pmidpoint_symm p a]
      apply foot_if_perp_points
      have : Perpendicular (qLine_through (pmidpoint p a) p) (qLine_through (pmidpoint p a) (Center (Circle_around u))) := by{
        have mp: pmidpoint p a ≠ p := by{exact pmidpoint_diff_left h.2.2}
        simp [*]
        have j1: Line_through mp = Line_through h.2.2 := by{
          apply line_through_unique
          constructor
          · exact line_through_mem_right mp
          unfold Lies_on Line_through
          simp
          apply colinear_perm13
          apply colinear_perm12
          exact pmidpoint_colinear p a
        }
        rw[j1]
        have j2: Line_through r = perp_bisector h.2.2 := by{
          symm
          apply line_through_unique
          constructor
          · exact pmidpoint_lies_on_perp_bisector h.right.right
          rw[perp_bisector_symm]
          exact (center_circle_around_lies_on_perp_bisector u).2.2
        }
        rw[j2]
        exact perp_bisector_is_perp h.right.right
      }
      exact perp_all this (qline_through_mem_left (pmidpoint p a) p) (qline_through_mem_right (pmidpoint p a) p) (qline_through_mem_left (pmidpoint p a) (Center (Circle_around u))) (qline_through_mem_right (pmidpoint p a) (Center (Circle_around u)))
    }
    rw[this]; clear this
    have : foot (pmidpoint b p) (perp_bisector h.2.2) = Center (Circle_around u) := by{
      have r': Center (Circle_around u) ≠ pmidpoint p a := by{tauto}
      have : perp_bisector h.2.2 = Line_through r' := by{
        apply line_through_unique
        constructor
        · rw[perp_bisector_symm]
          exact (center_circle_around_lies_on_perp_bisector u).2.2
        exact pmidpoint_lies_on_perp_bisector h.right.right
      }
      rw[this]
      apply foot_if_perp_points
      have : Perpendicular (qLine_through (Center (Circle_around u)) (pmidpoint b p)) (qLine_through (Center (Circle_around u)) (pmidpoint p a)) := by{
        have r'': (Center (Circle_around u)) ≠ (pmidpoint b p) := by{
          symm
          apply pairwise_different_point3_perm12 at h
          rw[circle_around_perm12, pmidpoint_symm]
          apply perp_points_perm_switch at h'
          exact perp_points_midpoint_center_diff h h'
        }
        simp [*]
        have q1: Line_through r'' = perp_bisector h.2.1 := by{
          symm
          apply line_through_unique
          constructor
          · exact (center_circle_around_lies_on_perp_bisector u).2.1
          exact pmidpoint_lies_on_perp_bisector h.right.left
        }
        rw[q1]
        have q2: Line_through r' = perp_bisector h.2.2 := by{
          symm
          apply line_through_unique
          constructor
          · rw[perp_bisector_symm]
            exact (center_circle_around_lies_on_perp_bisector u).2.2
          exact pmidpoint_lies_on_perp_bisector h.right.right
        }
        rw[q2]
        apply perp_parallel (Line_through h.2.1)
        · exact perp_bisector_is_perp h.right.left
        apply perp_perp (Line_through h.2.2)
        · apply (perp_quot h.2.2 h.2.1).2
          apply perp_points_perm_back
          assumption
        exact perp_bisector_is_perp h.right.right
      }
      exact perp_all this (qline_through_mem_left (Center (Circle_around u)) (pmidpoint b p)) (qline_through_mem_right (Center (Circle_around u)) (pmidpoint b p)) (qline_through_mem_left (Center (Circle_around u)) (pmidpoint p a)) (qline_through_mem_right (Center (Circle_around u)) (pmidpoint p a))
    }
    rw[this]
  }
  rw[s1, point_abs_symm (pmidpoint a p) (Center (Circle_around u)), pmidpoint_symm, ← pythagoras_points_bc p1, point_abs_symm]
  have s2: (1 / 2 * point_abs p a) = point_abs (pmidpoint b p) (Center (Circle_around u)) := by{
    sorry
  }
  rw[s2, point_abs_symm (pmidpoint b p) (Center (Circle_around u)), add_comm, point_abs_symm b, ← pythagoras_points_bc p2, point_abs_symm b]

  simp
}

theorem thales_inverse{a b p : Point}(h: perp_points p a p b): Lies_on_circle p (Thales_circle a b) := by{
  by_cases ah: p = a
  · rw[ah]
    exact thales_mem_left a b
  by_cases bh: p = b
  · rw[bh]
    exact thales_mem_right a b
  by_cases ab: a = b
  rw[ab] at h
  unfold perp_points at h
  have : p.x-b.x ≠ 0 := by{exact sub_neq_zero bh}
  field_simp at h

  have t: pairwise_different_point3 a b p := by{
    unfold pairwise_different_point3
    tauto
  }
  have u: noncolinear a b p := by{exact perp_points_not_colinear t h}
  suffices : Circle_around u = Thales_circle a b
  · rw[← this]
    exact (circle_around_lies_on u).2.2
  suffices : Center (Circle_around u) = pmidpoint a b
  · apply same_center_point a
    rw[thales_center, this]
    exact (circle_around_lies_on u).1
    exact thales_mem_left a b
  exact perp_points_center t h
}
