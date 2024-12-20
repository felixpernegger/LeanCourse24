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
