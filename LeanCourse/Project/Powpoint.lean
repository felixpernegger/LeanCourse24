import LeanCourse.Project.CTangent
import Mathlib

open Function Set Classical
set_option linter.unusedTactic false
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
  have s1: 0 ≤ point_abs p (Center C) := by{exact point_abs_pos p (Center C)}
  have s2: 0 ≤ Radius C := by{exact zero_le (Radius C)}
  unfold outside_circle PowPoint
  simp [*]
  constructor
  · intro h
    refine pow_lt_pow_left h s2 ?mp.a
    norm_num

  intro h
  exact lt_of_pow_lt_pow_left 2 s1 h
}


/-The power line between twi lines is the set containing all points of
equal power respcitve two (fixed) circles. If the circles are not concentric
this really is a line (otherwis it would be either the whole plane or nothing)
-/

--THIS DEPENDS ON CASES AHHHH
/-
def PowLine: CCircle → CCircle → Line :=
  fun C O ↦ perp_through (qLine_through (Center C) (Center O)) (go_along (Center C) (Center O) (((Radius C)^2-(Radius O)^2+(point_abs (Center C) (Center O))^2)/(2*(point_abs (Center C) (Center O)))))
-/

/-first small lemma (better suited elsewhere, but whatever)-/

lemma in_between_go_along{a b : Point}{r : ℝ}(ab : a ≠ b)(h : in_between a b (go_along a b r)) : 0 ≤ r ∧ r ≤ point_abs a b := by{
  unfold in_between at h
  have absub : 0 < point_abs a b := by{exact point_abs_neq ab}
  rw[← point_abs_symm b, go_along_abs1 ab, go_along_abs2 ab] at h
  have g1: 0 ≤ r := by{
    sorry
  }
  have g2: r ≤ point_abs a b := by{
    sorry
  }
  tauto
}

/-To define the powline (set set of points in respect to two noncentric circles where powpint to the circles is the same), we have to observe followung
characterization:-/

theorem same_powpoint_char{C O : CCircle}(h : ¬Concentric C O)(p : Point)(h' : in_between (Center C) (Center O) (foot p (qLine_through (Center C) (Center O)))): PowPoint p C = PowPoint p O ↔ Lies_on p (perp_through (qLine_through (Center C) (Center O)) (go_along (Center C) (Center O) (((Radius C)^2-(Radius O)^2+(point_abs (Center C) (Center O))^2)/(2*(point_abs (Center C) (Center O)))))) := by{
  set q := (foot p (qLine_through (Center C) (Center O)))
  have p1: perp_points (Center C) q p q := by{
    exact perp_points_foot (Center C) p (qline_through_mem_left (Center C) (Center O))
  }
  have p2: perp_points (Center O) q p q:= by{
    exact perp_points_foot (Center O) p (qline_through_mem_right (Center C) (Center O))
  }
  apply perp_points_perm_front at p1
  apply perp_points_perm_front at p2
  apply perp_points_perm_back at p1
  apply perp_points_perm_back at p2
  unfold PowPoint
  rw[point_abs_symm p (Center C), point_abs_symm p (Center O), pythagoras_points p1, pythagoras_points p2]
  have s1: point_abs q (Center C) ^ 2 + point_abs p q ^ 2 - ↑(Radius C) ^ 2 =
    point_abs q (Center O) ^ 2 + point_abs p q ^ 2 - ↑(Radius O) ^ 2 ↔ point_abs q (Center C) ^ 2  - point_abs q (Center O) ^ 2 =
    ↑(Radius C) ^ 2  - ↑(Radius O) ^ 2 := by{
      constructor
      intro h
      linarith

      intro h
      linarith
  }
  have s2: Lies_on p (perp_through (qLine_through (Center C) (Center O)) (go_along (Center C) (Center O) ((↑(Radius C) ^ 2 - ↑(Radius O) ^ 2 + point_abs (Center C) (Center O) ^ 2) / (2 * point_abs (Center C) (Center O))))) ↔ q = (go_along (Center C) (Center O) ((↑(Radius C) ^ 2 - ↑(Radius O) ^ 2 + point_abs (Center C) (Center O) ^ 2) / (2 * point_abs (Center C) (Center O)))) := by{
    set r := ((↑(Radius C) ^ 2 - ↑(Radius O) ^ 2 + point_abs (Center C) (Center O) ^ 2) / (2 * point_abs (Center C) (Center O)))
    unfold q
    set a := Center C
    set b := Center O
    set c := go_along a b r
    set L := qLine_through a b
    have s3: Lies_on c L := by{
      unfold L c
      exact go_along_lies_on_qline_through a b r
    }
    symm
    exact is_foot_iff_on_perp_through p c L s3
  }
  suffices : point_abs q (Center C) ^ 2  - point_abs q (Center O) ^ 2 =
    ↑(Radius C) ^ 2  - ↑(Radius O) ^ 2 ↔
q = (go_along (Center C) (Center O) ((↑(Radius C) ^ 2 - ↑(Radius O) ^ 2 + point_abs (Center C) (Center O) ^ 2) / (2 * point_abs (Center C) (Center O))))

  · tauto

  set a := Center C
  set b := Center O
  set r := ((↑(Radius C) ^ 2 - ↑(Radius O) ^ 2 + point_abs a b ^ 2) / (2 * point_abs a b))
  set c := go_along a b r
  clear s1 s2
  have : point_abs q b = point_abs a b - point_abs q a := by{
    unfold in_between at h'
    rw[point_abs_symm q a]
    linarith
  }
  rw[this]
  clear this
  have : point_abs q a ^ 2 - (point_abs a b - point_abs q a) ^ 2 = 2* (point_abs a b) * (point_abs q a) - (point_abs a b)^2:= by{ring}
  rw[this]
  clear this
  have t1: point_abs a b ≠ 0 := by{
    unfold a b Concentric at *
    contrapose h
    simp at *
    exact abs_zero_imp_same (Center C) (Center O) h
  }
  have s3: 2 * point_abs a b * point_abs q a - point_abs a b ^ 2 = ↑(Radius C) ^ 2 - ↑(Radius O) ^ 2  ↔ point_abs q a = (↑(Radius C) ^ 2 - ↑(Radius O) ^ 2 + point_abs a b ^2)/(2*point_abs a b) := by{
    field_simp
    constructor
    · intro h
      linarith
    intro h
    linarith
  }
  suffices : point_abs q a = (↑(Radius C) ^ 2 - ↑(Radius O) ^ 2 + point_abs a b ^2)/(2*point_abs a b) ↔ q = c
  · tauto
  clear s3
  have ab: a ≠ b := by{unfold a b Concentric at *; assumption}
  obtain ⟨R,hR⟩ := colinear_go_along ab (in_between_imp_colinear h')
  rw[point_abs_symm, hR, go_along_abs1 ab]
  unfold r at *
  set r' := ((↑(Radius C) ^ 2 - ↑(Radius O) ^ 2 + point_abs (Center C) (Center O) ^ 2) / (2 * point_abs (Center C) (Center O)))
  have rr': r' = r := by{
    unfold r r'
    rfl
  }
  rw[rr']
  unfold c
  have : abs R = R := by{
    simp
    rw[hR] at h'
    exact (in_between_go_along ab h').1
  }
  rw[this]
  constructor
  · intro h
    rw[h]
  intro h
  exact go_along_inj ab h
}

#check Line_through
def PowLine {C O : CCircle}(h : ¬Concentric C O) : Line where
  range := {p | PowPoint p C = PowPoint p O}
  span := by{
    sorry
  }

lemma lies_on_powline{C O : CCircle}(h : ¬Concentric C O)(p : Point): Lies_on p (PowLine h) ↔ PowPoint p C = PowPoint p O := by{
  unfold Lies_on PowLine
  simp
}

/-and a quick version:-/

def qPowLine : CCircle → CCircle → Line :=
  fun C O ↦ if h: ¬Concentric C O then PowLine h else real_line

@[simp] lemma qpowline_simp{C O : CCircle}(h : ¬Concentric C O): qPowLine C O = PowLine h := by{
  unfold qPowLine
  simp [*]
}

lemma qpowline_symm(C O : CCircle): qPowLine O C = qPowLine C O := by{
  by_cases h : ¬Concentric C O
  have OC: ¬Concentric O C := by{
    unfold Concentric at *
    tauto
  }
  simp [*]
  ext t
  unfold PowLine
  simp
  tauto

  simp at *
  have h': Concentric O C := by{
    unfold Concentric at *
    tauto
  }
  unfold qPowLine
  simp [*]
}

lemma powline_symm{C O : CCircle}(h : ¬Concentric C O): PowLine h = PowLine (not_concentric_symm h) := by{
  rw[← qpowline_simp, ← qpowline_simp, qpowline_symm]
}

theorem powline_perp{C O : CCircle}(h : ¬Concentric C O): Perpendicular (qLine_through (Center C) (Center O)) (PowLine h) := by{
  sorry
}

lemma powline_unique{C O : CCircle}(h : ¬Concentric C O){p : Point}(hp : PowPoint p C = PowPoint p O): perp_through (qLine_through (Center C) (Center O)) p = PowLine h := by{
  symm
  apply perp_through_unique
  constructor
  · exact powline_perp h
  exact (lies_on_powline h p).2 hp
}

/-The powpoint of the intersection of two circle is the same, namely both zero.
Therefore we can make a few more lemmas:-/

lemma powline_intersection1{C O : CCircle}(h : ¬Concentric C O){p : Point}(hp : Lies_on_circle p C ∧ Lies_on_circle p O): Lies_on p (PowLine h) := by{
  apply (lies_on_powline h p).2
  rw[(powpoint_lies_on p C).1 hp.1, (powpoint_lies_on p O).1 hp.2]
}

lemma powline_intersection2{C O : CCircle}(h : ¬Concentric C O){p : Point}(hp : Lies_on_circle p C ∧ Lies_on_circle p O): perp_through (qLine_through (Center C) (Center O)) p = PowLine h := by{
  apply powline_unique
  rw[(powpoint_lies_on p C).1 hp.1, (powpoint_lies_on p O).1 hp.2]
}

lemma powline_intersection3{C O : CCircle}(h : ¬Concentric C O)(p q : Point)(hp : Lies_on_circle p C ∧ Lies_on_circle p O)(hq : Lies_on_circle q C ∧ Lies_on_circle q O)(pq : p ≠ q): Line_through pq = PowLine h := by{
  symm
  apply line_through_unique
  constructor
  · exact powline_intersection1 h hp
  exact powline_intersection1 h hq
}

/-in the case the circle are ctangent we have something nice-/
lemma powline_ctangent{C O : CCircle}(h : ¬Concentric C O)(h' : CTangent C O): Common_tangent h' = PowLine h := by{
  symm
  apply common_tangent_unique
  · contrapose h
    unfold PosRad Concentric at *
    simp at *
    obtain ⟨h1,h2⟩ := h
    rw[← ctangent_radius_zero_right h' h2, ← ctangent_radius_zero_left h' h1]

  constructor
  apply powline_intersection1
  constructor
  · exact ctangent_mem_left h'
  exact ctangent_mem_right h'

  exact powline_perp h
}

/-The cool thing about powlines is now that they are copunctal in the following sense:-/

def cnoncolinear(C O U : CCircle): Prop :=
  noncolinear (Center C) (Center O) (Center U)

lemma cnoncolinear_perm12 {C O U : CCircle} (h : cnoncolinear C O U) : cnoncolinear O C U := by{
  unfold cnoncolinear at *
  exact noncolinear_perm12 h
}

lemma cnoncolinear_perm13 {C O U : CCircle} (h : cnoncolinear C O U) : cnoncolinear U O C := by{
  unfold cnoncolinear at *
  exact noncolinear_perm13 h
}

lemma cnoncolinear_perm23 {C O U : CCircle} (h : cnoncolinear C O U) : cnoncolinear C U O := by{
  unfold cnoncolinear at *
  exact noncolinear_perm23 h
}

/-The existence of the circumcenter is a special case of the folowing now:-/

theorem powline_copunctal{C O U : CCircle}(h : cnoncolinear C O U): Copunctal (qPowLine C O) (qPowLine O U) (qPowLine U C) := by{
  refine copunctal_simp ?h ?h'
  refine lines_not_same_parallel (qPowLine C O) (qPowLine O U) (qPowLine U C) ?h.h
  contrapose h
  unfold cnoncolinear noncolinear
  simp at *
  by_cases disj: ¬(Center C ≠ Center O ∧ Center O ≠ Center U ∧ Center U ≠ Center C)
  simp at disj
  apply colinear_self
  tauto

  simp at disj
  obtain ⟨CO,OU,UC⟩ := disj
  have s1: Parallel (qLine_through (Center C) (Center O)) (qLine_through (Center O) (Center U)) := by{
    have t1: Perpendicular (Line_through CO) (qPowLine O U) := by{
      apply perp_parallel (qPowLine C O)
      have : ¬Concentric C O := by{
        unfold Concentric
        assumption
      }
      simp [this]
      rw[← qline_through_line_through]
      apply perp_symm
      exact powline_perp this
      assumption
    }
    simp [*] at *
    have t2: Perpendicular (Line_through OU) (qPowLine O U) := by{
      rw[← qline_through_line_through]
      have : ¬Concentric O U := by{
        unfold Concentric
        assumption
      }
      simp [this]
      exact powline_perp this
    }
    apply perp_symm at t1
    apply perp_symm at t2
    exact perp_perp (qPowLine O U) t1 t2
  }
  simp  [*] at s1
  apply (parallel_quot CO OU).1 at s1
  apply colinear_perm12
  apply (colinear_alt (Center O) (Center C) (Center U)).2
  have : ((Center O).x - (Center C).x) / ((Center O).x - (Center U).x) = -(((Center C).x - (Center O).x) / ((Center O).x - (Center U).x)) := by{ring}
  rw[this]
  clear this
  simpa

  have h0: (Center C ≠ Center O ∧ Center O ≠ Center U ∧ Center U ≠ Center C) := by{
    contrapose h
    unfold cnoncolinear noncolinear
    simp at *
    apply colinear_self
    tauto
  }
  obtain ⟨CO',OU',UC'⟩ := h0
  have CO: ¬Concentric C O := by{unfold Concentric;assumption}
  have OU: ¬Concentric O U := by{unfold Concentric;assumption}
  have UC: ¬Concentric U C := by{unfold Concentric;assumption}
  have s1: ¬Parallel (PowLine CO) (PowLine OU) := by{
    contrapose h
    unfold cnoncolinear noncolinear
    simp at *
    have u1: Parallel (Line_through CO') (Line_through OU') := by{
      apply perp_perp (PowLine CO)
      apply perp_symm
      rw[← qline_through_line_through]
      exact powline_perp CO

      apply parallel_perp (PowLine OU)
      apply parallel_symm
      assumption
      apply perp_symm
      rw[← qline_through_line_through]
      exact powline_perp OU
    }
    apply (parallel_quot CO' OU').1 at u1
    apply colinear_perm12
    apply (colinear_alt (Center O) (Center C) (Center U)).2
    have : ((Center O).x - (Center C).x) / ((Center O).x - (Center U).x) = -(((Center C).x - (Center O).x) / ((Center O).x - (Center U).x)) := by{ring}
    rw[this]
    clear this
    simpa
  }
  use Intersection s1
  simp [*]
  constructor
  · exact intersection_mem_left s1
  constructor
  · exact intersection_mem_right s1
  refine
    (lies_on_powline (of_eq_true (Eq.trans (congrArg Not (eq_false UC)) not_false_eq_true))
          (Intersection s1)).mpr
      ?h.right.right.a

  have t1: PowPoint (Intersection s1) O = PowPoint (Intersection s1) U := by{
    refine (lies_on_powline OU (Intersection s1)).mp ?_
    exact intersection_mem_right s1
  }
  have t2: PowPoint (Intersection s1) C = PowPoint (Intersection s1) O := by{
    refine (lies_on_powline CO (Intersection s1)).mp ?_
    exact intersection_mem_left s1
  }
  rw[t2,←t1]
}

/-_Therefore we can define the power of point center:-/

def PowCener{C O U : CCircle}(h : cnoncolinear C O U) : Point :=
  Line_center (powline_copunctal h)

--do the trivial stuff for this first, then fix the theorems beforehand.




/-
/-As explained earlier, the case when C and O are concentric is irrelevant and is just given for conveninence!-/

theorem powline_def(C O : CCircle)(p : Point)(CO: ¬Concentric C O) : PowPoint p C = PowPoint p O ↔ Lies_on p (PowLine C O) := by{
  constructor
  intro h
  unfold Concentric at CO
  let q := foot p (Line_through CO)
  let r := (go_along (Center C) (Center O) (((Radius C)^2-(Radius O)^2+(point_abs (Center C) (Center O))^2)/(2*(point_abs (Center C) (Center O)))))
  have s1: point_abs (Center C) q = ((Radius C)^2-(Radius O)^2+(point_abs (Center C) (Center O))^2)/(2*(point_abs (Center C) (Center O))) := by{
    have t1: point_abs (Center C) (Center O) ≠ 0 := by{
      contrapose CO
      simp at *
      exact abs_zero_imp_same (Center C) (Center O) CO
    }
    have t2: 2 * (point_abs (Center C) (Center O)) ≠ 0 := by{
      contrapose t1
      simp at *
      assumption
    }
    suffices goal: (Radius C)^2 - (point_abs (Center C) q)^2 = (Radius O)^2 - ((point_abs (Center C) q) - (point_abs (Center C) (Center O)))^2

    field_simp
    let x := point_abs (Center C) q
    have xdef: x = point_abs (Center C) q := rfl
    let d := point_abs (Center C) (Center O)
    have ddef : d = point_abs (Center C) (Center O) := rfl
    rw[← ddef, ← xdef] at goal
    rw[← ddef, ← xdef]
    rw[← ddef] at t2 t1
    clear xdef ddef
    have ff: x^2-(x-d)^2 + d^2= (Radius C)^2 - (Radius O)^2 +d^2 := by{linarith}
    have ee: x^2 -(x-d)^2 + d^2 = x * (2*d) := by{ring_nf}
    rw[←  ee, ff]
    rfl
    have perp1: perp_points q p q (Center C) := by{
      unfold q
      apply perp_points_perm_front; apply perp_points_perm_back; apply perp_points_perm_switch
      apply perp_points_foot
      exact line_through_mem_left CO
    }
    have perp2: perp_points q p q (Center O) := by{
      unfold q
      apply perp_points_perm_front; apply perp_points_perm_back; apply perp_points_perm_switch
      apply perp_points_foot
      exact line_through_mem_right CO
    }
    have p1: point_abs (Center C) q ^ 2 = point_abs p (Center C) ^ 2 - point_abs q p ^ 2 := by{
      rw[pythagoras_points perp1
      ring
    }
    have p2: point_abs (Center O) q ^ 2 = point_abs p (Center O) ^ 2 - point_abs q p ^ 2 := by{
      rw[pythagoras_points perp2]
      ring
    }
    nth_rw 1[p1]
    have : (point_abs (Center C) q - point_abs (Center C) (Center O)) ^ 2 = (point_abs (Center O) q)^2 := by{
      #check colinear_imp_in_between2
      have col: colinear (Center C) (Center O) q := by{
        have : Lies_on q (Line_through CO) := by{
          unfold q
          exact foot_on_line (Line_through CO) p
        }
        unfold Lies_on Line_through at this
        simp at this
        assumption
      }
      obtain h0|h0|h0 := colinear_imp_in_between2 (Center C) (Center O) q col
      unfold in_between at h0
      rw[← h0]
      ring_nf
      rw[point_abs_symm]

      swap
      unfold in_between at h0
      rw[point_abs_symm q (Center C)] at h0
      rw[← h0]
      rw[point_abs_symm (Center O) (Center C)]
      ring_nf
      rw[point_abs_symm q (Center O)]

      unfold in_between at h0
      sorry
      --omg pls kill me
    }
    rw[this]
    nth_rw 1[p2]
    unfold PowPoint at h
    linarith
  }
  sorry
  sorry
}
-/
