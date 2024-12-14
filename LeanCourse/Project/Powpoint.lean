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

lemma powline_intersection3{C O : CCircle}(h : ¬Concentric C O){p : Point}{q : Point}(hp : Lies_on_circle p C ∧ Lies_on_circle p O)(hq : Lies_on_circle q C ∧ Lies_on_circle q O)(pq : p ≠ q): Line_through pq = PowLine h := by{
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
      rw[pythagoras_points perp1]
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
