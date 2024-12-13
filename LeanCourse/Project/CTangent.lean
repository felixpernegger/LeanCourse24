import LeanCourse.Project.Tangents
import Mathlib

open Function Set Classical

noncomputable section

/-Here deal with Tangential Circles.
The required predicate will be called "CTangent" for "circle tangent" or something-/

def Concentric(C O : CCircle) : Prop :=
  Center C = Center O

lemma concentric_symm{C O : CCircle}(h : Concentric C O): Concentric O C := by{
  unfold Concentric at *
  tauto
}

/-Fot the ifrst few things we basically copy the Tangents section-/

def CTangent(C O : CCircle) : Prop :=
  Tangential C.range O.range

def CTangent_point{C O : CCircle}(h : CTangent C O): Point := by{
  unfold CTangent at h
  exact (Tangential_point h)
}

lemma ctangent_mem_left{C O : CCircle}(h : CTangent C O): Lies_on_circle (CTangent_point h) C := by{
  unfold Lies_on_circle CTangent_point
  exact (tangential_point_in_sets h).1
}

lemma ctangent_mem_right{C O : CCircle}(h : CTangent C O): Lies_on_circle (CTangent_point h) O := by{
  unfold Lies_on_circle CTangent_point
  exact (tangential_point_in_sets h).2
}

theorem ctangent_point_unique{C O : CCircle}(p : Point)(h : CTangent C O)(hp : Lies_on_circle p C ∧ Lies_on_circle p O): p = CTangent_point h := by{
  unfold Lies_on_circle CTangent_point CTangent at *
  exact tangential_point_unique h hp
}

lemma ctangent_symm{C O : CCircle}(h : CTangent C O) : CTangent O C := by{
  unfold CTangent Tangential at *
  rwa[inter_comm O.range C.range]
}

lemma ctangent_point_symm{C O : CCircle}(h : CTangent C O) : CTangent_point (ctangent_symm h) = CTangent_point h := by{
  apply ctangent_point_unique
  constructor
  · exact ctangent_mem_right (ctangent_symm h)
  exact ctangent_mem_left (ctangent_symm h)
}

lemma point_abs_ctangent_left{C O : CCircle}(h : CTangent C O) : point_abs (Center C) (CTangent_point h) = Radius C := by{
  exact point_abs_point_lies_on_circle (ctangent_mem_left h)
}

lemma point_abs_ctangent_right{C O : CCircle}(h : CTangent C O) : point_abs (Center O) (CTangent_point h) = Radius O := by{
  exact point_abs_point_lies_on_circle (ctangent_mem_right h)
}

lemma concentric_ctangent{C O : CCircle}(h : Concentric C O)(h': CTangent C O): ¬PosRad C ∧ ¬PosRad O := by{
  have s1: CTangent_point h' = Center C := by{
    let p := reflection_point_point (CTangent_point h') (Center C)
    have t0 : Radius C = Radius O := by{
      have t: point_abs (Center C) (CTangent_point h') = Radius C := by{
        exact point_abs_ctangent_left h'
      }
      have : point_abs (Center O) (CTangent_point h') = Radius O := by{
        have OC: CTangent O C := by{exact ctangent_symm h'}
        have : CTangent_point h' = CTangent_point OC := by{
          exact ctangent_point_symm OC
        }
        rw[this]
        exact point_abs_ctangent_left OC
      }
      unfold Concentric at h
      rw[h] at t
      rw[t] at this
      ext
      assumption
    }
    have t1: point_abs (Center C) p = point_abs (Center C) (CTangent_point h') := by{
      have : Center C = pmidpoint p (CTangent_point h') := by{
        unfold p
        symm
        exact reflection_point_point_pmidpoint (CTangent_point h') (Center C)
      }
      rw [this, pmidpoint_abs_right, pmidpoint_symm, pmidpoint_abs_right, point_abs_symm]
    }
    have s2: point_abs (Center C) (CTangent_point h') = Radius C := by{
      exact point_abs_ctangent_left h'
    }
    rw[s2] at t1
    have s3: Lies_on_circle p C := by{exact point_on_circle_simp t1}
    have s4: Lies_on_circle p O := by{
      unfold Concentric at h
      rw[t0, h] at t1
      exact point_on_circle_simp t1
    }
    have s5: p = CTangent_point h' := by{
      apply ctangent_point_unique
      constructor
      · assumption
      assumption
    }
    have : point_abs p (CTangent_point h') = 0 := by{
      rw[s5]
      exact point_abs_self (CTangent_point h')
    }
    unfold p at this
    rw[reflection_point_abs2] at this
    simp at this
    exact abs_zero_imp_same (CTangent_point h') (Center C) this
  }
  constructor
  have q1: Lies_on_circle (CTangent_point h') C := by{exact ctangent_mem_left h'}
  have q2: point_abs (Center C) (CTangent_point h') = Radius C := by{exact point_abs_ctangent_left h'}
  rw[s1] at q2
  have : Radius C = 0 := by{
    symm
    have : point_abs (Center C) (Center C) = 0 := by{exact point_abs_self (Center C)}
    rw[this] at q2
    ext
    assumption
  }
  unfold PosRad
  simpa

  have q1: Lies_on_circle (CTangent_point h') O := by{exact ctangent_mem_right h'}
  have q2: point_abs (Center O) (CTangent_point h') = Radius O := by{
    exact point_abs_point_lies_on_circle q1
  }
  unfold PosRad
  simp
  ext
  rw[← q2]
  simp
  unfold Concentric at h
  rw[←h,s1]
  exact point_abs_self (Center C)
}


lemma ctangent_point_lies_on{C O : CCircle}(h: CTangent C O) : Lies_on (CTangent_point h) (qLine_through (Center C) (Center O)) := by{
  by_cases hC : PosRad C
  swap
  unfold PosRad at hC
  simp at hC
  have : CTangent_point h = Center C := by{
    exact (lies_on_radius_zero hC (ctangent_mem_left h))
  }
  rw[this]
  exact qline_through_mem_left (Center C) (Center O)
  by_cases hO : PosRad O
  swap
  unfold PosRad at hO
  simp at hO
  have : CTangent_point h = Center O := by{
    exact (lies_on_radius_zero hO (ctangent_mem_right h))
  }
  rw[this]
  exact qline_through_mem_right (Center C) (Center O)
  have CO : ¬Concentric C O := by{
    by_contra h0
    have : ¬PosRad C ∧ ¬PosRad O := by{exact concentric_ctangent h0 h}
    tauto
  }
  unfold Concentric at CO
  have s1: qLine_through (Center C) (Center O) = Line_through CO := by{exact qline_through_line_through CO}
  rw[s1]
  clear s1
  let p := reflection_point_line (CTangent_point h) (Line_through CO)
  have hp : p = CTangent_point h := by{
    apply ctangent_point_unique
    let r := point_line_abs (CTangent_point h) (Line_through CO)
    have hr: point_line_abs p (Line_through CO) = r := by{
      unfold p
      rw[reflection_point_line_abs]
    }
    constructor
    refine point_on_circle_simp ?hp.left.h
    have perp: perp_points (foot p (Line_through CO)) (Center C) (foot p (Line_through CO)) p := by{
      apply perp_points_perm_front
      apply perp_points_perm_back
      apply perp_points_foot
      exact line_through_mem_left CO
    }
    rw[pythagoras_points_bc perp]
    unfold point_line_abs at hr
    rw[hr]
    unfold r
    have perp2: perp_points (foot (CTangent_point h) (Line_through CO)) (Center C) (foot (CTangent_point h) (Line_through CO)) (CTangent_point h) := by{
      apply perp_points_perm_front
      apply perp_points_perm_back
      apply perp_points_foot
      exact line_through_mem_left CO
    }
    unfold p
    simp
    unfold point_line_abs
    rw[← pythagoras_points_bc perp2]
    exact point_abs_ctangent_left h

    refine point_on_circle_simp ?hp.right.h
    have perp: perp_points (foot p (Line_through CO)) (Center O) (foot p (Line_through CO)) p := by{
      apply perp_points_perm_front
      apply perp_points_perm_back
      apply perp_points_foot
      exact line_through_mem_right CO
    }
    rw[pythagoras_points_bc perp]
    unfold point_line_abs at hr
    rw[hr]
    unfold r
    have perp2: perp_points (foot (CTangent_point h) (Line_through CO)) (Center O) (foot (CTangent_point h) (Line_through CO)) (CTangent_point h) := by{
      apply perp_points_perm_front
      apply perp_points_perm_back
      apply perp_points_foot
      exact line_through_mem_right CO
    }
    unfold p
    simp
    unfold point_line_abs
    rw[← pythagoras_points_bc perp2]
    exact point_abs_ctangent_right h
  }
  unfold p at hp
  exact (reflection_point_line_on_line (CTangent_point h) (Line_through CO)).1 hp
}

theorem ctangent_colinear{C O : CCircle}(h : CTangent C O): colinear (Center C) (Center O) (CTangent_point h) := by{
  have cent: Lies_on (CTangent_point h) (qLine_through (Center C) (Center O)) := by{exact ctangent_point_lies_on h}
  by_cases hC: PosRad C
  by_cases hO: PosRad O
  have CO : ¬Concentric C O := by{
    by_contra h0
    have : ¬PosRad C ∧ ¬PosRad O := by{exact concentric_ctangent h0 h}
    tauto
  }
  unfold Concentric at CO
  have s1: qLine_through (Center C) (Center O) = Line_through CO := by{exact qline_through_line_through CO}
  rw[s1] at cent
  unfold Lies_on Line_through at cent
  simpa

  have : (CTangent_point h) = Center O := by{
    unfold PosRad at hO
    simp at hO
    exact lies_on_radius_zero hO (ctangent_mem_right h)
  }
  apply colinear_self
  tauto

  have : (CTangent_point h) = Center C := by{
    unfold PosRad at hC
    simp at hC
    exact lies_on_radius_zero hC (ctangent_mem_left h)
  }
  apply colinear_self
  tauto
}

/-Now the tangent through CTangent_point C is the same as O:-/

lemma ctangent_tangent_through{C O : CCircle}(h : CTangent C O)(hC: PosRad C)(hO: PosRad O): Tangent_through (ctangent_mem_left h) = Tangent_through (ctangent_mem_right h) := by{
  --for simplicity
  have sC: Lies_on_circle (CTangent_point h) C := by{exact ctangent_mem_left h}
  have sO: Lies_on_circle (CTangent_point h) O := by{exact ctangent_mem_right h}
  have s1 : Center_line (sC) = Center_line (sO) := by{
    apply lines_eq_ex
    use (Center C)
    use CTangent_point h
    constructor
    exact Ne.symm (posrad_not_center hC sC)
    constructor
    exact center_on_center_line sC
    constructor
    swap
    constructor
    exact point_on_center_line sC
    exact point_on_center_line sO

    have t1: ¬Concentric C O := by{
      by_contra h0
      have : ¬PosRad C ∧ ¬PosRad O := by{exact concentric_ctangent h0 h}
      tauto
    }
    unfold Concentric at t1
    have : Lies_on (CTangent_point h) (qLine_through (Center C) (Center O)) := by{exact ctangent_point_lies_on h}
    simp [*] at this
    unfold Lies_on Center_line Line_through at *
    simp at *
    have : qLine_through (Center O) (CTangent_point h) = Line_through t1 := by{
      apply line_through_unique
      constructor
      swap
      exact qline_through_mem_left (Center O) (CTangent_point h)
      have : (Center O) ≠ (CTangent_point h) := by{
        contrapose hO
        unfold PosRad
        simp at *
        have : point_abs (Center O) (CTangent_point h) = Radius O := by{exact point_abs_ctangent_right h}
        rw[hO] at this
        rw[point_abs_self] at this
        ext
        tauto
      }
      unfold qLine_through
      simp [*]
      unfold Lies_on Line_through
      simp
      apply colinear_perm13
      apply colinear_perm23
      exact ctangent_colinear h
    }
    rw[this]
    clear this
    unfold Line_through
    simp
    apply colinear_self
    tauto
  }
  have par: Parallel (Tangent_through (ctangent_mem_left h)) (Tangent_through (ctangent_mem_right h)) := by{
    apply perp_perp (Center_line sC)
    apply perp_symm
    exact tangent_through_is_perp sC hC

    rw[s1]
    apply perp_symm
    exact tangent_through_is_perp sO hO
  }
  apply (parallel_def (Tangent_through (ctangent_mem_left h)) (Tangent_through (ctangent_mem_right h))).1 at par
  obtain par|par := par
  swap
  ext
  rw[par]

  exfalso
  have : (CTangent_point h) ∈ (Tangent_through (ctangent_mem_left h)).range ∩ (Tangent_through (ctangent_mem_right h)).range := by{
    refine mem_inter ?ha ?hb
    have : Lies_on (CTangent_point h) (Tangent_through (ctangent_mem_left h)) := by{exact point_lies_on_tangent_through (ctangent_mem_left h)}
    unfold Lies_on at this
    assumption

    have : Lies_on (CTangent_point h) (Tangent_through (ctangent_mem_right h)) := by{exact point_lies_on_tangent_through (ctangent_mem_right h)}
    unfold Lies_on at this
    assumption
  }
  rw[par] at this
  contradiction
}

/-We can therefore define a commong tangent to the two circles.
To make it as general as possible, we use following approach:-/

def Common_tangent{C O : CCircle}(h : CTangent C O) : Line :=
  perp_through (qLine_through (Center C) (Center O)) (CTangent_point h)

--do a few more properties of the common tangent, in particular use the result above for center lines and stuff
--then characerize ctangent circles (not too bad)
