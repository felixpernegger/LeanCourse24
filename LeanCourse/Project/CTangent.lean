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

lemma ctangent_radius_zero_left{C O : CCircle}(h : CTangent C O)(hC: Radius C = 0): CTangent_point h = Center C := by{
  exact lies_on_radius_zero hC (ctangent_mem_left h)
}

lemma ctangent_radius_zero_right{C O : CCircle}(h : CTangent C O)(hO: Radius O = 0): CTangent_point h = Center O := by{
  exact lies_on_radius_zero hO (ctangent_mem_right h)
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

lemma ctangent_point_common_tangent{C O : CCircle}(h : CTangent C O) : Lies_on (CTangent_point h) (Common_tangent h) := by{
  unfold Common_tangent
  exact point_lies_on_perp_through (qLine_through (Center C) (Center O)) (CTangent_point h)
}

lemma common_tangent_perp{C O : CCircle}(h : CTangent C O) : Perpendicular (qLine_through (Center C) (Center O)) (Common_tangent h) := by{
  unfold Common_tangent
  exact perp_through_is_perp (qLine_through (Center C) (Center O)) (CTangent_point h)
}

lemma common_tangent_symm{C O : CCircle}(h : CTangent C O) : Common_tangent (ctangent_symm h) = Common_tangent h := by{
  unfold Common_tangent
  rw[qline_through_symm, ctangent_point_symm h]
}

/-The common tangent as we proved before is now the same as the respective tangents:-/
/-at least if we use posrad-/

lemma common_tangent_left{C O : CCircle}(h : CTangent C O)(hC : PosRad C): Common_tangent h = Tangent_through (ctangent_mem_left h) := by{
  have CO: Center C ≠ Center O := by{
    by_contra p0
    have : ¬PosRad C ∧ ¬PosRad O := by{exact concentric_ctangent p0 h}
    tauto
  }
  by_cases hO: PosRad O
  have s1: Tangent_through (ctangent_mem_left h) = Tangent_through (ctangent_mem_right h) := by{exact ctangent_tangent_through h hC hO}
  unfold Common_tangent
  simp [CO]
  have goal: Line_through CO = Center_line (ctangent_mem_left h) := by{
    apply center_line_unique hC
    constructor
    exact line_through_mem_left CO
    have : Lies_on (CTangent_point h) (qLine_through (Center C) (Center O)) := by{exact ctangent_point_lies_on h}
    simp [CO] at this
    assumption
  }
  rw[goal]
  apply tangent_through_unique
  assumption
  exact point_lies_on_perp_through (Center_line (ctangent_mem_left h)) (CTangent_point h)
  exact perp_is_tangent (ctangent_mem_left h)

  unfold PosRad at hO
  simp at hO
  have s1: CTangent_point h = Center O := by{
    exact ctangent_radius_zero_right h hO
  }
  apply tangent_through_unique
  assumption
  unfold Common_tangent
  exact point_lies_on_perp_through (qLine_through (Center C) (Center O)) (CTangent_point h)

  have : Common_tangent h = perp_through (Center_line (ctangent_mem_left h)) (CTangent_point h) := by{
    unfold Common_tangent
    simp [CO]
    have : Line_through CO = Center_line (ctangent_mem_left h) := by{
      apply center_line_unique hC
      constructor
      exact line_through_mem_left CO
      unfold Line_through Lies_on
      simp
      exact ctangent_colinear h
    }
    rw[this]
  }
  rw[this]
  exact perp_is_tangent (ctangent_mem_left h)
}

lemma common_tangent_right{C O : CCircle}(h : CTangent C O)(hO : PosRad O): Common_tangent h = Tangent_through (ctangent_mem_right h) := by{
  have h': CTangent O C := by{exact ctangent_symm h}
  have : Common_tangent h = Common_tangent h' := by{exact common_tangent_symm h'}
  rw[this]
  have : CTangent_point h = CTangent_point h' := by{exact ctangent_point_symm h'}
  have : Tangent_through (ctangent_mem_right h) = Tangent_through (ctangent_mem_left h') := by{
    apply tangent_through_unique
    assumption
    rw[← this]
    exact point_lies_on_tangent_through (ctangent_mem_right h)
    exact tangent_through_is_tangent (ctangent_mem_right h)
  }
  rw[this]
  exact (common_tangent_left h' hO)
}

/-So its perp to the respective center_lines:-/

lemma common_tangent_perp_left{C O : CCircle}(h : CTangent C O)(hC : PosRad C): Perpendicular (Common_tangent h) (Center_line (ctangent_mem_left h)) := by{
  rw[common_tangent_left]
  exact tangent_through_is_perp (ctangent_mem_left h) hC
  assumption
}

lemma common_tangent_perp_right{C O : CCircle}(h : CTangent C O)(hO : PosRad O): Perpendicular (Common_tangent h) (Center_line (ctangent_mem_right h)) := by{
  rw[common_tangent_right]
  exact tangent_through_is_perp (ctangent_mem_right h) hO
  assumption
}

/-we finish off with following characterization:-/

lemma common_tangent_unique{C O : CCircle}{L : Line}(h: CTangent C O)(h' : PosRad C ∨ PosRad O)(hL : Lies_on (CTangent_point h) L ∧ (Perpendicular (qLine_through (Center C) (Center O)) L)) : L = Common_tangent h := by{
  obtain ⟨hL1,hL2⟩ := hL
  obtain h'|h' := h'
  rw[common_tangent_left]
  apply tangent_through_unique
  assumption
  exact hL1

  have t1: Center C ≠ Center O := by{
    contrapose h'
    simp at *
    have : Concentric C O := by{exact h'}
    have : ¬PosRad C ∧ ¬PosRad O := by{exact concentric_ctangent this h}
    tauto
  }
  simp [*] at *
  have : Line_through t1 = Center_line (ctangent_mem_left h) := by{
    apply center_line_unique h'
    constructor
    exact line_through_mem_left t1
    unfold Lies_on Line_through
    simp
    exact ctangent_colinear h
  }
  have : L = (perp_through (Center_line (ctangent_mem_left h)) (CTangent_point h)) := by{
    apply perp_through_unique
    constructor
    rw[← this]
    assumption
    assumption
  }
  rw[this]
  apply perp_is_tangent
  assumption



  rw[common_tangent_right]
  apply tangent_through_unique
  assumption
  exact hL1

  have t1: Center C ≠ Center O := by{
    contrapose h'
    simp at *
    have : Concentric C O := by{exact h'}
    have : ¬PosRad C ∧ ¬PosRad O := by{exact concentric_ctangent this h}
    tauto
  }
  simp [*] at *
  have : Line_through t1 = Center_line (ctangent_mem_right h) := by{
    apply center_line_unique h'
    constructor
    exact line_through_mem_right t1
    unfold Lies_on Line_through
    simp
    exact ctangent_colinear h
  }
  have : L = (perp_through (Center_line (ctangent_mem_right h)) (CTangent_point h)) := by{
    apply perp_through_unique
    constructor
    rw[← this]
    assumption
    assumption
  }
  rw[this]
  apply perp_is_tangent
  assumption
}

/-To have to  deal a bit less with predicates, we introduce quick versions of our stuff:-/

def qCenter_line : CCircle → Point → Line :=
  fun C p ↦ qLine_through (Center C) p

def qTangent_through : CCircle → Point → Line :=
  fun C p ↦ if h: Lies_on_circle p C then (Tangent_through h) else (perp_through (qCenter_line C p) p)

def qCTangent_point : CCircle → CCircle → Point :=
  fun C O ↦ if h: CTangent C O then (CTangent_point h) else pmidpoint (Center C) (Center O)

def qCommon_tangent : CCircle → CCircle → Line :=
  fun C O ↦ (perp_through (qLine_through (Center C) (Center O)) (qCTangent_point C O))

@[simp] lemma qcenter_line_simp{C : CCircle}{p : Point}(h : Lies_on_circle p C): qCenter_line C p = Center_line h := by{
  unfold qCenter_line Center_line
  rfl
}

@[simp] lemma qtangent_through_simp{C : CCircle}{p : Point}(h : Lies_on_circle p C): qTangent_through C p = Tangent_through h := by{
  unfold qTangent_through
  simp [*]
}

@[simp] lemma qctangent_point_simp{C O : CCircle}(h : CTangent C O): qCTangent_point C O = CTangent_point h := by{
  unfold qCTangent_point
  simp [*]
}

@[simp] lemma qcommon_tangent_simp{C O : CCircle}(h : CTangent C O): qCommon_tangent C O = Common_tangent h := by{
  unfold Common_tangent qCommon_tangent
  simp [*]
}

lemma qcenter_line_center(C : CCircle)(p : Point): Lies_on (Center C) (qCenter_line C p) := by{
  unfold qCenter_line
  exact qline_through_mem_left (Center C) p
}

lemma qcenter_line_point(C : CCircle)(p : Point): Lies_on p (qCenter_line C p) := by{
  unfold qCenter_line
  exact qline_through_mem_right (Center C) p
}

lemma qtangent_through_point(C : CCircle)(p : Point): Lies_on p (qTangent_through C p) := by{
  unfold qTangent_through
  by_cases h0: Lies_on_circle p C
  simp [*]
  exact point_lies_on_tangent_through (of_eq_true (eq_true h0))
  simp [*]
  exact point_lies_on_perp_through (qCenter_line C p) p
}

lemma qctangent_point_symm(C O : CCircle): qCTangent_point O C = qCTangent_point C O := by{
  unfold qCTangent_point
  by_cases h : CTangent C O
  have h': CTangent O C := by{exact ctangent_symm h}
  simp [*]
  exact ctangent_point_symm (of_eq_true (eq_true h))

  have h': ¬CTangent O C := by{
    by_contra p0
    apply ctangent_symm at p0
    contradiction
  }
  simp [*]
  exact pmidpoint_symm (Center C) (Center O)
}

lemma qcommon_tangent_symm(C O : CCircle) : qCommon_tangent O C = qCommon_tangent C O := by{
  unfold qCommon_tangent
  rw[qline_through_symm (Center C) (Center O), qctangent_point_symm C O]
}

/-Now we want to characterize ctangent circles.
This isnt super nice, because there are two different cases:
The circles are tangent "from the outside" or from the inside. Therefore we first introduce some
more predicates. First we will with the edge case of one circle lying of the other:-/

lemma ctangent_radius_zero{C O : CCircle}(h : Lies_on_circle (Center O) C): CTangent C O ↔ Radius O = 0 := by{
  constructor
  intro h'
  sorry

  intro h'
  unfold CTangent Tangential
  by_contra h0
  by_cases h1: (C.range ∩ O.range).encard < 1
  have : (C.range ∩ O.range) = ∅ := by{sorry}
  sorry
  sorry
}

/-FINISH THIS OMG THIS IS HORRIBLE-/
