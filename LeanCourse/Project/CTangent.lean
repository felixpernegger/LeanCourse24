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
    #check reflection_point_point
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
  have q2: point_abs (Center O) (CTangent_point h') = Radius O := by{sorry}
  sorry
}


--theorem ctangent_perp{C O : CCircle}(h : CTangent C O)(hC : PosRad C)(hO : PosRad O) : Perpendicular

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
  sorry
  #check lies_on_foot
}

theorem ctangent_colinear{C O : CCircle}(h : CTangent C O): colinear (Center C) (Center O) (CTangent_point h) := by{
  sorry
}

/-Now the tangent through CTangent_point C is the same as O:-/

lemma ctangent_tangent_through{C O : CCircle}(h : CTangent C O)(hC: PosRad C)(hO: PosRad O): Tangent_through (ctangent_point_mem_left h) = Tangent_through (ctangent_point_mem_right h) := by{
  sorry
}
