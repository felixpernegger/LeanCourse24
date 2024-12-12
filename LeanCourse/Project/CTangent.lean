import LeanCourse.Project.Tangents
import Mathlib

open Function Set Classical

noncomputable section

/-Here deal with Tangential Circles.
The required predicate will be called "CTangent" for "circle tangent" or something-/

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

lemma point_abs_ctangent_left{C O : CCircle}(h : CTangent C O) : point_abs (Center C) (CTangent_point h) = Radius C := by{
  exact point_abs_point_lies_on_circle (ctangent_mem_left h)
}

lemma point_abs_ctangent_right{C O : CCircle}(h : CTangent C O) : point_abs (Center O) (CTangent_point h) = Radius O := by{
  exact point_abs_point_lies_on_circle (ctangent_mem_right h)
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

  #check lies_on_foot
}

theorem ctangent_colinear{C O : CCircle}(h : CTangent C O): colinear (Center C) (Center O) (CTangent_point h) := by{
  sorry
}

/-Now the tangent through CTangent_point C is the same as O:-/

lemma ctangent_tangent_through{C O : CCircle}(h : CTangent C O)(hC: PosRad C)(hO: PosRad O): Tangent_through (ctangent_point_mem_left h) = Tangent_through (ctangent_point_mem_right h) := by{
  sorry
}
