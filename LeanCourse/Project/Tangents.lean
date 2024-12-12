import LeanCourse.Project.qObject
import Mathlib

open Function Set Classical

noncomputable section

/-Here we prove a few things about tangents (on circles). Unfortunately, we cannot yet prove thales theorem
which is needed for constructing a tangents through a give point to a circle-/

/-As tangent inthe vast majority of cases actually means tangent line to circle, we just use the predicate Tangent-/

def Tangent(L : Line)(C : CCircle) : Prop :=
  Tangential L.range C.range

def Tangent_point{L : Line}{C : CCircle}(h : Tangent L C): Point := by{
  unfold Tangent at h
  exact (Tangential_point h)
}

/-This does what we want:-/

lemma tangent_point_on_line{L : Line}{C : CCircle}(h : Tangent L C): Lies_on (Tangent_point h) L := by{
  unfold Lies_on Tangent_point
  exact (tangential_point_in_sets h).1
}

lemma tangent_point_on_circle{L : Line}{C : CCircle}(h : Tangent L C): Lies_on_circle (Tangent_point h) C := by{
  unfold Lies_on_circle Tangent_point
  exact (tangential_point_in_sets h).2
}

/-And it's unique:-/

theorem tangent_point_unique{L : Line}{C : CCircle}(p : Point)(h : Tangent L C)(hp: Lies_on p L ∧ Lies_on_circle p C): p = Tangent_point h := by{
  unfold Lies_on Tangent_point Lies_on_circle Tangent at *
  exact tangential_point_unique h hp
}

/-therefore the distance on the tangent point is the radius of the circle to the center:-/

lemma point_abs_tangent_point{L : Line}{C : CCircle}(h : Tangent L C) : point_abs (Center C) (Tangent_point h) = Radius C := by{
  refine point_abs_point_lies_on_circle (Tangent_point h) ?h
  exact tangent_point_on_circle h
}

/-Also note:-/
lemma tangent_point_foot{L : Line}{C : CCircle}(h : Tangent L C) : Tangent_point h = foot (Center C) L := by{
  symm
  apply tangent_point_unique
  constructor
  · exact foot_on_line L (Center C)
  refine point_on_circle_simp ?hp.right.h
  apply le_antisymm
  by_contra p0
  simp at *
  have s1: point_line_abs (Center C) L < point_abs (Center C) (Tangent_point h) := by{
    have t1: point_line_abs (Center C) L ≤ point_abs (Center C) (Tangent_point h) := by{
      exact point_line_abs_leq_point_abs (Center C) (Tangent_point h) (tangent_point_on_line h)
    }
    have t2: point_line_abs (Center C) L ≠ point_abs (Center C) (Tangent_point h) := by{
      contrapose p0
      simp at *
      symm at p0
      have : Tangent_point h = foot (Center C) L := by{
        exact (point_line_abs_eq_point_abs_iff (Center C) (Tangent_point h) L (tangent_point_on_line h)).1 p0
      }
      rw[← this, @point_abs_tangent_point]
      rfl
    }
    contrapose t2
    simp at *
    linarith
  }
  have s2: point_abs (Center C) (Tangent_point h) = Radius C := by{
    exact point_abs_tangent_point h
  }
  rw[s2] at s1
  unfold point_line_abs at s1
  have : ↑(Radius C) < ↑(Radius C) := by{exact gt_trans s1 p0}
  contrapose this
  simp

  by_contra h0
  simp at *
  let u := √(↑(Radius C)^2 -(point_abs (Center C) (foot (Center C) L))^2)
  have upos : 0 < u := by{
    unfold u
    simp
    have : 0 ≤ point_abs (Center C) (foot (Center C) L) := by{exact point_abs_pos (Center C) (foot (Center C) L)}
    nlinarith
  }
  obtain ⟨a,b,ah,bh,ab⟩ := ex_points_on_li
  let p := go_along
}

/-Now an important theorem:

A line is tangent to a circle, iff the foot of the center of the Circle lies on the Circle: (if this isnt clear, draw a picture):-/

theorem line_tangent_iff(L : Line)(C : CCircle): Tangent L C ↔ Lies_on_circle (foot (Center C) L) C := by{
  constructor
  intro h
  refine point_on_circle_simp ?mp.h
  rw[← tangent_point_foot h]
  exact point_abs_tangent_point h

  intro h
  by_contra h0
  unfold Tangent at h0
  unfold Tangential at h0
  have : 1 < (L.range ∩ C.range).encard  ∨ (L.range ∩ C.range).encard < 1 := by{exact lt_or_gt_of_ne fun a ↦ h0 (id (Eq.symm a))}
  clear h0
  obtain h0|h0 := this
  simp at h0
  obtain ⟨a,b,ah,bh,ab⟩ := Set.one_lt_encard_iff.1 h0
  have ac: Lies_on_circle a C := by{
    unfold Lies_on_circle
    exact mem_of_mem_inter_right ah
  }
  have bc: Lies_on_circle b C := by{
    unfold Lies_on_circle
    exact mem_of_mem_inter_right bh
  }
  have ad: point_abs (Center C) a = Radius C := by{exact point_abs_point_lies_on_circle a ac}
  have bd: point_abs (Center C) b = Radius C := by{exact point_abs_point_lies_on_circle b bc}
  have g: point_abs (Center C) (foot (Center C) L) = Radius C := by{exact point_abs_point_lies_on_circle (foot (Center C) L) h}
  have aL : Lies_on a L := by{unfold Lies_on; exact mem_of_mem_inter_left ah}
  have bL : Lies_on b L := by{unfold Lies_on; exact mem_of_mem_inter_left bh}
  have eor: a ≠ Center C ∨ b ≠ Center C := by{exact Ne.ne_or_ne (Center C) ab}
  obtain p0|p0 := eor
  have : point_line_abs (Center C) L < point_abs (Center C) a := by{
    have t1: point_line_abs (Center C) L ≤ point_abs (Center C) a := by{
      exact point_line_abs_leq_point_abs (Center C) a aL
    }
    have t2: point_line_abs (Center C) L ≠ point_abs (Center C) a := by{
      by_contra q0
      symm at q0
      apply (point_line_abs_eq_point_abs_iff (Center C) a L aL).1 at q0
      rw[q0] at ab ad
      have : point_line_abs (Center C) L < point_abs (Center C) b := by{
        have s1:  point_line_abs (Center C) L ≤ point_abs (Center C) b := by{
          exact point_line_abs_leq_point_abs (Center C) b bL
        }
        have s2: point_abs (Center C) b ≠ point_line_abs (Center C) L := by{
          contrapose ab
          simp at *
          symm
          exact (point_line_abs_eq_point_abs_iff (Center C) b L bL).mp ab
        }
        contrapose s2
        simp at *
        linarith
      }
      unfold point_line_abs at this
      rw[bd, ad] at this
      linarith
    }
    contrapose t2
    simp at *
    linarith
  }
  unfold point_line_abs at this
  rw[g, ad] at this
  linarith

  have : point_line_abs (Center C) L < point_abs (Center C) b := by{
    have t1: point_line_abs (Center C) L ≤ point_abs (Center C) b := by{
      exact point_line_abs_leq_point_abs (Center C) b bL
    }
    have t2: point_line_abs (Center C) L ≠ point_abs (Center C) b := by{
      by_contra q0
      symm at q0
      apply (point_line_abs_eq_point_abs_iff (Center C) b L bL).1 at q0
      rw[q0] at ab bd
      have : point_line_abs (Center C) L < point_abs (Center C) a := by{
        have s1:  point_line_abs (Center C) L ≤ point_abs (Center C) a := by{
          exact point_line_abs_leq_point_abs (Center C) a aL
        }
        have s2: point_abs (Center C) a ≠ point_line_abs (Center C) L := by{
          contrapose ab
          simp at *
          exact (point_line_abs_eq_point_abs_iff (Center C) a L aL).mp ab
        }
        contrapose s2
        simp at *
        linarith
      }
      unfold point_line_abs at this
      rw[bd, ad] at this
      linarith
    }
    contrapose t2
    simp at *
    linarith
  }
  unfold point_line_abs at this
  rw[g, bd] at this
  linarith

  have footbad: (foot (Center C) L) ∈ (L.range ∩ C.range) := by{
    constructor
    suffices : Lies_on (foot (Center C) L) L
    · unfold Lies_on at this
      assumption
    exact foot_on_line L (Center C)

    unfold Lies_on_circle at h
    assumption
  }
  contrapose h0
  simp
  use foot (Center C) L
}
