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
  have weirdnonneg: 0 ≤ ↑(Radius C) ^ 2 - point_abs (Center C) (foot (Center C) L) ^ 2 := by{
    have : 0 ≤ point_abs (Center C) (foot (Center C) L) := by{exact point_abs_pos (Center C) (foot (Center C) L)}
    simp [*]
    nlinarith
  }
  have upos : 0 < u := by{
    unfold u
    simp
    have : 0 ≤ point_abs (Center C) (foot (Center C) L) := by{exact point_abs_pos (Center C) (foot (Center C) L)}
    nlinarith
  }
  obtain ⟨a,ah1,ah2⟩ := ex_different_point_on_line (foot (Center C) L) L
  let p := go_along (foot (Center C) L) a u
  let q := go_along (foot (Center C) L) a (-u)
  have pq: p ≠ q := by{
    by_contra p0
    have : u = 0 := by{
      unfold p q go_along p_scal_mul padd at p0
      simp at p0
      have : (dir (foot (Center C) L) a).x ≠ (0:ℂ) := by{
        contrapose ah2
        simp at *
        have : pabs (dir (foot (Center C) L) a) = 0 := by{
          unfold pabs
          rw[ah2]
          simp
        }
        symm
        exact (dir_zero (foot (Center C) L) a).1 this
      }
      have br: -(↑u * (dir (foot (Center C) L) a).x) = ↑u*(-1) * ((dir (foot (Center C) L) a)).x := by{ring}
      rw[br] at p0
      clear br
      have : (↑u : ℂ) = 0 := by{
        by_contra z0
        have : (dir (foot (Center C) L) a).x = -(dir (foot (Center C) L) a).x :=by{
          calc
            (dir (foot (Center C) L) a).x = (1/(↑u))*(↑u*(dir (foot (Center C) L) a).x) := by{field_simp}
              _= (1/(↑u))*(↑u * -1 * (dir (foot (Center C) L) a).x) := by{rw[p0]}
              _= -(dir (foot (Center C) L) a).x := by{field_simp;ring}
        }
        have : (dir (foot (Center C) L) a).x = 0 := by{
          exact CharZero.eq_neg_self_iff.mp this
        }
        contradiction
      }
      norm_cast at this
    }
    rw[this] at upos
    contrapose upos
    simp
  }
  have hp : Lies_on_circle p C := by{
    refine point_on_circle_simp ?h
    have pperp: perp_points (foot (Center C) L) (Center C) (foot (Center C) L) p := by{
      by_cases z: (foot (Center C) L) = Center C
      apply perp_points_self
      tauto

      by_cases i: (foot (Center C) L) = p
      apply perp_points_self
      tauto

      have : Perpendicular (Line_through z) (Line_through i) := by{
        have : L = Line_through i := by{
          apply line_through_unique
          constructor
          exact foot_on_line L (Center C)
          unfold p
          apply go_along_lies_on
          constructor
          exact foot_on_line L (Center C)
          assumption
        }
        rw[← this]
        have : Line_through z = perp_through L (Center C) := by{
          have : ¬Lies_on (Center C) L := by{
            contrapose z
            simp at *
            exact foot_point_on_line z
          }
          rw[← foot_line_through this]
        }
        rw[this]
        apply perp_symm
        exact perp_through_is_perp L (Center C)
      }
      exact perp_line_through_points this
    }
    rw[pythagoras_points_bc pperp]
    rw[point_abs_symm p (foot (Center C) L)]
    unfold p
    have : foot (Center C) L ≠ a := by{exact id (Ne.symm ah2)}
    rw[point_abs_symm (foot (Center C) L) (Center C)]
    rw[go_along_abs1 this u]
    unfold u
    simp [*]
    symm
    calc
      ↑(Radius C) = √(↑(Radius C)^2) := by{
        have : 0 ≤ ↑(Radius C) := by{exact zero_le (Radius C)}
        exact Eq.symm (Real.sqrt_sq this)
      }
        _= √(point_abs (Center C) (foot (Center C) L) ^ 2 +
      (↑(Radius C) ^ 2 - point_abs (Center C) (foot (Center C) L) ^ 2)) := by{ring_nf}
        _= √(point_abs (Center C) (foot (Center C) L) ^ 2 +
      √(↑(Radius C) ^ 2 - point_abs (Center C) (foot (Center C) L) ^ 2) ^ 2) := by{
        have : √(↑(Radius C) ^ 2 - point_abs (Center C) (foot (Center C) L) ^ 2) ^ 2 = (↑(Radius C) ^ 2 - point_abs (Center C) (foot (Center C) L) ^ 2) := by{
          exact Real.sq_sqrt weirdnonneg
        }
        rw[this]
      }
  }
  have hq : Lies_on_circle q C := by{
    apply point_on_circle_simp
    have qperp: perp_points (foot (Center C) L) (Center C) (foot (Center C) L) q := by{
      by_cases z: (foot (Center C) L) = Center C
      apply perp_points_self
      tauto

      by_cases i: (foot (Center C) L) = q
      apply perp_points_self
      tauto

      have : Perpendicular (Line_through z) (Line_through i) := by{
        have : L = Line_through i := by{
          apply line_through_unique
          constructor
          exact foot_on_line L (Center C)
          unfold q
          apply go_along_lies_on
          constructor
          exact foot_on_line L (Center C)
          assumption
        }
        rw[← this]
        have : Line_through z = perp_through L (Center C) := by{
          have : ¬Lies_on (Center C) L := by{
            contrapose z
            simp at *
            exact foot_point_on_line z
          }
          rw[← foot_line_through this]
        }
        rw[this]
        apply perp_symm
        exact perp_through_is_perp L (Center C)
      }
      exact perp_line_through_points this
    }
    rw[pythagoras_points_bc qperp]
    rw[point_abs_symm q (foot (Center C) L)]
    unfold q
    have : foot (Center C) L ≠ a := by{exact id (Ne.symm ah2)}
    rw[point_abs_symm (foot (Center C) L) (Center C)]
    rw[go_along_abs1 this (-u)]
    unfold u
    simp [*]
    symm
    calc
      ↑(Radius C) = √(↑(Radius C)^2) := by{
        have : 0 ≤ ↑(Radius C) := by{exact zero_le (Radius C)}
        exact Eq.symm (Real.sqrt_sq this)
      }
        _= √(point_abs (Center C) (foot (Center C) L) ^ 2 +
      (↑(Radius C) ^ 2 - point_abs (Center C) (foot (Center C) L) ^ 2)) := by{ring_nf}
        _= √(point_abs (Center C) (foot (Center C) L) ^ 2 +
      √(↑(Radius C) ^ 2 - point_abs (Center C) (foot (Center C) L) ^ 2) ^ 2) := by{
        have : √(↑(Radius C) ^ 2 - point_abs (Center C) (foot (Center C) L) ^ 2) ^ 2 = (↑(Radius C) ^ 2 - point_abs (Center C) (foot (Center C) L) ^ 2) := by{
          exact Real.sq_sqrt weirdnonneg
        }
        rw[this]
      }
  }
  have ph2: p = Tangent_point h := by{
    apply tangent_point_unique
    constructor
    unfold p
    have ha2: foot (Center C) L ≠ a := by{tauto}
    have : L = Line_through ha2 := by{
      apply line_through_unique
      constructor
      exact foot_on_line L (Center C)
      assumption
    }
    nth_rw 2[this]
    unfold Lies_on
    nth_rw 1[Line_through]
    simp
    exact go_along_colinear (foot (Center C) L) a u

    assumption
  }
  have qh2: q = Tangent_point h := by{
    apply tangent_point_unique
    constructor
    unfold q
    have ha2: foot (Center C) L ≠ a := by{tauto}
    have : L = Line_through ha2 := by{
      apply line_through_unique
      constructor
      exact foot_on_line L (Center C)
      assumption
    }
    nth_rw 2[this]
    unfold Lies_on
    nth_rw 1[Line_through]
    simp
    exact go_along_colinear (foot (Center C) L) a (-u)

    assumption
  }
  rw[ph2,qh2] at pq
  contradiction
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

/-From this we can deduce that all lines are perpendicular to the radius, this howver only makes sense when we have positive radius.-/

theorem tangent_is_perp{C : CCircle}{L : Line}(h : Tangent L C): Perpendicular L (qLine_through (Center C) )
