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
  apply point_abs_point_lies_on_circle
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
  have ad: point_abs (Center C) a = Radius C := by{exact point_abs_point_lies_on_circle ac}
  have bd: point_abs (Center C) b = Radius C := by{exact point_abs_point_lies_on_circle bc}
  have g: point_abs (Center C) (foot (Center C) L) = Radius C := by{exact point_abs_point_lies_on_circle h}
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

/-To make this a bit clearer, first following:-/

lemma tangent_point_not_center{C : CCircle}{L : Line}(hC : PosRad C)(h : Tangent L C): Tangent_point h ≠ Center C := by{
  exact posrad_not_center hC (tangent_point_on_circle h)
}

theorem tangent_is_perp{C : CCircle}{L : Line}(hC : PosRad C)(h : Tangent L C): Perpendicular L (Line_through (tangent_point_not_center hC h)) := by{
  have h': Lies_on_circle (foot (Center C) L) C := by{exact (line_tangent_iff L C).mp h}
  have cnot: ¬Lies_on (Center C) L := by{
    contrapose hC
    unfold PosRad
    simp at *
    have : foot (Center C) L = Center C := by{exact foot_point_on_line hC}
    have t: point_abs (Center C) ((foot (Center C) L)) = Radius C := by{exact point_abs_point_lies_on_circle h'}
    rw[this] at t
    rw[point_abs_self (Center C)] at t
    ext
    tauto
  }
  have hL: Line_through (tangent_point_not_center hC h) = perp_through L (Center C) := by{
    have t: Line_through (tangent_point_not_center hC h) = Line_through (foot_point_not_on_line cnot) := by{
      symm
      apply line_through_unique
      constructor
      · rw[tangent_point_foot h]
        exact line_through_mem_left (foot_point_not_on_line cnot)
      exact line_through_mem_right (foot_point_not_on_line cnot)
    }
    rw[t]
    exact foot_line_through cnot
  }
  rw[hL]
  exact perp_through_is_perp L (Center C)
}

/- We define the line_through for a point on the perimiter nicely sperately, for more generality we use
qLine_through:-/

def Center_line{C : CCircle}{p : Point}(hp : Lies_on_circle p C): Line :=
  qLine_through (Center C) p

lemma center_on_center_line{C : CCircle}{p : Point}(hp : Lies_on_circle p C): Lies_on (Center C) (Center_line hp) := by{
  unfold Center_line
  exact qline_through_mem_left (Center C) p
}

lemma point_on_center_line{C : CCircle}{p : Point}(hp : Lies_on_circle p C): Lies_on p (Center_line hp) := by{
  unfold Center_line
  exact qline_through_mem_right (Center C) p
}

/-if posrad, this is the normal line_through:-/

lemma posrad_center_line{C : CCircle}{p : Point}(hp : Lies_on_circle p C)(hC : PosRad C): Center_line hp = Line_through (posrad_not_center hC hp) := by{
  unfold Center_line
  unfold qLine_through
  have : ¬Center C = p := by{
    by_contra a
    symm at a
    contrapose a
    exact posrad_not_center hC hp
  }
  simp [*]
  exact line_through_symm (posrad_not_center hC hp)
}

/-The reveserse also holds, given a point on a circle, the perp through it is a tangent:-/
lemma perp_is_tangent{C : CCircle}{p : Point}(hp : Lies_on_circle p C) : Tangent (perp_through (Center_line hp) p) C := by{
  by_cases hC : PosRad C
  apply (line_tangent_iff (perp_through (Center_line hp) p) C).2
  have goal: foot (Center C) (perp_through (Center_line hp) p) = p := by{
    rw[posrad_center_line hp hC,line_through_symm (Ne.symm (posrad_not_center hC hp))]
    exact foot_perp_through2 (Ne.symm (posrad_not_center hC hp))}
  rwa[goal]

  unfold PosRad at hC
  simp at hC
  have : p = Center C := by{exact lies_on_radius_zero hC hp}
  apply (line_tangent_iff (perp_through (Center_line hp) p) C).2
  have : foot (Center C) (perp_through (Center_line hp) p) = Center C := by{
    symm
    apply foot_unique
    constructor
    · rw[← this]
      exact point_lies_on_perp_through (Center_line hp) p
    exact point_lies_on_perp_through (perp_through (Center_line hp) p) (Center C)
  }
  rw[this]
  apply point_on_circle_simp
  rw[hC]
  exact point_abs_self (Center C)
}

/-Therefore we can define the tangent through any given point!-/

def Tangent_through{C : CCircle}{p : Point}(h : Lies_on_circle p C) : Line :=
  perp_through (Center_line h) p

/-As usual this does what we want:-/

lemma tangent_through_is_tangent{C : CCircle}{p : Point}(h : Lies_on_circle p C) : Tangent (Tangent_through h) C := by{
  unfold Tangent_through
  exact perp_is_tangent h
}

/-And the point lies on it:-/

lemma point_lies_on_tangent_through{C : CCircle}{p : Point}(h : Lies_on_circle p C) : Lies_on p (Tangent_through h) := by{
  unfold Tangent_through
  exact point_lies_on_perp_through (Center_line h) p
}

/-if posrad, this is perpendicular to the centerline:-/

lemma tangent_through_is_perp{C : CCircle}{p : Point}(h : Lies_on_circle p C)(hC : PosRad C) : Perpendicular (Tangent_through h) (Center_line h) := by{
  have s1: Tangent (Tangent_through h) C := by{exact tangent_through_is_tangent h}
  have s2: Center_line h = Line_through (tangent_point_not_center hC s1) := by{
    apply line_through_unique
    constructor
    have : Tangent_point s1 = p := by{
      symm
      apply tangent_point_unique
      constructor
      · exact point_lies_on_tangent_through h
      assumption
    }
    rw[this]
    exact point_on_center_line h
    exact center_on_center_line h
  }
  rw[s2]
  exact tangent_is_perp hC s1
}

/-And indeed unique for posrad!-/

theorem tangent_through_unique{C : CCircle}{p : Point}{L : Line}(h : Lies_on_circle p C)(hC : PosRad C)(hp : Lies_on p L)(hL : Tangent L C) : L = Tangent_through h := by{
  have goal : Parallel L (Tangent_through h) := by{
    sorry
  }

}
