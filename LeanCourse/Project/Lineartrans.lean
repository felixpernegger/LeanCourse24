import LeanCourse.Project.Reflections
import Mathlib

open Function Set Classical

noncomputable section

/-In this section we introduce linear transformations.
Linear transformations pretty much preserve _everything_ (as long as the scale factor isnt zero).
Proving that is rather tedious, thus we only bring up what we will actually use.-/

/-First small small lemma which will save us a bit of time occassionally:-/

lemma not_zero_simp{a : Point}(ah : a ≠ zero): a.x ≠ 0 := by{
  contrapose ah
  unfold zero
  simp at *
  ext
  simpa
}

def Linear_trans_point : Point → Point → Point → Point :=
  fun a b p ↦ padd (pmul a p) b

/-the inverse of a linear transformation is 1/a and -b/a or:-/
def lt_inv1 : Point → Point → Point :=
  fun a b ↦ recip a

def lt_inv2 : Point → Point → Point :=
  fun a b ↦ pneg (pmul b (recip a))

/-A few observations:-/

lemma linear_trans_point_comp(a b c d p: Point): Linear_trans_point a b (Linear_trans_point c d p) = Linear_trans_point (pmul a c) (padd (pmul a d) b) p := by{
  ext
  unfold Linear_trans_point padd pmul
  simp
  ring
}

@[simp] lemma linear_trans_point_id(p : Point): Linear_trans_point one zero p = p := by{
  unfold Linear_trans_point one zero padd pmul
  ext
  simp
}

lemma linear_trans_point_inv_left(a b : Point)(ah : a ≠ zero)(p : Point): Linear_trans_point (lt_inv1 a b) (lt_inv2 a b) (Linear_trans_point a b p) = p := by{
  have : a.x ≠ 0 := by{exact fun a_1 ↦ id (Ne.symm ah) (congrArg Point.mk (id (Eq.symm a_1)))}
  unfold Linear_trans_point lt_inv1 lt_inv2 recip pmul padd pneg
  field_simp
}


lemma linear_trans_point_inv_right(a b : Point)(ah : a ≠ zero)(p : Point): Linear_trans_point a b (Linear_trans_point (lt_inv1 a b) (lt_inv2 a b) p) = p := by{
  have : a.x ≠ 0 := by{exact fun a_1 ↦ id (Ne.symm ah) (congrArg Point.mk (id (Eq.symm a_1)))}
  unfold Linear_trans_point lt_inv1 lt_inv2 recip pmul padd pneg
  field_simp
}

lemma linear_trans_point_inj(a b: Point)(ah : a ≠ zero){u v : Point}(h : Linear_trans_point a b u = Linear_trans_point a b v): u = v := by{
  calc
    u = Linear_trans_point one zero u := by{exact Eq.symm (linear_trans_point_id u)}
      _= Linear_trans_point (pmul (recip a) a) (padd (pmul (recip a) b) (pneg (pmul b (recip a)))) u := by{
        have : a.x ≠ 0 := by{
          contrapose ah
          unfold zero
          simp at *
          ext
          assumption
        }
        unfold Linear_trans_point recip pmul pneg padd one zero
        simp
        field_simp
      }
      _= Linear_trans_point (recip a) (pneg (pmul b (recip a))) (Linear_trans_point a b u) := by{rw[linear_trans_point_comp (recip a) (pneg (pmul b (recip a))) a b u]}
      _= Linear_trans_point (recip a) (pneg (pmul b (recip a))) (Linear_trans_point a b v) := by{rw[h]}
      _= Linear_trans_point (pmul (recip a) a) (padd (pmul (recip a) b) (pneg (pmul b (recip a)))) v := by{rw[linear_trans_point_comp (recip a) (pneg (pmul b (recip a))) a b v]}
      _= Linear_trans_point one zero v := by{
        have : a.x ≠ 0 := by{
          contrapose ah
          unfold zero
          simp at *
          ext
          assumption
        }
        unfold Linear_trans_point recip pmul pneg padd one zero
        simp
        field_simp
      }
      _= v := by{rw[linear_trans_point_id v]}
}

/-And colinear points stay colinear!-/
lemma linear_trans_point_colinear(a b : Point){u v r : Point}(h : colinear u v r): colinear (Linear_trans_point a b u) (Linear_trans_point a b v) (Linear_trans_point a b r) := by{
  unfold colinear
  have : det (Linear_trans_point a b u) (Linear_trans_point a b v) (Linear_trans_point a b r) = det (pmul a u) (pmul a v) (pmul a r) := by{
    unfold Linear_trans_point padd pmul det conj
    obtain ⟨a1,a2⟩ := a
    obtain ⟨b1,b2⟩ := b
    obtain ⟨u1,u2⟩ := u
    obtain ⟨v1,v2⟩ := v
    obtain ⟨r1,r2⟩ := r
    simp
    ring
  }
  rw[this]
  clear this
  unfold colinear at *
  apply det_zero_detproper at h
  rw[det_detproper]
  have goal:(detproper (pmul a u).x (conj (pmul a u).x) 1 (pmul a v).x (conj (pmul a v).x) 1 (pmul a r).x (conj (pmul a r).x)
      1) = 0 := by{
        have : detproper (pmul a u).x (conj (pmul a u).x) 1 (pmul a v).x (conj (pmul a v).x) 1 (pmul a r).x (conj (pmul a r).x) 1 = (a.x * (conj a.x)) * (detproper (u.x) (conj (u.x)) 1 (v.x) (conj (v.x)) 1 (r.x) (conj (r.x)) 1) := by{
          unfold conj detproper pmul
          simp
          ring
        }
        rw[this]
        clear this
        rw[h]
        ring
    }
  rw[goal]
  simp
}

def linear_trans_set : Point → Point → Set Point → Set Point :=
  fun a b S ↦ {u | ∃ s ∈ S, u = Linear_trans_point a b s}

def Linear_trans_line : Point → Point → Line → Line :=
  fun a b L ↦ (if h : a = zero then real_line else ⟨linear_trans_set a b L.range, by{
    have ah: a.x≠ 0 := by{
      contrapose h
      unfold zero
      simp at *
      ext
      simp [h]
    }
    obtain ⟨u,v,uv,uh,vh⟩ := ex_points_on_line L
    have hL : L = Line_through uv := by{
      apply line_through_unique
      tauto
    }
    rw[hL]
    use Linear_trans_point a b u
    use Linear_trans_point a b v
    unfold Line_through linear_trans_set
    simp
    constructor
    by_contra h0
    have : u = v := by{exact linear_trans_point_inj a b h h0}
    contradiction

    ext z
    simp
    constructor
    intro hh
    obtain ⟨s,sh1,sh2⟩ := hh
    have : z = Linear_trans_point a b s := by{unfold Linear_trans_point; assumption}
    rw[this]
    exact linear_trans_point_colinear a b sh1
    have s1: Linear_trans_point a b (Linear_trans_point (recip a) (pneg (pmul b (recip a))) z) = z := by{
      unfold Linear_trans_point pneg recip padd pmul
      field_simp
    }
    intro hh
    use Linear_trans_point (recip a) (pneg (pmul b (recip a))) z
    constructor
    swap
    ext
    unfold Linear_trans_point padd pneg pmul recip
    simp
    field_simp

    have uh: u = (Linear_trans_point (recip a) (pneg (pmul b (recip a))) (Linear_trans_point a b u)) := by{
      unfold Linear_trans_point pneg recip padd pmul
      field_simp
    }
    have vh: v =  (Linear_trans_point (recip a) (pneg (pmul b (recip a))) (Linear_trans_point a b v)) := by{
      unfold Linear_trans_point pneg recip padd pmul
      field_simp
    }
    rw[uh,vh,← s1]
    clear uh vh s1
    have : (Linear_trans_point (recip a) (pneg (pmul b (recip a)))
    (Linear_trans_point a b (Linear_trans_point (recip a) (pneg (pmul b (recip a))) z))) = Linear_trans_point (recip a) (pneg (pmul b (recip a))) z := by{
      unfold Linear_trans_point recip pneg pmul padd
      field_simp
    }
    rw[this]
    apply linear_trans_point_colinear
    assumption
  }⟩)

lemma linear_trans_set_mem(a b p : Point)(ah : a ≠ zero)(S : Set Point): Linear_trans_point a b p ∈ linear_trans_set a b S ↔ p ∈ S := by{
  constructor
  intro h
  unfold linear_trans_set at h
  simp at h
  obtain ⟨s,sh1,sh2⟩ := h
  have : p = s := by{
    have : a.x ≠ 0 := by{exact fun a_1 ↦ id (Ne.symm ah) (congrArg Point.mk (id (Eq.symm a_1)))}
    unfold Linear_trans_point padd pmul at sh2
    field_simp at sh2
    simp [*] at sh2
    ext
    assumption
  }
  rw[this]
  assumption

  intro h
  unfold linear_trans_set
  simp
  use p
}

lemma linear_trans_lies_on(a b : Point)(ah : a ≠ zero)(p : Point)(L : Line): Lies_on (Linear_trans_point a b p) (Linear_trans_line a b L) ↔ Lies_on p L := by{
  unfold Lies_on Linear_trans_line at *
  simp [*]
  exact linear_trans_set_mem a b p ah L.range
}

/-perp points stay perp-/

lemma linear_trans_perp_points(a b : Point)(ha : a ≠ zero)(u v w r : Point): perp_points (Linear_trans_point a b u) (Linear_trans_point a b v) (Linear_trans_point a b w) (Linear_trans_point a b r) ↔ perp_points u v w r := by{
  have t1: a.x ≠ 0 := by{exact fun a_1 ↦ id (Ne.symm ha) (congrArg Point.mk (id (Eq.symm a_1)))}
  unfold perp_points Linear_trans_point padd pmul
  field_simp
  by_cases h0: w.x = r.x
  rw[h0]
  simp

  have t2: w.x - r.x ≠ 0 := by{exact sub_neq_zero fun a ↦ h0 (congrArg Point.x a)}
  have : a.x*w.x-a.x*r.x≠ 0 := by{
    by_contra p0
    have : a.x*w.x - a.x *r.x = a.x*(w.x-r.x) := by{ring}
    rw[this] at p0
    simp at p0
    tauto
  }
  have : (a.x * u.x - a.x * v.x) / (a.x * w.x - a.x * r.x) = (u.x-v.x)/(w.x-r.x) := by{field_simp;ring}
  rw[this]
}

/-therefore perp lines stay perp:-/

lemma linear_trans_perp(a b : Point)(ah : a ≠ zero)(L R : Line): Perpendicular (Linear_trans_line a b L) (Linear_trans_line a b R) ↔ Perpendicular L R := by{
  constructor
  intro h
  unfold Perpendicular at *
  obtain ⟨u,v,s,r,uv,sr,uh,vh,sh,rh,hh⟩ := h
  use Linear_trans_point (lt_inv1 a b) (lt_inv2 a b) u
  use Linear_trans_point (lt_inv1 a b) (lt_inv2 a b) v
  use Linear_trans_point (lt_inv1 a b) (lt_inv2 a b) s
  use Linear_trans_point (lt_inv1 a b) (lt_inv2 a b) r
  constructor
  contrapose uv
  simp at *
  apply linear_trans_point_inj (lt_inv1 a b) (lt_inv2 a b)
  contrapose ah
  unfold lt_inv1 recip at ah
  unfold zero at *
  simp at *
  ext
  simpa
  assumption

  constructor
  contrapose sr
  simp at *
  apply linear_trans_point_inj (lt_inv1 a b) (lt_inv2 a b)
  contrapose ah
  unfold lt_inv1 recip at ah
  unfold zero at *
  simp at *
  ext
  simpa
  assumption

  constructor
  sorry
  sorry
  sorry
}

/-Thus perp_throughs stay the same:-/

lemma linear_trans_perp_through(a b : Point)(ah : a ≠ zero)(p : Point)(L : Line): Linear_trans_line a b (perp_through L p) = perp_through (Linear_trans_line a b L) (Linear_trans_point a b p) := by{
  apply perp_through_unique
  constructor
  apply (linear_trans_perp a b ah L (perp_through L p)).2
  exact perp_through_is_perp L p

  apply (linear_trans_lies_on a b ah p (perp_through L p)).2
  exact point_lies_on_perp_through L p
}

/-Thus foots stay the same:-/

lemma linear_trans_foot(a b : Point)(ah : a ≠ zero)(p : Point)(L : Line): Linear_trans_point a b (foot p L) = foot (Linear_trans_point a b p) (Linear_trans_line a b L) := by{
  apply foot_unique
  constructor
  apply (linear_trans_lies_on a b ah (foot p L) L).2
  exact foot_on_line L p

  rw[← linear_trans_perp_through]
  apply (linear_trans_lies_on a b ah (foot p L) (perp_through L p)).2
  · exact foot_on_perp L p
  assumption
}


--TO DO: PERP LINES STAY PERP, THEREFORE PERP THROUGH STAY THE SAME THEREFORE FOOTS STAY THE SAME
--THEREFORE REFLECTION STAY THE SAME

--THEN : THEORE EXISTS A B WITH A NOT ZERO (IMPORTANT) FOR ANY LINE, SUCH THAT L GETS SENT TO THE REAL LINE

--IN THE ANGLES SECTION THEN SHOW THAT ANGLES ARE PRESERVED UNDER LINEAR TRANS
