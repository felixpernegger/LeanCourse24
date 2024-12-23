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

lemma linear_trans_point_eq(p : Point){a b c d : Point}(h1: a = c)(h2: b = d): Linear_trans_point a b p = Linear_trans_point c d p := by{rw[h1,h2]}

lemma linear_trans_point_id_simp(p : Point){a b : Point}(ah : a = one)(bh : b = zero): Linear_trans_point a b p = p := by{
  rw[ah,bh]
  unfold Linear_trans_point zero one pmul padd
  simp
}

/-the inverse of a linear transformation is 1/a and -b/a or:-/
def lt_inv1 : Point → Point → Point :=
  fun a b ↦ recip a

lemma lt_inv1_not_zero(a b : Point)(ah: a ≠ zero): lt_inv1 a b ≠ zero := by{
  contrapose ah
  simp at *
  unfold zero lt_inv1 recip at *
  ext
  simp at *
  assumption
}

def lt_inv2 : Point → Point → Point :=
  fun a b ↦ pneg (pmul b (recip a))

lemma lt_inv1_inv(a b : Point)(ah: a ≠ zero): pmul (lt_inv1 a b) a = one := by{
  have : a.x ≠ 0 := by{exact not_zero_simp ah}
  unfold lt_inv1 recip pmul one
  field_simp
}

lemma lt_inv2_inv(a b : Point)(ah : a ≠ zero): padd (pmul (lt_inv1 a b) b) (lt_inv2 a b) = zero := by{
  unfold lt_inv2 lt_inv1 recip pmul padd zero pneg
  field_simp [not_zero_simp ah]
}

lemma lt_inv2_inv'(a b : Point)(ah : a ≠ zero): padd (pmul a (lt_inv2 a b)) b = zero := by{
  unfold lt_inv2 recip pmul padd zero pneg
  field_simp [not_zero_simp ah]
  ring
}

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

/-therefore also noncolinear:-/
lemma linear_trans_point_noncolinear(a b : Point)(ah : a ≠ zero){u v r : Point}(h : noncolinear u v r): noncolinear (Linear_trans_point a b u) (Linear_trans_point a b v) (Linear_trans_point a b r) := by{
  contrapose h
  unfold noncolinear at *
  simp at *
  rw[← linear_trans_point_inv_left a b ah u, ← linear_trans_point_inv_left a b ah v, ← linear_trans_point_inv_left a b ah r]
  exact linear_trans_point_colinear (lt_inv1 a b) (lt_inv2 a b) h
}

--lemma linear_trans_set_inv_left

def Linear_trans_set : Point → Point → Set Point → Set Point :=
  fun a b S ↦ {u | ∃ s ∈ S, u = Linear_trans_point a b s}

@[simp] lemma linear_trans_set_id(S : Set Point): Linear_trans_set one zero S = S := by{
  unfold Linear_trans_set
  simp_rw [linear_trans_point_id]
  simp
}

lemma linear_trans_set_eq(S : Set Point){a b c d : Point}(h1: a = c)(h2: b = d): Linear_trans_set a b S = Linear_trans_set c d S := by{rw[h1,h2]}

lemma linear_trans_set_id_simp(S : Set Point){a b : Point}(ah : a = one)(bh : b = zero): Linear_trans_set a b S = S := by{
  rw[ah,bh]
  simp
}

lemma linear_trans_set_comp(a b c d : Point)(S : Set Point): Linear_trans_set a b (Linear_trans_set c d S) = Linear_trans_set (pmul a c) (padd (pmul a d) b) S := by{
  ext u
  unfold Linear_trans_set
  simp
  constructor
  intro h
  obtain ⟨v,vh1,vh2⟩ := h
  obtain ⟨r,rh1,rh2⟩ := vh1
  use r
  constructor
  · assumption
  rw[vh2,rh2]
  exact linear_trans_point_comp a b c d r

  intro h
  obtain ⟨s,sh1,sh2⟩ := h
  use Linear_trans_point c d s
  constructor
  use s
  rw[sh2]
  symm
  exact linear_trans_point_comp a b c d s
}

lemma linear_trans_set_inv_left(a b : Point)(ah : a ≠ zero)(S : Set Point): Linear_trans_set (lt_inv1 a b) (lt_inv2 a b) (Linear_trans_set a b S) = S := by{
  rw[linear_trans_set_comp]
  apply linear_trans_set_id_simp
  · exact lt_inv1_inv a b ah
  exact lt_inv2_inv a b ah
}

lemma linear_trans_set_inv_right(a b : Point)(ah : a ≠ zero)(S : Set Point): Linear_trans_set a b (Linear_trans_set (lt_inv1 a b) (lt_inv2 a b) S) = S := by{
  rw[linear_trans_set_comp]
  apply linear_trans_set_id_simp
  · rw[pmul_comm]
    exact lt_inv1_inv a b ah
  exact lt_inv2_inv' a b ah
}

def Linear_trans_line : Point → Point → Line → Line :=
  fun a b L ↦ (if h : a = zero then real_line else ⟨Linear_trans_set a b L.range, by{
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
    unfold Line_through Linear_trans_set
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

lemma linear_trans_line_comp(a b : Point)(ah : a ≠ zero)(c d : Point)(ch : c ≠ zero)(L : Line): Linear_trans_line a b (Linear_trans_line c d L) = Linear_trans_line (pmul a c) (padd (pmul a d) b) L := by{
  unfold Linear_trans_line
  have : pmul a c ≠ zero := by{
    by_contra h0
    unfold pmul zero at *
    simp at *
    obtain h0|h0 := h0
    contrapose ah
    simp
    ext
    simp [*]

    contrapose ch
    simp
    ext
    simp [*]
  }
  simp [*]
  exact linear_trans_set_comp a b c d L.range
}

lemma linear_trans_line_inv_left(a b : Point)(ah : a ≠ zero)(L : Line): Linear_trans_line (lt_inv1 a b) (lt_inv2 a b) (Linear_trans_line a b L) = L := by{
  unfold Linear_trans_line
  simp [*]
  have : lt_inv1 a b ≠ zero := by{
    contrapose ah
    simp at *
    unfold zero lt_inv1 recip at *
    simp at *
    ext
    simp
    assumption
  }
  simp [*]
  simp_rw[linear_trans_set_inv_left a b ah L.range]
}

lemma linear_trans_line_inv_right(a b : Point)(ah : a ≠ zero)(L : Line): Linear_trans_line a b (Linear_trans_line (lt_inv1 a b) (lt_inv2 a b) L) = L := by{
  unfold Linear_trans_line
  simp [*]
  have : lt_inv1 a b ≠ zero := by{
    contrapose ah
    simp at *
    unfold zero lt_inv1 recip at *
    simp at *
    ext
    simp
    assumption
  }
  simp [*]
  simp_rw[linear_trans_set_inv_right a b ah L.range]
}


lemma linear_trans_set_mem(a b p : Point)(ah : a ≠ zero)(S : Set Point): Linear_trans_point a b p ∈ Linear_trans_set a b S ↔ p ∈ S := by{
  constructor
  intro h
  unfold Linear_trans_set at h
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
  unfold Linear_trans_set
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
  · rw[← linear_trans_line_inv_left a b ah L]
    exact (linear_trans_lies_on (lt_inv1 a b) (lt_inv2 a b) (lt_inv1_not_zero a b ah) u (Linear_trans_line a b L)).2 uh
  constructor
  · rw[← linear_trans_line_inv_left a b ah L]
    exact (linear_trans_lies_on (lt_inv1 a b) (lt_inv2 a b) (lt_inv1_not_zero a b ah) v (Linear_trans_line a b L)).2 vh
  constructor
  · rw[← linear_trans_line_inv_left a b ah R]
    exact (linear_trans_lies_on (lt_inv1 a b) (lt_inv2 a b) (lt_inv1_not_zero a b ah) s (Linear_trans_line a b R)).2 sh
  constructor
  · rw[← linear_trans_line_inv_left a b ah R]
    exact (linear_trans_lies_on (lt_inv1 a b) (lt_inv2 a b) (lt_inv1_not_zero a b ah) r (Linear_trans_line a b R)).2 rh

  exact (linear_trans_perp_points (lt_inv1 a b) (lt_inv2 a b) (lt_inv1_not_zero a b ah) u v s r).2 hh


  intro h

  unfold Perpendicular at *
  obtain ⟨u,v,s,r,uv,sr,uh,vh,sh,rh,hh⟩ := h
  use Linear_trans_point a b u
  use Linear_trans_point a b v
  use Linear_trans_point a b s
  use Linear_trans_point a b r
  constructor
  contrapose uv
  simp at *
  exact linear_trans_point_inj a b ah uv

  constructor
  contrapose sr
  simp at *
  exact linear_trans_point_inj  a b ah sr

  constructor
  · exact (linear_trans_lies_on a b ah u L).2 uh
  constructor
  · exact (linear_trans_lies_on a b ah v L).2 vh
  constructor
  · exact (linear_trans_lies_on a b ah s R).2 sh
  constructor
  · exact (linear_trans_lies_on a b ah r R).2 rh
  exact (linear_trans_perp_points a b ah u v s r).mpr hh
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

/-Now we show reflections stay the same:-/

lemma linear_trans_reflection_point_point(a b : Point)(ah : a ≠ zero)(p q : Point): Linear_trans_point a b (reflection_point_point p q) = reflection_point_point (Linear_trans_point a b p) (Linear_trans_point a b q) := by{
  unfold Linear_trans_point reflection_point_point padd pmul p_scal_mul pneg
  simp
  ring
}

/-And using the foot result above this works for line reflections:-/

lemma linear_trans_reflection_point_line(a b : Point)(ah : a ≠ zero)(p : Point)(L : Line): Linear_trans_point a b (reflection_point_line p L) = reflection_point_line (Linear_trans_point a b p) (Linear_trans_line a b L) := by{
  unfold reflection_point_line
  rw[← linear_trans_foot a b ah p L, linear_trans_reflection_point_point]
  assumption
}

/-One of the major reasons we do all of this rather tedious work, is that we transform every line onto the real line,
and therefore if we want to prove something concerning some central line, we "only" have to prove the speical case
when the line is the real line and can then transform everything back into its original state.
For example, this method will later be used to show angles stay the same when we reflect them across a line. -/

lemma linear_trans_line_real_line(L : Line): ∃(a b : Point), a ≠ zero ∧ Linear_trans_line a b L = real_line := by{
  obtain ⟨u,v,uv,uh,vh⟩ := ex_points_on_line L
  have s1: padd v (pneg u) ≠ zero := by{
    contrapose uv
    unfold padd pneg zero at *
    simp at *
    ext
    rw[← add_zero u.x, ← uv]
    ring
  }
  have s2: recip (padd v (pneg u)) ≠ zero := by{
    contrapose s1
    simp at *
    unfold recip zero at s1
    simp at s1
    unfold zero
    ext
    simpa
  }
  use recip (padd v (pneg u))
  use pmul (pneg u) (recip (padd v (pneg u)))
  constructor
  assumption

  rw[real_line_line_through]
  apply line_through_unique
  constructor
  unfold Linear_trans_line Lies_on
  simp [*]
  have : zero = Linear_trans_point (recip (padd v (pneg u))) (pmul (pneg u) (recip (padd v (pneg u)))) u := by{
    unfold Linear_trans_point padd pmul zero pneg recip at *
    field_simp
  }
  rw[this]
  exact
    (linear_trans_set_mem (recip (padd v (pneg u))) (pmul (pneg u) (recip (padd v (pneg u)))) u s2
          L.range).mpr
      uh

  unfold Linear_trans_line Lies_on
  simp [*]
  have : one = Linear_trans_point (recip (padd v (pneg u))) (pmul (pneg u) (recip (padd v (pneg u)))) v := by{
    unfold Linear_trans_point padd pmul zero one pneg recip at *
    symm at uv
    have : v.x +-u.x ≠ 0 := by{exact fun a ↦ s1 (congrArg Point.mk a)}
    field_simp
  }
  rw[this]
  exact
    (linear_trans_set_mem (recip (padd v (pneg u))) (pmul (pneg u) (recip (padd v (pneg u)))) v s2
          L.range).mpr
      vh
}
variable (R : Line)

def lt_norm_line1 : Line → Point :=
  fun L ↦ (linear_trans_line_real_line L).choose

lemma lt_norm_line1_ex2(L : Line): ∃(b : Point), (lt_norm_line1 L) ≠ zero ∧ Linear_trans_line (lt_norm_line1 L) b L = real_line := by{
  exact Exists.choose_spec (linear_trans_line_real_line L)
}

def lt_norm_line2 : Line → Point :=
  fun L ↦ (lt_norm_line1_ex2 L).choose

lemma lt_norm_line1_neq_zero(L : Line): lt_norm_line1 L ≠ zero := by{
  obtain ⟨b,bh⟩ := lt_norm_line1_ex2 L
  tauto
}

lemma lt_norm_line_real_line(L : Line): Linear_trans_line (lt_norm_line1 L) (lt_norm_line2 L) L = real_line := by{
  unfold lt_norm_line2
  exact (Exists.choose_spec (lt_norm_line1_ex2 L)).2
}

/-We can also define the inverse, which therefore takes the real line to L:-/

def lt_norm_line_inv1: Line → Point :=
  fun L ↦ lt_inv1 (lt_norm_line1 L) (lt_norm_line2 L)

def lt_norm_line_inv2: Line → Point :=
  fun L ↦ lt_inv2 (lt_norm_line1 L) (lt_norm_line2 L)

lemma lt_norm_line_inv1_neq_zero(L : Line): lt_norm_line_inv1 L ≠ zero := by{
  unfold lt_norm_line_inv1
  exact lt_inv1_not_zero (lt_norm_line1 L) (lt_norm_line2 L) (lt_norm_line1_neq_zero L)
}

/-Which is inverse...-/

lemma lt_norm_line_inv_inv_point_left(L : Line)(p : Point): Linear_trans_point (lt_norm_line_inv1 L) (lt_norm_line_inv2 L) (Linear_trans_point (lt_norm_line1 L) (lt_norm_line2 L) p) = p := by{
  unfold lt_norm_line_inv1 lt_norm_line_inv2
  exact linear_trans_point_inv_left (lt_norm_line1 L) (lt_norm_line2 L) (lt_norm_line1_neq_zero L) p
}

lemma lt_norm_line_inv_inv_point_right(L : Line)(p : Point): Linear_trans_point (lt_norm_line1 L) (lt_norm_line2 L) (Linear_trans_point (lt_norm_line_inv1 L) (lt_norm_line_inv2 L) p) = p := by{
  unfold lt_norm_line_inv1 lt_norm_line_inv2
  exact linear_trans_point_inv_right (lt_norm_line1 L) (lt_norm_line2 L) (lt_norm_line1_neq_zero L) p
}

lemma lt_norm_line_inv_inv_set_left(L : Line)(S : Set Point): Linear_trans_set (lt_norm_line_inv1 L) (lt_norm_line_inv2 L) (Linear_trans_set (lt_norm_line1 L) (lt_norm_line2 L) S) = S := by{
  unfold lt_norm_line_inv1 lt_norm_line_inv2
  exact linear_trans_set_inv_left (lt_norm_line1 L) (lt_norm_line2 L) (lt_norm_line1_neq_zero L) S
}

lemma lt_norm_line_inv_inv_set_right(L : Line)(S : Set Point): Linear_trans_set (lt_norm_line1 L) (lt_norm_line2 L) (Linear_trans_set (lt_norm_line_inv1 L) (lt_norm_line_inv2 L) S) = S := by{
  unfold lt_norm_line_inv1 lt_norm_line_inv2
  exact linear_trans_set_inv_right (lt_norm_line1 L) (lt_norm_line2 L) (lt_norm_line1_neq_zero L) S
}

lemma lt_norm_line_inv_inv_line_left(L : Line)(R : Line): Linear_trans_line (lt_norm_line_inv1 L) (lt_norm_line_inv2 L) (Linear_trans_line (lt_norm_line1 L) (lt_norm_line2 L) R) = R := by{
  unfold lt_norm_line_inv1 lt_norm_line_inv2
  exact linear_trans_line_inv_left (lt_norm_line1 L) (lt_norm_line2 L) (lt_norm_line1_neq_zero L) R
}

lemma lt_norm_line_inv_inv_line_right(L : Line)(R : Line): Linear_trans_line (lt_norm_line1 L) (lt_norm_line2 L) (Linear_trans_line (lt_norm_line_inv1 L) (lt_norm_line_inv2 L) R) = R := by{
  unfold lt_norm_line_inv1 lt_norm_line_inv2
  exact linear_trans_line_inv_right (lt_norm_line1 L) (lt_norm_line2 L) (lt_norm_line1_neq_zero L) R
}

--TO DO: PERP LINES STAY PERP, THEREFORE PERP THROUGH STAY THE SAME THEREFORE FOOTS STAY THE SAME
--THEREFORE REFLECTION STAY THE SAME

--THEN : THEORE EXISTS A B WITH A NOT ZERO (IMPORTANT) FOR ANY LINE, SUCH THAT L GETS SENT TO THE REAL LINE

--IN THE ANGLES SECTION THEN SHOW THAT ANGLES ARE PRESERVED UNDER LINEAR TRANS
