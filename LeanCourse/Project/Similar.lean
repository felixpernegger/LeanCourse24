import LeanCourse.Project.Thales
import Mathlib

open Function Set Classical

noncomputable section

set_option linter.unusedTactic false

/-In this section we finally introduce similar triangles.
To not make every. single. thing twice., unlike before, we wont be making point versions for each lemma.
-/

/-There are sort of two versions triangles can be similar:
They can be similar in the usual sense
but they can also be similar in the usuall sense and have same orientation

These cases are fundamentally different from each other, and it is adivisable to first
deal with the second notion of similar, which we call "direct similar" or just dsimilar.-/

/-We say two triangles are dsimilar iff there is a linear transformation between them:-/
/-First a "standard trianlge" just for convenience:-/
def std_triangle : Triangle where
  a := zero
  b := one
  c := Point.mk ({re := 0, im := 1})
  noncolinear := by{
    unfold noncolinear colinear det zero one conj
    simp
    norm_num
  }

def Linear_trans_tri: Point → Point → Triangle → Triangle :=
  fun u v T ↦ (if h : u = zero then std_triangle else Triangle.mk (Linear_trans_point u v T.a) (Linear_trans_point u v T.b) (Linear_trans_point u v T.c) (by{
    apply linear_trans_point_noncolinear
    · assumption
    exact T.noncolinear
  }))

def dSimilar(T Q : Triangle): Prop :=
  ∃(a b : Point), a ≠ zero ∧ Q = Linear_trans_tri a b T

@[simp] lemma linear_trans_tri_id(T : Triangle): Linear_trans_tri one zero T = T := by{
  unfold Linear_trans_tri
  simp
}

lemma linear_trans_tri_eq(T : Triangle){a b c d : Point}(h1: a = c)(h2: b = d): Linear_trans_tri a b T = Linear_trans_tri c d T := by{rw[h1,h2]}

lemma linear_trans_tri_id_simp(T : Triangle){a b : Point}(ah : a = one)(bh : b = zero): Linear_trans_tri a b T = T := by{
  rw[ah,bh]
  simp
}

lemma linear_trans_tri_comp(a b : Point)(ah : a ≠ zero)(c d : Point)(ch : c ≠ zero)(T : Triangle): Linear_trans_tri a b (Linear_trans_tri c d T) = Linear_trans_tri (pmul a c) (padd (pmul a d) b) T := by{
  unfold Linear_trans_tri
  simp [*, linear_trans_point_comp]
  have : pmul a c ≠ zero := by{
    unfold pmul zero at *
    simp at *
    constructor
    · contrapose ah
      simp at *
      ext
      rw[ah]
    contrapose ch
    simp at *
    ext
    rw[ch]
  }
  simp [this]
}

lemma linear_trans_tri_inv_left(a b : Point)(ah : a ≠ zero)(T : Triangle): Linear_trans_tri (lt_inv1 a b) (lt_inv2 a b) (Linear_trans_tri a b T) = T := by{
  unfold Linear_trans_tri
  simp [*, linear_trans_point_inv_left, lt_inv1_not_zero]
}

lemma linear_trans_tri_inv_right(a b : Point)(ah : a ≠ zero)(T : Triangle): Linear_trans_tri a b (Linear_trans_tri (lt_inv1 a b) (lt_inv2 a b) T) = T := by{
  unfold Linear_trans_tri
  simp [*, linear_trans_point_inv_right, lt_inv1_not_zero]
}

lemma linear_trans_tri_inj(a b: Point)(ah : a ≠ zero){T Q : Triangle}(h : Linear_trans_tri a b T = Linear_trans_tri a b Q): T = Q := by{
  unfold Linear_trans_tri at h
  simp [*, linear_trans_point_inj] at *
  ext
  have : T.a = Q.a := by{
    apply linear_trans_point_inj a b ah h.1
    }
  simp [*]

  have : T.b = Q.b := by{
    apply linear_trans_point_inj a b ah h.2.1
    }
  simp [*]

  have : T.c = Q.c := by{
    apply linear_trans_point_inj a b ah h.2.2
    }
  simp [*]
}

/-Importantly, angles are preserved. Ww've proved this already earlier, but here the triangle version:-/
lemma linear_trans_tri_angle_a(a b : Point)(ah : a ≠ zero)(T : Triangle): Angle_A (Linear_trans_tri a b T) = Angle_A T := by{
  unfold Angle_A Linear_trans_tri
  simp [*, linear_trans_angle]
}

lemma linear_trans_tri_angle_b(a b : Point)(ah : a ≠ zero)(T : Triangle): Angle_B (Linear_trans_tri a b T) = Angle_B T := by{
  unfold Angle_B Linear_trans_tri
  simp [*, linear_trans_angle]
}

lemma linear_trans_tri_angle_c(a b : Point)(ah : a ≠ zero)(T : Triangle): Angle_C (Linear_trans_tri a b T) = Angle_C T := by{
  unfold Angle_C Linear_trans_tri
  simp [*, linear_trans_angle]
}

/-Now being dSimilar is an equivalence relation:-/

lemma dsimilar_refl(T : Triangle): dSimilar T T := by{
  unfold dSimilar
  use one
  use zero
  constructor
  · exact one_neq_zero
  simp
}

lemma dsimilar_symm{T Q : Triangle}(h: dSimilar T Q): dSimilar Q T := by{
  unfold dSimilar at *
  obtain ⟨a,b,ah,h⟩ := h
  use lt_inv1 a b
  use lt_inv2 a b
  constructor
  · exact lt_inv1_not_zero a b ah
  rw[h, linear_trans_tri_inv_left a b ah]
}

lemma dsimilar_trans{T Q R : Triangle}(TQ: dSimilar T Q)(QR: dSimilar Q R): dSimilar T R := by{
  unfold dSimilar at *
  obtain ⟨a,b,ah,ab⟩ := TQ
  obtain ⟨c,d,ch,cd⟩ := QR
  rw[cd,ab,linear_trans_tri_comp]
  use (pmul c a)
  use (padd (pmul c b) d)
  constructor
  · exact pmul_neq_zero ch ah
  rfl
  assumption
  assumption
}

/-As proven beofre we have same angles:-/
theorem dsimilar_imp_same_angles{T Q : Triangle}(h : dSimilar T Q): Angle_A T = Angle_A Q ∧ Angle_B T = Angle_B Q ∧ Angle_C T = Angle_C Q := by{
  unfold dSimilar at h
  obtain ⟨a,b,ah,h⟩ := h
  rw[h]
  simp [*, linear_trans_tri_angle_a, linear_trans_tri_angle_b, linear_trans_tri_angle_c]
}

lemma dsimilar_angle_a{T Q : Triangle}(h : dSimilar T Q): Angle_A T = Angle_A Q := by{
  exact (dsimilar_imp_same_angles h).1
}

lemma dsimilar_angle_b{T Q : Triangle}(h : dSimilar T Q): Angle_B T = Angle_B Q := by{
  exact (dsimilar_imp_same_angles h).2.1
}

lemma dsimilar_angle_c{T Q : Triangle}(h : dSimilar T Q): Angle_C T = Angle_C Q := by{
  exact (dsimilar_imp_same_angles h).2.2
}

/-Next we want to show the (in my opinion not super obvious) fact that
if T and Q are similar, the a,b translating them are unique.-/

/-For this we first show (which basically already is the fact)
that 2 pairs of points we have unique linear trans between them-/

/-We do this in some steps:-/
lemma two_pairs_ex_linear_trans(a b c d : Point)(ab : a ≠ b): ∃(u v : Point), Linear_trans_point u v a = c ∧ Linear_trans_point u v b = d := by{
  use Point.mk ((c.x-d.x)/(a.x-b.x))
  use Point.mk ((a.x*d.x - b.x*c.x)/(a.x-b.x))
  have absub: a.x-b.x ≠ 0 := by{exact sub_neq_zero ab}
  unfold Linear_trans_point padd pmul
  field_simp
  constructor
  · ext
    field_simp
    ring
  ext
  field_simp
  ring
}

/-If c and d are disjoin u ≠ zero:-/
lemma two_pair_linear_trans_neq_zero{a b c d u v : Point}(cd : c ≠ d)(ac: Linear_trans_point u v a = c)(bd: Linear_trans_point u v b = d): u ≠ zero := by{
  contrapose cd
  simp at *
  rw[cd] at ac bd
  rw[← ac, ← bd]
  unfold Linear_trans_point zero padd pmul
  ext
  simp
}

lemma two_pairs_linears_trans_ex{a b c d : Point}(ab : a ≠ b){u v : Point}(uv : Linear_trans_point u v a = c ∧ Linear_trans_point u v b = d): u = Point.mk ((c.x-d.x)/(a.x-b.x)) ∧ v = Point.mk ((a.x*d.x - b.x*c.x)/(a.x-b.x)) := by{
  have absub: a.x-b.x ≠ 0 := by{exact sub_neq_zero ab}
  unfold Linear_trans_point padd pmul at *
  have s1 : ({ x := ({ x := u.x * a.x } : Point).x + v.x }: Point).x = c.x ∧ ({ x := ({ x := u.x * b.x } : Point).x + v.x } : Point).x = d.x := by{
    rw[uv.1,uv.2]
    tauto
  }
  simp at s1
  obtain ⟨s1,s2⟩ := s1
  have t1: u.x * (a.x-b.x) = c.x-d.x := by{
    ring_nf
    calc
      u.x * a.x - u.x * b.x = (u.x * a.x + v.x) - (u.x * b.x + v.x) := by{ring}
        _= c.x - d.x := by{rw[s1,s2]}
  }
  have g1: u.x = (c.x-d.x)/(a.x - b.x) := by{
    field_simp [t1]
  }
  constructor
  · ext
    simp [*]
  ext
  simp
  calc
    v.x = c.x - ((c.x - d.x) / (a.x - b.x)) * a.x := by{rw[← g1,← s1]; ring}
      _= (a.x * d.x - b.x * c.x) / (a.x - b.x) := by{
        field_simp
        ring
      }
}

lemma two_pairs_linear_trans_unique(a b c d : Point)(ab : a ≠ b){u v r s : Point}(uv : Linear_trans_point u v a = c ∧ Linear_trans_point u v b = d)(rs : Linear_trans_point r s a = c ∧ Linear_trans_point r s b = d): u = r ∧ v = s := by{
  rw[(two_pairs_linears_trans_ex ab uv).1, (two_pairs_linears_trans_ex ab rs).1, (two_pairs_linears_trans_ex ab uv).2, (two_pairs_linears_trans_ex ab rs).2]
  tauto
}

/-Now we define the "scale factor" between similar triangles.
As we will need to first variable "a" way more often we call
the 1st (a) scale factor and the 2nd (b) dshift_factor:-/
lemma similar_imp_ex{T Q : Triangle}(h : dSimilar T Q): ∃(a b : Point), a ≠ zero ∧ Q = Linear_trans_tri a b T := by{
  unfold dSimilar at h
  assumption
}

def dScale_factor{T Q : Triangle}(h : dSimilar T Q): Point :=
  choose (similar_imp_ex h)

lemma dscale_factor_ex_shift{T Q : Triangle}(h : dSimilar T Q): ∃(b : Point), dScale_factor h ≠ zero ∧ Linear_trans_tri (dScale_factor h) b T = Q := by{
  unfold dScale_factor
  obtain ⟨b,bh1,bh2⟩ := Exists.choose_spec (similar_imp_ex h)
  use b
  tauto
}

def dShift_factor{T Q : Triangle}(h : dSimilar T Q): Point :=
  choose (dscale_factor_ex_shift h)

/-And quick versions:-/
def qdScale_factor(T Q : Triangle) : Point :=
  if h : dSimilar T Q then dScale_factor h else zero

def qdShift_factor(T Q : Triangle) : Point :=
  if h : dSimilar T Q then dShift_factor h else zero

@[simp] lemma qdscale_factor_simp{T Q : Triangle}(h : dSimilar T Q): qdScale_factor T Q = dScale_factor h := by{
  unfold qdScale_factor
  simp [*]
}

@[simp] lemma qdshift_factor_simp{T Q : Triangle}(h : dSimilar T Q): qdShift_factor T Q = dShift_factor h := by{
  unfold qdShift_factor
  simp [*]
}

/-This satistfies the usual stuff:-/
@[simp] lemma dscale_factor_neq_zero{T Q : Triangle}(h: dSimilar T Q): dScale_factor h ≠ zero := by{
  exact (Exists.choose_spec (dscale_factor_ex_shift h)).1
}

lemma dscale_factor_dshift_factor{T Q : Triangle}(h: dSimilar T Q): Linear_trans_tri (dScale_factor h) (dShift_factor h) T = Q := by{
  unfold dShift_factor
  exact (Exists.choose_spec (dscale_factor_ex_shift h)).2
}

/-The scale and shift factor are unique!-/
lemma factors_imp_similar{T Q : Triangle}{u v : Point}(uh : u ≠ zero)(uv : Linear_trans_tri u v T = Q) : dSimilar T Q := by{
  unfold dSimilar
  use u
  use v
  tauto
}

theorem dscale_factor_dshift_factor_unique{T Q : Triangle}{u v : Point}(uh : u ≠ zero)(uv : Linear_trans_tri u v T = Q): u = dScale_factor (factors_imp_similar uh uv) ∧ v = dShift_factor (factors_imp_similar uh uv) := by{
  have h: dSimilar T Q := by{
    unfold dSimilar
    use u
    use v
    tauto
  }
  have ab: T.a ≠ T.b := by{
    exact tri_diff_ab T
  }
  apply two_pairs_linear_trans_unique T.a T.b Q.a Q.b ab
  unfold Linear_trans_tri at uv
  obtain ⟨a,b,c,hT⟩ := T
  obtain ⟨r,s,t,hQ⟩ := Q
  simp [*] at *
  obtain ⟨uv1,uv2,uv3,uv4⟩ := uv
  tauto

  have g: Linear_trans_tri (dScale_factor h) (dShift_factor h) T = Q := by{exact dscale_factor_dshift_factor h}
  unfold Linear_trans_tri at *
  obtain ⟨a,b,c,hT⟩ := T
  obtain ⟨r,s,t,hQ⟩ := Q
  simp [*] at *
  tauto
}

/-Or more simply:-/
lemma dscale_and_ex_imp_dsimilar{T Q : Triangle}{u : Point}(uh : u ≠ zero)(uh' : ∃(v : Point), Linear_trans_tri u v T = Q): dSimilar T Q := by{
  obtain ⟨v,vh⟩ := uh'
  unfold dSimilar
  use u
  use v
  tauto
}

theorem dscale_factor_unique{T Q : Triangle}{u : Point}(uh : u ≠ zero)(uh' : ∃(v : Point), Linear_trans_tri u v T = Q): u = dScale_factor (dscale_and_ex_imp_dsimilar uh uh') := by{
  obtain ⟨v,vh⟩ := uh'
  exact (dscale_factor_dshift_factor_unique uh vh).1
}

lemma dshift_and_ex_imp_dsimilar{T Q : Triangle}{v : Point}(vh: ∃(u : Point), u ≠ zero ∧ Linear_trans_tri u v T = Q): dSimilar T Q := by{
  obtain ⟨u,uh⟩ := vh
  unfold dSimilar
  use u
  use v
  tauto
}

theorem dshift_factor_unique{T Q : Triangle}{v : Point}(vh: ∃(u : Point), u ≠ zero ∧ Linear_trans_tri u v T = Q): v = dShift_factor (dshift_and_ex_imp_dsimilar vh) := by{
  obtain ⟨u,uh1,uh2⟩ := vh
  exact (dscale_factor_dshift_factor_unique uh1 uh2).2
}
--(pmul a c) (padd (pmul a d) b)
/-Under compositions these factors obviously behave like linear_trans_..._comp:-/
lemma dscale_factor_comp{T Q R : Triangle}(TQ: dSimilar T Q)(QR: dSimilar Q R): dScale_factor (dsimilar_trans TQ QR) = pmul (dScale_factor QR) (dScale_factor TQ) := by{
  symm
  apply dscale_factor_unique
  · exact pmul_neq_zero (dscale_factor_neq_zero QR) (dscale_factor_neq_zero TQ)
  use padd (pmul (dScale_factor QR) (dShift_factor TQ)) (dShift_factor QR)
  rw[← linear_trans_tri_comp, dscale_factor_dshift_factor, dscale_factor_dshift_factor]
  exact dscale_factor_neq_zero QR
  exact dscale_factor_neq_zero TQ
}

lemma dshift_factor_comp{T Q R : Triangle}(TQ : dSimilar T Q)(QR: dSimilar Q R): dShift_factor (dsimilar_trans TQ QR) = padd (pmul (dScale_factor QR) (dShift_factor TQ)) (dShift_factor QR) := by{
  symm
  apply dshift_factor_unique
  use pmul (dScale_factor QR) (dScale_factor TQ)
  constructor
  · exact pmul_neq_zero (dscale_factor_neq_zero QR) (dscale_factor_neq_zero TQ)
  rw[← linear_trans_tri_comp, dscale_factor_dshift_factor, dscale_factor_dshift_factor]
  exact dscale_factor_neq_zero QR
  exact dscale_factor_neq_zero TQ
}

/-Therefore scale factors of inverse stuff is lt_inv:-/

lemma dscale_factor_refl(T : Triangle): dScale_factor (dsimilar_refl T) = one := by{
  symm
  apply dscale_factor_unique
  · exact one_neq_zero
  use zero
  exact linear_trans_tri_id T
}

lemma dshift_factor_refl(T : Triangle): dShift_factor (dsimilar_refl T) = zero := by{
  symm
  apply dshift_factor_unique
  use one
  constructor
  · exact one_neq_zero
  exact linear_trans_tri_id T
}

/-For the two lemmas here, rw bugged, so i had to do it a bit weirdly.-/
lemma dscale_factor_symm{T Q : Triangle}(h : dSimilar T Q): dScale_factor (dsimilar_symm h) = lt_inv1 (dScale_factor h) (dShift_factor h) := by{
  symm
  apply dscale_factor_unique
  · exact lt_inv1_not_zero (dScale_factor h) (dShift_factor h) (dscale_factor_neq_zero h)
  use lt_inv2 (dScale_factor h) (dShift_factor h)
  have t: Linear_trans_tri (dScale_factor h) (dShift_factor h) T = Q := by{exact dscale_factor_dshift_factor h}
  have tt: Linear_trans_tri (lt_inv1 (dScale_factor h) (dShift_factor h)) (lt_inv2 (dScale_factor h) (dShift_factor h))
    (Linear_trans_tri (dScale_factor h) (dShift_factor h) T) =
  T := by{
    exact linear_trans_tri_inv_left (dScale_factor h) (dShift_factor h) (dscale_factor_neq_zero h) T
  }
  rw[t] at tt
  assumption
}

lemma dshift_factor_symm{T Q : Triangle}(h : dSimilar T Q): dShift_factor (dsimilar_symm h) = lt_inv2 (dScale_factor h) (dShift_factor h) := by{
  symm
  apply dshift_factor_unique
  use lt_inv1 (dScale_factor h) (dShift_factor h)
  constructor
  · exact lt_inv1_not_zero (dScale_factor h) (dShift_factor h) (dscale_factor_neq_zero h)
  have t: Linear_trans_tri (dScale_factor h) (dShift_factor h) T = Q := by{exact dscale_factor_dshift_factor h}
  have tt: Linear_trans_tri (lt_inv1 (dScale_factor h) (dShift_factor h)) (lt_inv2 (dScale_factor h) (dShift_factor h))
    (Linear_trans_tri (dScale_factor h) (dShift_factor h) T) =
  T := by{
    exact linear_trans_tri_inv_left (dScale_factor h) (dShift_factor h) (dscale_factor_neq_zero h) T
  }
  rw[t] at tt
  assumption
}

/-The lenghts of the sides of traingles are scaling with scale factor!-/

/-Once again rw is bugging with dscale_factor_dshift_factor, so I use an (unnecessary) have tactic...-/
lemma dsimilar_abs_tri_ab{T Q : Triangle}(h : dSimilar T Q): abs_tri_ab Q = (pabs (dScale_factor h)) * (abs_tri_ab T) := by{
  have : abs_tri_ab (Linear_trans_tri (dScale_factor h) (dShift_factor h) T) = abs_tri_ab Q := by{
    rw[dscale_factor_dshift_factor h]
  }
  rw[← this]
  unfold Linear_trans_tri abs_tri_ab
  simp [dscale_factor_neq_zero, linear_trans_point_point_abs]
}

lemma dsimilar_abs_tri_bc{T Q : Triangle}(h : dSimilar T Q): abs_tri_bc Q = (pabs (dScale_factor h)) * (abs_tri_bc T) := by{
  have : abs_tri_bc (Linear_trans_tri (dScale_factor h) (dShift_factor h) T) = abs_tri_bc Q := by{
    rw[dscale_factor_dshift_factor h]
  }
  rw[← this]
  unfold Linear_trans_tri abs_tri_bc
  simp [dscale_factor_neq_zero, linear_trans_point_point_abs]
}

lemma dsimilar_abs_tri_ca{T Q : Triangle}(h : dSimilar T Q): abs_tri_ca Q = (pabs (dScale_factor h)) * (abs_tri_ca T) := by{
  have : abs_tri_ca (Linear_trans_tri (dScale_factor h) (dShift_factor h) T) = abs_tri_ca Q := by{
    rw[dscale_factor_dshift_factor h]
  }
  rw[← this]
  unfold Linear_trans_tri abs_tri_ca
  simp [dscale_factor_neq_zero, linear_trans_point_point_abs]
}

/-And so does the area: (squared)-/

lemma dsimilar_area_tri{T Q : Triangle}(h : dSimilar T Q): area_tri Q = (pabs (dScale_factor h))^2 * area_tri T := by{
  have : area_tri (Linear_trans_tri (dScale_factor h) (dShift_factor h) T) = area_tri Q := by{
    rw[dscale_factor_dshift_factor]
  }
  rw[← this]
  unfold area_tri Linear_trans_tri area_points det conj Linear_trans_point pmul padd pabs
  simp [dscale_factor_neq_zero]
  ring_nf
  field_simp
  set a1 := T.a.x.re
  set a2 := T.a.x.im
  set b1 := T.b.x.re
  set b2 := T.b.x.im
  set c1 := T.c.x.re
  set c2 := T.c.x.im
  unfold Complex.abs Complex.normSq
  simp
  set s1 := (dScale_factor h).x.re
  set s2 := (dScale_factor h).x.im
  ring_nf
  have : √(s1 ^ 2 + s2 ^ 2) ^ 2 = s1^2 + s2^2 := by{
    refine Real.sq_sqrt ?h
    nlinarith
  }
  rw[this]
  ring
}

/-Very very importtantly triangles are dsimilar iff they have same angles.
The "→" direction we showed already. The other direction is the last thing we will say
about dsimilar for now.-/

theorem same_angles_imp_dsmimilar{T Q : Triangle}(hA: Angle_A T = Angle_A Q)(hB: Angle_B T = Angle_B Q)(hC: Angle_C T = Angle_C Q): dSimilar T Q := by{
  have tab: T.a ≠ T.b := by{
    exact tri_diff_ab T
  }
  have qab: Q.a ≠ Q.b := by{
    exact tri_diff_ab Q
  }
  obtain ⟨u,v,tqa,tqb⟩ := two_pairs_ex_linear_trans T.a T.b Q.a Q.b tab
  have s1: u ≠ zero := by{
    exact two_pair_linear_trans_neq_zero qab tqa tqb
  }
  suffices goal: Q.c = Linear_trans_point u v T.c
  · unfold dSimilar
    use u
    use v
    constructor
    · exact s1
    unfold Linear_trans_tri
    simp [*]
    ext
    rw[← tqa]
    simp
    rw[goal]

  have c1: colinear Q.a Q.c (Linear_trans_point u v T.c) := by{
    apply angle_out_same_imp_colinear Q.b
    · exact id (Ne.symm qab)
    unfold Angle_A at hA
    rw[angle_symm, angle_symm (Linear_trans_point u v T.c), ← hA, ← tqa, ← tqb]
    simp
    symm
    exact linear_trans_angle u v s1 T.c T.a T.b
  }

  have c2: colinear Q.b Q.c (Linear_trans_point u v T.c) := by{
    apply angle_out_same_imp_colinear Q.a
    · exact qab
    unfold Angle_B at hB
    rw[← hB, ← tqa, ← tqb]
    symm
    exact linear_trans_angle u v s1 T.a T.b T.c
  }

  rw[← tri_c_intersection_ca_bc]
  symm
  apply intersection_unique
  unfold Lies_on tri_ca tri_bc Line_through
  simp [*]
  apply colinear_perm12
  assumption
}

/-Obviously we dont always want to show all 3 angles, because of angle sum 2 suffice already.
/(We actually didnt evene use hC in the proof above lol)-/

lemma same_angles_imp_dsimilar_ab{T Q : Triangle}(hA: Angle_A T = Angle_A Q)(hB: Angle_B T = Angle_B Q): dSimilar T Q := by{
  apply same_angles_imp_dsmimilar hA hB
  rw[tri_sum_angle_c T, tri_sum_angle_c Q, hA, hB]
}

lemma same_angles_imp_dsimilar_bc{T Q : Triangle}(hB: Angle_B T = Angle_B Q)(hC: Angle_C T = Angle_C Q): dSimilar T Q := by{
  refine same_angles_imp_dsmimilar ?_ hB hC
  rw[tri_sum_angle_a T, tri_sum_angle_a Q, hB, hC]
}

lemma same_angles_imp_dsimilar_ca{T Q : Triangle}(hC: Angle_C T = Angle_C Q)(hA: Angle_A T = Angle_A Q): dSimilar T Q := by{
  refine same_angles_imp_dsmimilar hA ?_ hC
  rw[tri_sum_angle_b T, tri_sum_angle_b Q, hA, hC]
}

/-A second way to check for similar triangles, is to have 1 angle and same proportions of
the sides adjacent to it (for this it is actually important we use directed angles):-/
/-Unfortunately unlike the theorem before this we have no "general" version.
Furthermore, the proof is kind of ugly because it is not symmetric despite the statment being-/
theorem same_angle_same_prop_imp_dsimilar_a{T Q : Triangle}(hA: Angle_A T = Angle_A Q)(h: (abs_tri_ab Q)/(abs_tri_ab T) = (abs_tri_ca Q)/(abs_tri_ca T)): dSimilar T Q := by{
  have tab: T.a ≠ T.b := by{exact tri_diff_ab T}
  have qab: Q.a ≠ Q.b := by{exact tri_diff_ab Q}
  have qac: Q.a ≠ Q.c := by{exact tri_diff_ac Q}
  obtain ⟨u,v,tqa,tqb⟩ := two_pairs_ex_linear_trans T.a T.b Q.a Q.b tab
  have s1: u ≠ zero := by{exact two_pair_linear_trans_neq_zero qab tqa tqb}

  suffices goal: Q.c = Linear_trans_point u v T.c
  · unfold dSimilar
    use u
    use v
    constructor
    · exact s1
    unfold Linear_trans_tri
    simp [*]
    ext
    rw[← tqa]
    simp
    rw[goal]

  have c1: colinear Q.a Q.c (Linear_trans_point u v T.c) := by{
    apply angle_out_same_imp_colinear Q.b
    · exact id (Ne.symm qab)
    unfold Angle_A at hA
    rw[angle_symm, angle_symm (Linear_trans_point u v T.c), ← hA, ← tqa, ← tqb]
    simp
    symm
    exact linear_trans_angle u v s1 T.c T.a T.b
  }
  sorry
  #check colinear_go_along
}

--DO THINGY HERE!!! with the sides and angle
