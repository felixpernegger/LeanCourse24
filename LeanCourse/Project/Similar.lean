import LeanCourse.Project.Thales
import Mathlib

open Function Set Classical

noncomputable section

set_option linter.unusedTactic false

/-
def oldSimilar (T Q : Triangle) : Prop :=
  ∃z : ℂ, (z* T.a.x = Q.a.x) ∧ (z* T.b.x = Q.b.x) ∧ (z* T.c.x = Q.c.x)

/-For more general cases, see Similar and direct Similar.-/
/-Note that the scaling factor cant be 0:-/
lemma oldsimilar_neq_zero {T Q : Triangle}(z : ℂ)(zh : (z* T.a.x = Q.a.x) ∧ (z* T.b.x = Q.b.x) ∧ (z* T.c.x = Q.c.x)) : z≠ 0 := by{
  by_contra p
  rw[p] at zh
  simp at zh
  obtain ⟨a,b,c, q⟩ := Q
  simp at zh
  unfold noncolinear at q
  unfold colinear at q
  unfold det at q
  unfold conj at q
  push_neg at q
  obtain ⟨zh1,zh2,zh3⟩ := zh
  rw[← zh1 ,← zh2,← zh3] at q
  simp at q
}

/-Lets show being oldsimilar is an equivalence relation:-/

lemma oldsimilar_refl (T : Triangle) : oldSimilar T T := by{
  use 1
  simp
}

lemma oldsimilar_symm (T Q : Triangle) (h : oldSimilar T Q) : oldSimilar Q T := by{
  obtain ⟨z,zh⟩ := h
  have : z ≠ 0 := by{
    exact oldsimilar_neq_zero z zh
    }
  use z⁻¹
  obtain ⟨zh1,zh2,zh3⟩ := zh
  rw[← zh1, ← zh2, ← zh3]
  field_simp [this]
}

lemma oldsimilar_trans {T Q R: Triangle} (h : oldSimilar T Q) (h': oldSimilar Q R): oldSimilar T R := by{
  obtain ⟨z,zh⟩ := h
  obtain ⟨v, vh⟩ := h'
  use v*z
  obtain ⟨zh1,zh2,zh3⟩ := zh
  obtain ⟨vh1,vh2,vh3⟩ := vh
  repeat
    rw[mul_assoc]
  rw[zh1, zh2, zh3, vh1, vh2, vh3]
  tauto
}

/-conjugating "very" similar triangles gives very similar triangles:-/

lemma oldsimilar_conj {T Q : Triangle}(h : oldSimilar T Q): oldSimilar (tri_conj T) (tri_conj Q) := by{
  unfold oldSimilar at *
  obtain ⟨r,rh⟩ := h
  use conj r
  unfold tri_conj pconj
  simp
  repeat
    rw[← conj_mul']
  tauto
}

/-To obtain the scaling factor we define a function for arbitrary triangles. This works as at there has to be at least one "pair" where eahc coordinates are nonzero-/

/-
def scale_factor : Triangle → Triangle → ℝ :=
  fun T Q ↦ max (max (Complex.abs (T.a.x / Q.a.x)) (Complex.abs (T.b.x / Q.b.x))) (Complex.abs (T.c.x / Q.c.x))

/-With this we can prove that lengths scale according to this:-/
lemma ab_scal (T Q : Triangle)(h : oldSimilar T Q) : (abs_tri_ab T) = (scale_factor T Q) * (abs_tri_ab Q) := by{
  apply oldsimilar_symm at h
  unfold scale_factor
  unfold abs_tri_ab
  unfold oldSimilar at h
  unfold point_abs
  obtain ⟨z,⟨zh1,zh2,zh3⟩⟩ := h
  rw[← zh1]
  rw[← zh2]
  rw[← zh3]
  have this (i : ℂ) (h: ¬(i = 0)): Complex.abs z * Complex.abs i / Complex.abs i = Complex.abs z := by{field_simp [h]}
  by_cases u1: Q.a.x = 0
  rw[u1]
  simp
  by_cases u2: Q.b.x = 0
  right
  assumption
  left
  rw[this Q.b.x u2]
  by_cases u3: Q.c.x = 0
  rw[u3]
  simp

  rw[this Q.c.x u3]
  simp

  simp
  rw[this Q.a.x u1]
  by_cases u2: Q.b.x = 0
  rw[u2]
  simp
  left
  by_cases u3: Q.c.x = 0
  rw[u3]
  simp
  rw[this Q.c.x u3]
  simp

  rw[this Q.b.x u2]
  simp
  by_cases u3: Q.c.x = 0
  rw[u3]
  simp
  calc
    Complex.abs (z * Q.a.x - z * Q.b.x) = Complex.abs (z * (Q.a.x - Q.b.x)) := by ring_nf
      _= (Complex.abs z) * Complex.abs (Q.a.x -Q.b.x) := by exact AbsoluteValue.map_mul Complex.abs z (Q.a.x - Q.b.x)
  sorry
}
-/

/-The version of Similar triangles actually useable are the following:-/

/-direct similar means, we cannont mirror (this preserves directed area and angles)-/
/-omfg i suck-/

def directSimilar (T Q : Triangle) : Prop :=
  ∃p : Point, oldSimilar (tri_shift T p) (Q)

/-directSimilar is weaker than oldSimilar:-/

lemma oldsimilar_imp_directsimilar {T Q : Triangle} (h: oldSimilar T Q) : directSimilar T Q := by{
  use Point.mk 0
  rw[tri_shift_zero]
  assumption
}

/-This again is a equivalence relation:-/

lemma directsimilar_refl (T : Triangle) : directSimilar T T :=  by{
  use Point.mk 0
  rw[tri_shift_zero]
  exact oldsimilar_refl T
}

lemma directsimilar_symm {T Q : Triangle} (h: directSimilar T Q) : directSimilar Q T := by{
  unfold directSimilar at *
  unfold oldSimilar at *
  obtain ⟨p,hp⟩ := h
  obtain ⟨r,rh1,rh2,rh3⟩ := hp
  use Point.mk (-p.x * r)
  use 1/r
  unfold tri_shift padd at *
  simp at *
  have : r≠ 0 := by{
    by_contra h0
    rw[h0] at rh1 rh2 rh3
    simp at *
    obtain ⟨a,b,c,h⟩ := Q
    unfold noncolinear colinear det at h
    simp at *
    rw[← rh1,← rh2,← rh3] at h
    simp at h
  }
  rw[← rh1,← rh2,← rh3]
  field_simp
  ring_nf
  tauto
}

lemma directsimilar_trans{T Q R : Triangle}(TQ : directSimilar T Q)(QR: directSimilar Q R) : directSimilar T R := by{
  unfold directSimilar at *
  obtain ⟨p,hp⟩ := TQ
  obtain ⟨q,hq⟩ := QR
  unfold oldSimilar at *
  obtain ⟨n,hn⟩ := hp
  obtain ⟨m,hm⟩ := hq
  use (Point.mk (q.x /n +p.x))
  use n*m
  unfold tri_shift at *
  unfold padd at *
  simp at *
  obtain ⟨hn1,hn2,hn3⟩ := hn
  obtain ⟨hm1,hm2,hm3⟩ := hm
  rw[← hm1, ← hn1,← hm2, ← hn2,← hm3, ← hn3]
  have : n≠ 0 := by{
    by_contra h0
    rw[h0] at hn1 hn2 hn3
    simp at *
    obtain ⟨a,b,c,Q2⟩ := Q
    simp at *
    unfold noncolinear colinear det at Q2
    rw[← hn1,← hn2,← hn3] at Q2
    simp at Q2
   }
  field_simp
  ring_nf
  tauto
}
/-Mirrorring is cool:-/
lemma directsimilar_conj {T Q : Triangle}(h: directSimilar T Q) : directSimilar (tri_conj T) (tri_conj Q) := by{
  unfold directSimilar at *
  obtain ⟨p,hp⟩ := h
  use pconj p
  unfold oldSimilar at *
  obtain ⟨r,hr1,hr2,hr3⟩ := hp
  use conj r
  unfold tri_conj pconj tri_shift padd conj
  simp
  rw[← hr1,← hr2,← hr3]
  unfold tri_shift padd
  simp
}

/-Antisimilar is now define as being similar to the mirrored:-/

def antiSimilar (T Q : Triangle) : Prop :=
  directSimilar T (tri_conj Q)

/-AntiSimilar is a bit more awkward:-/
lemma antisimilar_pseudo_refl (T: Triangle) : antiSimilar T (tri_conj T) := by{
  unfold antiSimilar
  rw[tri_conj_twice]
  exact directsimilar_refl T
}

lemma antisimilar_symm {T Q : Triangle}(h : antiSimilar T Q) : antiSimilar Q T := by{
  unfold antiSimilar at *
  apply directsimilar_symm
  rw[← tri_conj_twice Q]
  exact directsimilar_conj h
}

lemma antisimilar_pseudo_trans {T Q R : Triangle}(TQ: antiSimilar T Q)(QR : antiSimilar Q R) : directSimilar T R := by{
  unfold antiSimilar at *
  have : directSimilar (tri_conj Q) R := by{
    rw[← tri_conj_twice R]
    exact directsimilar_conj QR
  }
  exact directsimilar_trans TQ this
}

lemma antisimilar_conj {T Q : Triangle}(TQ: antiSimilar T Q) : antiSimilar (tri_conj T) (tri_conj Q) := by{
  unfold antiSimilar at *
  exact directsimilar_conj TQ
}

/-the usual definition of Similar is the following:-/

def Similar (T Q : Triangle) : Prop :=
  directSimilar T Q ∨ antiSimilar T Q

/- Similar is weaker than antiSimilar, directSimilar and oldSimilar:-/

lemma antisimilar_imp_similar {T Q : Triangle}(h: antiSimilar T Q) : Similar T Q := by{
  right
  assumption
}

lemma directsimilar_imp_similar {T Q : Triangle}(h: directSimilar T Q) : Similar T Q := by{
  left
  assumption
}

lemma oldsimilar_imp_similar {T Q : Triangle}(h: oldSimilar T Q) : Similar T Q := by{
  apply directsimilar_imp_similar
  exact oldsimilar_imp_directsimilar h
}

/-once again being Similar is an equivalence relation:-/


lemma similar_refl (T : Triangle) : Similar T T := by{
  unfold Similar
  left
  exact directsimilar_refl T
}

lemma similar_symm {T Q : Triangle}(h : Similar T Q) : Similar Q T := by{
  unfold Similar at *
  obtain h|h := h
  left
  exact directsimilar_symm h
  right
  exact antisimilar_symm h
}

lemma similar_trans {T Q R : Triangle}(TQ : Similar T Q)(QR : Similar Q R) : Similar T R := by{
  unfold Similar at *
  obtain h|h := TQ
  obtain h'|h' := QR
  left
  exact directsimilar_trans h h'
  right
  unfold antiSimilar at *
  exact directsimilar_trans h h'

  obtain h'|h' := QR
  right
  unfold antiSimilar at *
  have : directSimilar (tri_conj Q) (tri_conj R) := by{
    exact directsimilar_conj h'
  }
  exact directsimilar_trans h this

  left
  exact antisimilar_pseudo_trans h h'
}

/-following may be useful:-/
lemma similar_conj {T Q : Triangle} (h: Similar T Q) : Similar T (tri_conj Q) := by{
  unfold Similar at *
  obtain h|h := h
  right
  unfold antiSimilar
  rw[tri_conj_twice]
  assumption
  unfold antiSimilar at h
  left
  assumption
}-/


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
#check real_line

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
