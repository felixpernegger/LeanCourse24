import LeanCourse.Project.Powpoint
import Mathlib

open Function Set Classical

noncomputable section


--Angles

#check Complex.arg

/-We now FINALLY deifne angles (I pretty much did everything you can reasonably do without angles lol)-/

/-We will use angles only as directed angles, furthermore, for the time being,
we only define angles between three points. Definining angles between lines is a bit tricky.

We will also make two versions of angles, seen as followed:
-/
#check Complex.arg_mul_coe_angle
#check Real.Angle
def Angle{a b c : Point}(ha : a ≠ b)(hc : c ≠ b): Real.Angle :=
  Complex.arg ((a.x-b.x)/(c.x-b.x))

def qAngle(a b c : Point): Real.Angle :=
  if ha : a ≠ b then (if hc : c ≠ b then (Angle ha hc) else 0) else 0

@[simp] lemma qangle_simp{a b c : Point}(ha : a ≠ b)(hc : c ≠ b): qAngle a b c = Angle ha hc := by{
  unfold qAngle
  simp [*]
}

@[simp] lemma qangle_simp_left(a b c : Point)(ha : a = b): qAngle a b c = 0 := by{
  unfold qAngle
  simp [*]
}

@[simp] lemma qangle_simp_left'(a b c : Point)(ha : b = a): qAngle a b c = 0 := by{
  unfold qAngle
  simp [*]
}

@[simp] lemma qangle_simp_right(a b c : Point)(ha : c = b): qAngle a b c = 0 := by{
  unfold qAngle
  simp [*]
}

@[simp] lemma qangle_simp_right'(a b c : Point)(ha : b = c): qAngle a b c = 0 := by{
  unfold qAngle
  simp [*]
}

/-We prove several elementary but very important properties:-/

lemma angle_self{a b : Point}(ha : a ≠ b): Angle ha ha = 0 := by{
  have asub : a.x-b.x ≠ 0 := by{exact sub_neq_zero ha}
  unfold Angle
  field_simp
}

lemma qangle_self(a b : Point): qAngle a b a = 0 := by{
  by_cases ha: a ≠ b
  · simp [*]
    exact angle_self ha
  simp at ha
  simp [*]
}

lemma angle_add{a b c d : Point}(ha : a ≠ b)(hc : c ≠ b)(hd : d ≠ b): Angle ha hd = Angle ha hc + Angle hc hd := by{
  unfold Angle
  have asub: a.x - b.x ≠ 0 := by{exact sub_neq_zero ha}
  have csub: c.x - b.x ≠ 0 := by{exact sub_neq_zero hc}
  have dsub: d.x - b.x ≠ 0 := by{exact sub_neq_zero hd}
  have rr: (a.x - b.x)/(d.x-b.x) = ((a.x-b.x)/(c.x-b.x))*((c.x-b.x)/(d.x-b.x)) := by{field_simp}
  rw[rr]
  refine Complex.arg_mul_coe_angle ?hx ?hy
  repeat
    by_contra p0
    simp at p0
    tauto
}

lemma angle_symm{a b c : Point}(ha : a ≠ b)(hc : c ≠ b): Angle hc ha = -(Angle ha hc) := by{
  have g: Angle ha ha = Angle ha hc + Angle hc ha := by{exact angle_add ha hc ha}
  rw[angle_self ha] at g
  have : Angle hc ha = Angle hc ha - 0 := by{simp}
  rw[this, g]
  simp
}

lemma qangle_symm(a b c : Point): qAngle a b c = -qAngle c b a := by{
  by_cases ha : a ≠ b
  by_cases hc : c ≠ b
  simp [*]
  rw[angle_symm ha hc]
  simp

  simp at hc
  simp [*]
  simp at ha
  simp [*]
}

/-With this we can already prove the sum of angles in a triangle!-/

theorem anglesum_points{a b c : Point}(h : pairwise_different_point3 a b c): qAngle a b c + qAngle b c a + qAngle c a b = Real.pi := by{
  obtain ⟨h1,h2,h3⟩ := h
  have h1' : b ≠ a :=by{tauto}
  have h2' : c ≠ b :=by{tauto}
  have h3' : a ≠ c :=by{tauto}
  have absub : a.x-b.x ≠ 0 := by{exact sub_neq_zero h1}
  have basub : b.x-a.x ≠ 0 := by{exact sub_neq_zero h1'}
  have bcsub : b.x-c.x ≠ 0 := by{exact sub_neq_zero h2}
  have cbsub : c.x-b.x ≠ 0 := by{exact sub_neq_zero h2'}
  have casub : c.x-a.x ≠ 0 := by{exact sub_neq_zero h3}
  have acsub : a.x-c.x ≠ 0 := by{exact sub_neq_zero h3'}
  simp [*]
  unfold Angle
  have s1: (↑((a.x - b.x) / (c.x - b.x)).arg : Real.Angle) + ↑((b.x - c.x) / (a.x - c.x)).arg = ↑((b.x-a.x)/(a.x-c.x)).arg := by{
    calc
      (↑((a.x - b.x) / (c.x - b.x)).arg : Real.Angle) + ↑((b.x - c.x) / (a.x - c.x)).arg = (((a.x-b.x)/(c.x-b.x))*((b.x-c.x)/(a.x-c.x))).arg := by{
        refine Eq.symm (Complex.arg_mul_coe_angle ?hx ?hy)
        repeat
          field_simp
          assumption
      }
      _= ↑((b.x - a.x) / (a.x - c.x)).arg := by{
        have : (a.x - b.x) / (c.x - b.x) * ((b.x - c.x) / (a.x - c.x)) = (b.x - a.x) / (a.x - c.x) := by{
          field_simp
          ring
        }
        rw[this]
      }
  }
  rw[s1]
  calc
    (↑((b.x - a.x) / (a.x - c.x)).arg : Real.Angle)  + ↑((c.x - a.x) / (b.x - a.x)).arg = (↑(((b.x - a.x) / (a.x - c.x))*((c.x - a.x) / (b.x - a.x))).arg) := by{
      symm
      apply Complex.arg_mul_coe_angle
      repeat
        field_simp
        assumption
    }
      _=((-1:ℂ)).arg := by{
        have : ((b.x - a.x) / (a.x - c.x))*((c.x - a.x) / (b.x - a.x)) = -1 := by{
          field_simp
          ring
        }
        rw[this]
      }
      _= Real.pi := by{simp}
}
#check triangle_pairwise_different

def Angle_A : Triangle → Real.Angle :=
  fun T ↦ Angle (tri_diff_ca T) (tri_diff_ba T)

def Angle_B : Triangle → Real.Angle :=
  fun T ↦ Angle (tri_diff_ab T) (tri_diff_cb T)

def Angle_C : Triangle → Real.Angle :=
  fun T ↦ Angle (tri_diff_bc T) (tri_diff_ac T)

theorem tri_sum_angle(T : Triangle): Angle_A T + Angle_B T + Angle_C T = Real.pi := by{
  have : pairwise_different_point3 T.a T.b T.c := by{exact (triangle_pairwise_different T)}
  unfold Angle_A Angle_B Angle_C
  repeat
    rw[← qangle_simp]
  apply anglesum_points
  apply pairwise_different_point3_perm12
  exact pairwise_different_point3_perm23 this
}

/-The next step is a bit ugly. We prove that angles along a line are either 0 or pi.
The case distinction is necessary, becuase the "center" of the angle is eithe rin the middle
or on the left/right.
This is one of the main reasons, very often one uses directed angles modulo pi. This also has some downsides however,
and we wont introduce them for now.-/

/-We do it in several steps.-/

lemma arg_real{t:ℂ}(h: t.im = 0): Complex.arg t = 0 ∨ Complex.arg t = Real.pi := by{
  have : t = t.re := by{exact Eq.symm (Complex.ext rfl (id (Eq.symm h)))}
  rw[this]
  by_cases h0: 0 ≤ t.re
  left
  exact Complex.arg_ofReal_of_nonneg h0
  right
  simp at *
  exact Complex.arg_ofReal_of_neg h0
}

theorem in_between_angle{a b c : Point}(h : in_between a c b)(ha: a ≠ b)(hc: c ≠ b): Angle ha hc = Real.pi := by{
  have col: colinear a c b := by{exact in_between_imp_colinear h}
  have absub: a.x-b.x ≠ 0 := by{exact sub_neq_zero ha}
  have basub: b.x-a.x ≠ 0 := by{exact sub_neq_zero (id (Ne.symm ha))}
  have cbsub: c.x-b.x ≠ 0 := by{exact sub_neq_zero hc}
  have bcsub: b.x-c.x ≠ 0 := by{exact sub_neq_zero (id (Ne.symm hc))}
  apply colinear_perm13 at col
  apply colinear_perm23 at col
  unfold Angle
  apply (colinear_alt b a c).1 at col
  have : (b.x - a.x) / (b.x - c.x) = (a.x-b.x)/(c.x-b.x) := by{
    field_simp
    ring
  }
  rw[this] at col
  clear this
  obtain h0|h0 := arg_real col
  by_contra p0
  clear p0
  have col2: colinear b a c := by{
    have : (a.x - b.x) / (c.x - b.x) = (b.x-a.x)/(b.x-c.x) := by{
      field_simp
      ring
    }
    rw[this] at col
    exact (colinear_alt b a c).2 col
  }
  apply colinear_perm12 at col2
  have l : a ≠ c := by{
    by_contra p0
    rw[p0] at h col h0
    contrapose hc
    unfold in_between at *
    simp at *
    clear absub basub cbsub bcsub col h0 ha hc p0 col2
    apply abs_zero_imp_same
    rw[point_abs_self c] at h
    rw[point_abs_symm b c] at h
    simp at h
    assumption
  }
  obtain p0|p0 := (colinear_alt2 a b c).1 col2
  · contradiction
  obtain ⟨t, ht⟩ := p0
  have acsub : a.x - c.x ≠ 0 := by{exact sub_neq_zero l}
  have s1: b = go_along a c (t*(point_abs a c)) := by{
    rw[ht]
    unfold go_along padd point_abs dir point_abs p_scal_mul
    ext
    simp
    have : (↑(Complex.abs (a.x - c.x)):ℂ) ≠ 0 := by{
      norm_cast
      exact (AbsoluteValue.ne_zero_iff Complex.abs).mpr acsub
    }
    field_simp
    ring
  }
  unfold in_between at h
  have t1: point_abs a b = abs (t)*(point_abs a c) := by{
    rw[s1]
    rw[go_along_abs1 l (t * point_abs a c)]
    have : point_abs a c = abs (point_abs a c) := by{exact Eq.symm (abs_of_nonneg (point_abs_pos a c))}
    nth_rw 2[this]
    exact abs_mul t (point_abs a c)
  }
  have t2: point_abs b c = abs (1-t) * point_abs a c := by{
    rw[point_abs_symm b c, s1, go_along_abs2 l]
    have u :  point_abs a c - t * point_abs a c =(1-t)*(point_abs a c) := by{ring}
    rw[u]
    clear u
    have : point_abs a c = abs (point_abs a c) := by{exact Eq.symm (abs_of_nonneg (point_abs_pos a c))}
    nth_rw 2[this]
    exact abs_mul (1-t) (point_abs a c)
  }
  rw[t1,t2] at h
  have hh: 0 ≤ t ∧ t ≤ 1 := by{
    have : 0 < point_abs a c := by{
      have : 0 ≤ point_abs a c := by{exact point_abs_pos a c}
      have r: point_abs a c ≠ 0 := by{
        contrapose l
        simp at *
        exact abs_zero_imp_same a c l
      }
      contrapose r
      simp at *
      linarith
    }
    have g: abs t + abs (1-t) = 1 := by{
      calc
        abs t + abs (1-t) = ((abs t)*(point_abs a c) + abs (1-t)*(point_abs a c))/(point_abs a c) := by{field_simp;ring}
          _= (point_abs a c)/(point_abs a c) := by{rw[h]}
          _= 1 := by{field_simp}
    }
    constructor
    by_contra q0
    simp at q0
    have i1: abs t = -t := by{exact abs_of_neg q0}
    have i2: abs (1 - t)= 1-t := by{
      apply abs_of_nonneg
      linarith
    }
    rw[i1,i2] at g
    have t0: t = 0 := by{linarith}
    rw[t0] at ht
    simp at ht
    rw[ht] at absub
    simp at absub

    rw[← g]
    calc
      t ≤ abs t := by{exact le_abs_self t}
        _= abs t + 0 := by{ring}
        _≤ abs t + abs (1-t) := by{
          apply add_le_add
          rfl
          exact abs_nonneg (1 - t)
        }
  }
  obtain ⟨h1,h2⟩ := hh
  rw[ht] at h0
  simp at h0
  have : ↑t * (a.x - c.x) / (c.x - (a.x - ↑t * (a.x - c.x))) = -↑t /(1-↑t) := by{
    have : (c.x - (a.x - ↑t * (a.x - c.x))) = (c.x-a.x)*(1-t) := by{ring}
    rw[this]
    clear this

    have : (1-(↑t : ℂ)) ≠ 0 := by{sorry}
    have : (c.x - a.x) * (1 - ↑t) ≠ 0 := by{
      refine mul_ne_zero ?ha this
      exact sub_neq_zero (id (Ne.symm l))
    }
    field_simp
    ring
  }
  rw[this] at h0
  clear this
  sorry
}
