import LeanCourse.Project.Powpoint
import Mathlib

open Function Set Classical

noncomputable section


--Angles

#check Complex.arg

/-We now FINALLY deifne angles (I pretty much did everything you can reasonably do without angles lol)-/

/-We will use angles only as directed angles, furthermore, for the time being,
we only define angles between three points. Definining angles between lines is a bit tricky.
-/
#check Complex.arg_mul_coe_angle
#check Real.Angle
def Angle : Point → Point → Point → Real.Angle :=
  fun a b c ↦ Complex.arg ((a.x-b.x)/(c.x-b.x))

@[simp] lemma angle_simp_left(a b c : Point)(ha : a = b): Angle a b c = 0 := by{
  unfold Angle
  simp [*]
}

@[simp] lemma angle_simp_left'(a b c : Point)(ha : b = a): Angle a b c = 0 := by{
  unfold Angle
  simp [*]
}

@[simp] lemma angle_simp_right(a b c : Point)(ha : c = b): Angle a b c = 0 := by{
  unfold Angle
  simp [*]
}

@[simp] lemma angle_simp_right'(a b c : Point)(ha : b = c): Angle a b c = 0 := by{
  unfold Angle
  simp [*]
}

/-A small lemma for convencience:-/
lemma same_arg_simp{x y : ℂ}(h : x = y): x.arg = y.arg := by{rw[h]}

/-Another!-/
@[simp] lemma arg_conj(x : ℂ): (conj x).arg = if x.arg = Real.pi then Real.pi else -x.arg
 := by{
  unfold conj
  rw [Complex.arg_conj]
}

lemma arg_pi_div_two{z : ℂ}(h: (↑z.arg : Real.Angle) = (↑(Real.pi / 2) : Real.Angle)): z.arg = Real.pi / 2 := by{
  obtain ⟨k,kh⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 h
  have hh: z.arg = 2*Real.pi * k + Real.pi/2 := by{linarith}
  clear kh
  have goal: k = 0 := by{
    apply le_antisymm
    have : 2 * Real.pi * ↑k + Real.pi / 2 ≤ Real.pi := by{
      rw[← hh]
      exact Complex.arg_le_pi z
    }
    have tt: Real.pi* k ≤ Real.pi*1/4 := by{linarith}

    have t1: (↑k:ℝ) ≤ 1/4 := by{
      simp [*] at tt
      have : Real.pi * (1/4) = Real.pi / 4 := by{ring}
      rw[← this] at tt
      exact le_of_mul_le_mul_left tt Real.pi_pos
    }
    contrapose t1
    simp at *
    have : (↑1 : ℝ) ≤ (↑k : ℝ) := by{exact Int.cast_one_le_of_pos t1}
    have : 4⁻¹ < (1:ℝ) := by{norm_num}
    linarith

    have :  -Real.pi < 2 * Real.pi * ↑k + Real.pi / 2 := by{
      rw[← hh]
      exact Complex.neg_pi_lt_arg z
    }
    have tt: Real.pi*(-3/4) ≤ Real.pi*k := by{linarith}
    have g: (-3/4 : ℝ) ≤ (↑k:ℝ) := by{
      exact le_of_mul_le_mul_left tt Real.pi_pos
    }
    contrapose g
    simp at *
    have : (↑k:ℝ) ≤ -1 := by{exact Int.cast_le_neg_one_of_neg g}
    linarith
  }
  rw[goal] at hh
  simp at hh
  assumption
}

lemma arg_neg_pi_div_two{z : ℂ}(h: (↑z.arg : Real.Angle) = (↑(-Real.pi / 2) : Real.Angle)): z.arg = -(Real.pi / 2) := by{
  obtain ⟨k,kh⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 h
  have hh: z.arg = 2*Real.pi * k - Real.pi/2 := by{linarith}
  clear kh
  have goal: k = 0 := by{
    apply le_antisymm
    have tt: 2 * Real.pi * ↑k - Real.pi / 2 ≤ Real.pi := by{
      rw[← hh]
      exact Complex.arg_le_pi z
    }
    have tt: Real.pi*k ≤ Real.pi * (3/4) := by{linarith}
    have g : k ≤ (3/4 : ℝ) := by{exact le_of_mul_le_mul_left tt Real.pi_pos}
    contrapose g
    simp at *
    have : 1 ≤ (↑k:ℝ) := by{exact Int.cast_one_le_of_pos g}
    linarith

    have tt: -Real.pi ≤ 2 * Real.pi * ↑k - Real.pi / 2 := by{
      suffices : -Real.pi < 2 * Real.pi * ↑k - Real.pi / 2
      linarith

      rw[← hh]
      exact Complex.neg_pi_lt_arg z
    }
    have tt: Real.pi*(-1/4) ≤ Real.pi * k := by{linarith}
    have g : -1/4 ≤ (↑k : ℝ) := by{exact le_of_mul_le_mul_left tt Real.pi_pos}
    contrapose g
    simp at *
    have : (↑k:ℝ) ≤ -1 := by{exact Int.cast_le_neg_one_of_neg g}
    linarith
  }
  rw[goal] at hh
  simp at hh
  assumption
}

/-We prove several elementary but very important properties:-/

lemma angle_self(a b : Point): Angle a b a = 0 := by{
  by_cases ha : a = b
  rw[ha]
  simp

  have asub : a.x-b.x ≠ 0 := by{exact sub_neq_zero ha}
  unfold Angle
  field_simp
}

lemma angle_add{a b c d : Point}(ha : a ≠ b)(hc : c ≠ b)(hd : d ≠ b): Angle a b d = Angle a b c + Angle c b d := by{
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

lemma angle_symm(a b c): Angle c b a = -(Angle a b c) := by{
  by_cases ha: a = b
  rw[ha]
  simp
  by_cases hc: c = b
  rw[hc]
  simp
  have g: Angle a b a = Angle a b c + Angle c b a := by{exact angle_add ha hc ha}
  rw[angle_self a] at g
  have : Angle c b a = Angle c b a - 0 := by{simp}
  rw[this, g]
  simp
}

/-With this we can already prove the sum of angles in a triangle!-/

theorem anglesum_points{a b c : Point}(h : pairwise_different_point3 a b c): Angle a b c + Angle b c a + Angle c a b = Real.pi := by{
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

/-Or in other words:-/

lemma anglesum_points1{a b c : Point}(h : pairwise_different_point3 a b c): Angle a b c = Real.pi +-Angle b c a +-Angle c a b := by{
  rw[← anglesum_points h]
  repeat
    rw[add_assoc]
  simp
}

lemma anglesum_points2{a b c : Point}(h : pairwise_different_point3 a b c): Angle b c a = Real.pi +-Angle c a b +-Angle a b c := by{
  rw[← anglesum_points h]
  repeat
    rw[add_assoc]
  simp
}

lemma anglesum_points3{a b c : Point}(h : pairwise_different_point3 a b c): Angle c a b = Real.pi +-Angle a b c +-Angle b c a := by{
  rw[← anglesum_points h]
  repeat
    rw[add_assoc]
  nth_rw 2[add_comm]
  repeat
    rw[add_assoc]
  simp
}

/-Or in other words once more:-/
lemma anglesum_point1'{a b c : Point}(h : pairwise_different_point3 a b c): Real.pi +-Angle a b c = Angle b c a + Angle c a b := by{
  rw[anglesum_points1]
  simp
  have : ↑Real.pi + (Angle c a b + (Angle b c a + ↑Real.pi)) = ↑Real.pi + ↑Real.pi + Angle c a b + Angle b c a := by{
    simp
    repeat
      rw[← add_assoc]
    rw[add_comm]
    repeat
      rw[← add_assoc]
    simp
  }
  rw[this]
  simp
  rw[add_comm]
  assumption
}

lemma anglesum_point2'{a b c : Point}(h : pairwise_different_point3 a b c): Real.pi +-Angle b c a = Angle c a b + Angle a b c := by{
  rw[anglesum_points2]
  simp
  rw[add_comm]
  repeat
    rw[add_assoc]
  simp
  rw[add_comm]
  assumption
}

lemma anglesum_point3'{a b c : Point}(h : pairwise_different_point3 a b c): Real.pi +-Angle c a b = Angle a b c + Angle b c a := by{
  rw[anglesum_points3]
  simp
  rw[add_comm]
  repeat
    rw[add_assoc]
  simp
  rw[add_comm]
  assumption
}

def Angle_A : Triangle → Real.Angle :=
  fun T ↦ Angle T.c T.a T.b

def Angle_B : Triangle → Real.Angle :=
  fun T ↦ Angle T.a T.b T.c

def Angle_C : Triangle → Real.Angle :=
  fun T ↦ Angle T.b T.c T.a

theorem tri_sum_angle(T : Triangle): Angle_A T + Angle_B T + Angle_C T = Real.pi := by{
  have : pairwise_different_point3 T.a T.b T.c := by{exact (triangle_pairwise_different T)}
  unfold Angle_A Angle_B Angle_C
  have : pairwise_different_point3 T.c T.a T.b := by{
    apply pairwise_different_point3_perm12
    apply pairwise_different_point3_perm23
    assumption
  }
  rw[anglesum_points this]
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

theorem angle_in_between{a b c : Point}(h : in_between a c b)(ha: a ≠ b)(hc: c ≠ b): Angle a b c = Real.pi := by{
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
  have s2: (↑t : ℂ) ≠ 0 := by{
      contrapose ha
      simp at *
      rw[ht,ha]
      ext
      simp
    }
  have s3: (1-(↑t : ℂ)) ≠ 0 := by{
    contrapose hc
    simp at *
    rw[ht]
    ext
    simp
    have : (↑t:ℂ)=1 := by{
      calc
        (↑t : ℂ)= ↑t + 0 := by{ring}
          _= ↑t + (1-↑t) := by{rw[hc]}
          _= 1 := by{ring}
    }
    rw[this]
    ring
  }
  have : ↑t * (a.x - c.x) / (c.x - (a.x - ↑t * (a.x - c.x))) = -↑t /(1-↑t) := by{
    have : (c.x - (a.x - ↑t * (a.x - c.x))) = (c.x-a.x)*(1-t) := by{ring}
    rw[this]
    clear this
    have : (c.x - a.x) * (1 - ↑t) ≠ 0 := by{
      refine mul_ne_zero ?ha s3
      exact sub_neq_zero (id (Ne.symm l))
    }
    field_simp
    ring
  }
  rw[this] at h0
  clear this
  norm_cast at h0
  have : -t / (1-t)< 0 := by{
    apply div_neg_of_neg_of_pos
    contrapose s2
    norm_cast
    simp
    linarith

    contrapose s3
    norm_cast
    simp
    linarith
  }
  have : (↑(-t / (1 - t)):ℂ).arg = Real.pi := by{
    exact Complex.arg_ofReal_of_neg this
  }
  rw[h0] at this
  contrapose this
  show 0 ≠ Real.pi
  symm
  exact Real.pi_ne_zero


  --Second case!
  rw[h0] -- lol
}

theorem angle_not_in_between'{a b c : Point}(h : in_between b c a)(ha : a ≠ b)(hc : c ≠ b): Angle a b c = 0 := by{
  have col: colinear a c b := by{apply colinear_perm13; exact in_between_imp_colinear h}
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

  have col2: colinear b a c := by{
    have : (a.x - b.x) / (c.x - b.x) = (b.x-a.x)/(b.x-c.x) := by{
      field_simp
      ring
    }
    rw[this] at col
    exact (colinear_alt b a c).2 col
  }
  apply colinear_perm12 at col2
  by_cases l : a ≠ c
  have acsub: a.x - c.x ≠ 0 := by{exact sub_neq_zero l}
  apply colinear_perm12 at col2
  obtain p0|p0 := (colinear_alt2 b a c).1 col2
  · symm at p0
    contradiction
  obtain ⟨t,ht⟩ := p0
  have s1: a = go_along b c (t*(point_abs b c)) := by{
    rw[ht]
    unfold go_along padd point_abs dir point_abs p_scal_mul
    ext
    simp
    have : (↑(Complex.abs (b.x - c.x)):ℂ) ≠ 0 := by{
      norm_cast
      exact (AbsoluteValue.ne_zero_iff Complex.abs).mpr bcsub
    }
    field_simp
    ring
  }
  have t1: point_abs a b = abs t * point_abs b c := by{
    rw[point_abs_symm a b,s1, go_along_abs1,abs_mul]
    field_simp
    left
    exact point_abs_pos b c
    exact id (Ne.symm hc)
  }
  have t2 : point_abs c a = abs (1-t)*point_abs b c := by{
    rw[s1,go_along_abs2]
    have : point_abs b c - t*point_abs b c = (1-t)*(point_abs b c) := by{ring}
    rw[this,abs_mul]
    field_simp
    left
    exact point_abs_pos b c
    exact id (Ne.symm hc)
  }
  unfold in_between at h
  rw[point_abs_symm] at t1 t2
  rw[t1,t2] at h
  have : point_abs b c ≠ 0 := by{
    contrapose hc
    simp at *
    symm
    exact abs_zero_imp_same b c hc
  }
  have : |t| * point_abs b c + |1 - t| * point_abs b c = (abs t + abs (1-t))*point_abs b c := by{ring}
  rw[this] at h
  have s2: abs t + abs (1-t) = 1 := by{
    calc
      abs t + abs (1-t) = ((abs t + abs (1-t))*point_abs b c)/(point_abs b c) := by{field_simp}
        _= (point_abs b c)/(point_abs b c) := by{rw[h]}
        _=1 := by{field_simp}
  }

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
        abs t + abs (1-t) = ((abs t)*(point_abs b c) + abs (1-t)*(point_abs b c))/(point_abs b c) := by{field_simp;ring}
          _= (point_abs b c)/(point_abs b c) := by{
            clear this
            rw[← this] at h
            rw[h]
          }
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
  have tt0: t ≠ 0 := by{
    contrapose ha
    simp at *
    ext
    rw[ht,ha]
    simp
  }
  have tt1: t≠1 := by{
    contrapose l
    simp at *
    ext
    rw[ht,l]
    simp
  }
  rw[ht]
  simp at *
  have : -(↑t * (b.x - c.x)) / (c.x - b.x) = t := by{field_simp;ring}
  rw[this]
  have: 0 < t := by{
    contrapose tt0
    simp at *
    linarith
  }
  rw[Complex.arg_ofReal_of_nonneg h1]
  rfl

  simp at l
  rw[l]
  field_simp
}

/-Now we state last theorem in a slightly nicer version:-/

theorem angle_not_in_between{a b c : Point}(h: colinear a b c)(h' : ¬in_between a c b)(ha : a ≠ b)(hc : c ≠ b): Angle a b c = 0 := by{
  apply colinear_perm23 at h
  obtain h0|h0|h0 := colinear_imp_in_between2 a c b h
  · tauto
  · apply in_between_symm at h0
    exact angle_not_in_between' h0 ha hc
  rw[angle_symm, angle_not_in_between' h0 hc ha]
  simp
}


/-As a collorary we obtain the following two results:-/
lemma angle_in_between_out{a b c p : Point}(h: in_between a c b)(ha : a ≠ b)(hc : c ≠ b)(hp : p ≠ b): Angle c b p = Real.pi + Angle a b p := by{
  rw[angle_add hc ha hp]
  apply in_between_symm at h
  rw[angle_in_between h hc ha]
}

lemma angle_not_in_between_out{a b c p : Point}(h : colinear a b c)(h' : ¬in_between a c b)(ha : a ≠ b)(hc : c ≠ b)(hp : p ≠ b): Angle c b p = Angle a b p := by{
  rw[angle_add hc ha hp, angle_symm, angle_not_in_between h h' ha hc]
  simp
}

/-To save some time, here is a specific use case:-/
lemma angle_pmidpoint_right{a b p : Point}(ab : a ≠ b)(hb: b ≠ p): Angle (pmidpoint a b) b p = Angle a b p := by{
  exact angle_not_in_between_out (pmidpoint_colinear a b) (pmidpoint_not_in_between_right ab) ab (pmidpoint_diff_right ab) (Ne.symm hb)
}

lemma angle_pmidpoint_left{a b p : Point}(ab : a ≠ b)(ha: a ≠ p) : Angle (pmidpoint a b) a p = Angle b a p := by{
  exact angle_not_in_between_out (colinear_perm12 a b (pmidpoint a b) (pmidpoint_colinear a b)) (pmidpoint_not_in_between_left ab) (Ne.symm ab) (pmidpoint_diff_left ab) (Ne.symm ha)
}
--Angle (pmidpoint a b) b p = Angle a b p

/-If the shift points, the angle between them stay the same:-/

lemma angle_shift(a b c v : Point): Angle (padd a v) (padd b v) (padd c v) = Angle a b c := by{
  by_cases ah: a=b
  rw[ah]
  simp
  by_cases ch: c=b
  rw[ch]
  simp

  have ah': padd a v ≠ padd b v := by{
    contrapose ah
    unfold padd at ah
    simp at *
    ext
    assumption
  }
  have ch': padd c v ≠ padd b v := by{
    contrapose ch
    unfold padd at ch
    simp at *
    ext
    assumption
  }
  unfold Angle
  unfold padd
  simp
}

/-Similarly, scaling by a nonzero numbers leaves angles intact:-/

lemma angle_scal(a b c :Point)(v : ℂ)(hv : v ≠ 0): Angle (p_scal_mul v a) (p_scal_mul v b) (p_scal_mul v c) = Angle a b c := by{
  by_cases ah: a=b
  rw[ah]
  simp
  by_cases ch: c=b
  rw[ch]
  simp

  have ah': p_scal_mul v a ≠ p_scal_mul v b := by{
    contrapose ah
    unfold p_scal_mul at ah
    simp at *
    simp [*] at ah
    ext
    assumption
  }
  have ch': p_scal_mul v c ≠ p_scal_mul v b := by{
    contrapose ch
    unfold p_scal_mul at ch
    simp at *
    simp [*] at ch
    ext
    assumption
  }
  unfold Angle p_scal_mul
  simp
  apply same_arg_simp
  have s1: c.x-b.x ≠ 0 := by{exact sub_neq_zero ch}
  have s2: (v * c.x - v * b.x) ≠ 0 := by{
    have : (v * c.x - v * b.x) = v*(c.x-b.x) := by{ring}
    rw[this]
    by_contra p0
    simp at p0
    tauto
  }
  field_simp
  ring
}

lemma angle_scal'(a b c x : Point)(xh: x ≠ zero): Angle (pmul x a) (pmul x b) (pmul x c) = Angle a b c := by{
  by_cases ah: a=b
  rw[ah]
  simp
  by_cases ch: c=b
  rw[ch]
  simp

  let q := x.x
  have s1: pmul x a = p_scal_mul q a := by{unfold pmul p_scal_mul q;rfl}
  have s2: pmul x b = p_scal_mul q b := by{unfold pmul p_scal_mul q;rfl}
  have s3: pmul x c = p_scal_mul q c := by{unfold pmul p_scal_mul q;rfl}
  rw[s1,s2,s3]
  have : q ≠ 0 := by{
    contrapose xh
    unfold q at xh
    simp at *
    unfold zero
    ext
    rw[xh]
  }
  exact angle_scal a b c q this
}

/-Conjugating takes an angle to its negative, i.e. switches the arguments:-/

lemma angle_pconj(a b c : Point): Angle (pconj a) (pconj b) (pconj c) = Angle c b a := by{
  by_cases ah: a=b
  rw[ah]
  simp
  by_cases ch: c=b
  rw[ch]
  simp

  have ah': pconj a ≠ pconj b := by{
    contrapose ah
    simp at *
    rw[← pconj_twice a,ah, pconj_twice]
  }
  have ch': pconj c ≠ pconj b := by{
    contrapose ch
    simp at *
    rw[← pconj_twice c, ch, pconj_twice]
  }

  unfold Angle
  unfold pconj
  have : ((({ x := conj a.x } : Point).x - ({ x := conj b.x }:Point).x) / (({ x := conj c.x }:Point).x - ({ x := conj b.x }:Point).x)) = (conj a.x - conj b.x)/(conj c.x -conj b.x) := by{
    simp
  }
  rw[this]
  clear this
  have s1: (conj a.x - conj b.x) / (conj c.x - conj b.x) = conj ((a.x-b.x)/(c.x-b.x)) := by{
    unfold pconj at ch'
    simp at ch'
    have : conj c.x - conj b.x ≠ 0 := by{
      contrapose ch'
      simp at *
      calc
        conj c.x = conj c.x - 0 := by{ring}
          _= conj c.x - (conj c.x - conj b.x) := by{rw[ch']}
          _= conj b.x := by{ring}
    }
    field_simp
  }
  rw[s1]
  rw[arg_conj]
  by_cases h: ((a.x - b.x) / (c.x - b.x)).arg = Real.pi
  simp [*]
  have : Angle a b c = Real.pi := by {
    unfold Angle
    rw[h]
  }
  have : Angle c b a = -Real.pi := by{
    rw [← this]
    exact angle_symm a b c
  }
  unfold Angle at this
  rw[this]
  simp

  simp [h]
  have : - Angle a b c = Angle c b a := by{
    rw[angle_symm c b a]
    simp
  }
  unfold Angle at this
  assumption
}

/-A very important thing is that angles stay the same under reflection, we will use this
to show that isoceles triangles have the same angles:-/

theorem angle_reflection_point(a b c x : Point):  Angle (reflection_point_point a x) (reflection_point_point b x) (reflection_point_point c x) = Angle a b c := by{
  symm
  by_cases ah: a=b
  rw[ah]
  simp

  by_cases ch: c = b
  rw[ch]
  simp

  have ah': reflection_point_point a x ≠ reflection_point_point b x := by{
    contrapose ah
    simp at *
    rw[← reflection_point_point_twice a x, ah, reflection_point_point_twice]
  }
  have ch': reflection_point_point c x ≠ reflection_point_point b x := by{
    contrapose ch
    simp at *
    rw[← reflection_point_point_twice c x, ch, reflection_point_point_twice]
  }
  unfold Angle
  unfold reflection_point_point padd p_scal_mul pneg
  simp
  apply same_arg_simp
  have cbsub: c.x-b.x≠0 := by{exact sub_neq_zero ch}
  have cbsub': -c.x+b.x ≠ 0 := by{
    contrapose cbsub
    simp at *
    have : (0:ℂ)=-0 :=by{ring}
    rw[this,← cbsub]
    ring
  }
  field_simp
  ring
}

/-To show that angles are the same if we reflect them along aribitrary lines we use a trick as follows:
First we show angles are preserved under linear transformation, so the take point and a line to the real line, then the
reflection is just conjugating and turn back.
We will use this to show isoceles triangles have same angles at the base.-/

theorem linear_trans_angle(a b : Point)(ah: a ≠ zero)(u v w : Point): Angle (Linear_trans_point a b u) (Linear_trans_point a b v) (Linear_trans_point a b w) = Angle u v w := by{
  unfold Angle Linear_trans_point padd pmul
  simp
  have goal:((a.x * u.x - a.x * v.x) / (a.x * w.x - a.x * v.x)) = (u.x-v.x)/(w.x-v.x) := by{
    have a0: a.x ≠ 0 := by{exact fun a_1 ↦ id (Ne.symm ah) (congrArg Point.mk (id (Eq.symm a_1)))}
    by_cases wv: w=v
    rw[wv]
    simp

    have : w.x - v.x ≠ 0 := by{exact sub_neq_zero wv}
    have : a.x*w.x-a.x*v.x = a.x*(w.x-v.x) := by{ring}
    rw[this]
    have : a.x * (w.x-v.x) ≠ 0 := by{
      by_contra h0
      simp at h0
      tauto
    }
    field_simp
    ring
  }
  rw[goal]
}

/-We use linear transformations with the special case for the real line, which we have already proved:
(this is a bit tedious but satisfying in my opinion)-/

theorem angle_reflection_line(a b c : Point)(L : Line): Angle a b c = Angle (reflection_point_line c L) (reflection_point_line b L) (reflection_point_line a L) := by{
  by_cases ah: a=b
  rw[ah]
  simp
  by_cases ch: c=b
  rw[ch]
  simp

  symm
  calc
    Angle (reflection_point_line c L) (reflection_point_line b L) (reflection_point_line a L) = Angle (Linear_trans_point (lt_norm_line1 L) (lt_norm_line2 L) (reflection_point_line c L)) (Linear_trans_point (lt_norm_line1 L) (lt_norm_line2 L) (reflection_point_line b L)) (Linear_trans_point (lt_norm_line1 L) (lt_norm_line2 L) (reflection_point_line a L)) := by{
      rw[linear_trans_angle (lt_norm_line1 L) (lt_norm_line2 L) (lt_norm_line1_neq_zero L) (reflection_point_line c L) (reflection_point_line b L) (reflection_point_line a L)]
    }
      _= Angle (reflection_point_line (Linear_trans_point (lt_norm_line1 L) (lt_norm_line2 L) c) (Linear_trans_line (lt_norm_line1 L) (lt_norm_line2 L) L)) (reflection_point_line (Linear_trans_point (lt_norm_line1 L) (lt_norm_line2 L) b) (Linear_trans_line (lt_norm_line1 L) (lt_norm_line2 L) L)) (reflection_point_line (Linear_trans_point (lt_norm_line1 L) (lt_norm_line2 L) a) (Linear_trans_line (lt_norm_line1 L) (lt_norm_line2 L) L)) := by{
        repeat
          rw[linear_trans_reflection_point_line]
        repeat
          exact (lt_norm_line1_neq_zero L)
      }
      _= Angle (reflection_point_line (Linear_trans_point (lt_norm_line1 L) (lt_norm_line2 L) c) real_line) (reflection_point_line (Linear_trans_point (lt_norm_line1 L) (lt_norm_line2 L) b) real_line) (reflection_point_line (Linear_trans_point (lt_norm_line1 L) (lt_norm_line2 L) a) real_line) := by{
        repeat
          rw[lt_norm_line_real_line L]
      }
      _= Angle (pconj (Linear_trans_point (lt_norm_line1 L) (lt_norm_line2 L) c)) (pconj (Linear_trans_point (lt_norm_line1 L) (lt_norm_line2 L) b)) (pconj (Linear_trans_point (lt_norm_line1 L) (lt_norm_line2 L) a)) := by{
        repeat
          rw[reflection_point_line_real_line]
      }
      _= Angle (Linear_trans_point (lt_norm_line1 L) (lt_norm_line2 L) a) (Linear_trans_point (lt_norm_line1 L) (lt_norm_line2 L) b) (Linear_trans_point (lt_norm_line1 L) (lt_norm_line2 L) c) := by{
        rw[angle_pconj]
      }
      _= Angle (Linear_trans_point (lt_norm_line_inv1 L) (lt_norm_line_inv2 L) ((Linear_trans_point (lt_norm_line1 L) (lt_norm_line2 L) a))) (Linear_trans_point (lt_norm_line_inv1 L) (lt_norm_line_inv2 L) ((Linear_trans_point (lt_norm_line1 L) (lt_norm_line2 L) b))) (Linear_trans_point (lt_norm_line_inv1 L) (lt_norm_line_inv2 L) ((Linear_trans_point (lt_norm_line1 L) (lt_norm_line2 L) c))) := by{
        nth_rw 2[linear_trans_angle]
        exact lt_norm_line_inv1_neq_zero L
      }
      _= Angle a b c := by{
        repeat
          rw[lt_norm_line_inv_inv_point_left]
      }
}

/-With this we are now able to prove isocoloes triangle (i.e. triangles for which two sides have same length) have
same angles at their base.
First a (more general) point version:
-/
theorem same_abs_angle{a b p : Point}(h: point_abs p a = point_abs p b): Angle p a b = Angle a b p := by{
  by_cases ab: a=b
  rw[ab]
  simp

  rw[angle_reflection_line a b p (perp_bisector ab), reflection_point_line_perp_bisector ab,reflection_point_line_perp_bisector' ab,(reflection_point_line_on_line p (perp_bisector ab)).2 ((perp_bisector_def a b p ab).1 h)]
}
/-(note: the inverse of this will be proven at a later point)-/

/-Therefore in a circle we have same angles to the center:-/
lemma same_angles_circle_center{a b : Point}{C : CCircle}(ha: Lies_on_circle a C)(hb: Lies_on_circle b C): Angle (Center C) a b = Angle a b (Center C) := by{
  exact same_abs_angle (point_abs_lies_on_circle_same ha hb)
}


/-Now the triangle version: (once again the special point is at A for simplicity)-/

def Isosceles(T : Triangle): Prop :=
  abs_tri_ab T = abs_tri_ca T

theorem isosceles_angle{T : Triangle}(h: Isosceles T): Angle_B T = Angle_C T := by{
  unfold Angle_B Angle_C Isosceles abs_tri_ab abs_tri_ca at *
  rw[point_abs_symm T.c T.a] at h
  exact same_abs_angle h
}

/-In the next section we will prove Thales theorem. We have everything set up for this except a characterization
of perp points via angles:-/

lemma angle_perp_points(a b c : Point)(bh: b ≠ a)(ch: c ≠ a): perp_points a b a c ↔ Angle b a c = Real.pi / (2:ℝ) ∨ Angle b a c = - Real.pi / (2:ℝ) := by{
  have s1: ((b.x-a.x)/(c.x-a.x)) = ((a.x-b.x)/(a.x-c.x)) := by{
    by_cases ac: a=c
    rw[ac]
    simp

    have : c.x-a.x ≠ 0 := by{exact sub_neq_zero fun a_1 ↦ ac (id (Eq.symm a_1))}
    have : a.x - c.x ≠ 0 := by{exact sub_neq_zero ac}
    field_simp
    ring
  }
  unfold Angle perp_points
  rw[← s1]
  clear s1
  constructor
  intro h
  have s2: ((b.x-a.x)/(c.x-a.x)).im ≠ 0 := by{
    by_contra p0
    have : (b.x-a.x)/(c.x-a.x) = 0 := by{
      exact Eq.symm (Complex.ext (id (Eq.symm h)) (id (Eq.symm p0)))
    }
    field_simp at this
    have : b.x -a.x ≠ 0 := by{exact sub_neq_zero bh}
    have : c.x - a.x ≠ 0 := by{exact sub_neq_zero ch}
    tauto
  }
  by_cases h0: ((b.x - a.x) / (c.x - a.x)).im < 0
  right
  rw[(Complex.arg_eq_neg_pi_div_two_iff).2 ⟨h, h0⟩]
  ring_nf

  left
  have g: 0 < ((b.x - a.x) / (c.x - a.x)).im := by{
    contrapose s2
    simp at *
    linarith
  }
  rw[(Complex.arg_eq_pi_div_two_iff).2 ⟨h, g⟩]

  intro h
  obtain h|h := h
  suffices:  ((b.x - a.x) / (c.x - a.x)).re = 0 ∧  0 < ((b.x - a.x) / (c.x - a.x)).im
  tauto
  have goal : ((b.x - a.x) / (c.x - a.x)).arg = (Real.pi / 2) := by{
    exact arg_pi_div_two h
  }
  exact Complex.arg_eq_pi_div_two_iff.mp goal

  suffices:  ((b.x - a.x) / (c.x - a.x)).re = 0 ∧  ((b.x - a.x) / (c.x - a.x)).im < 0
  tauto
  have goal : ((b.x - a.x) / (c.x - a.x)).arg = -(Real.pi / 2) := by{
    exact arg_neg_pi_div_two h
  }
  exact Complex.arg_eq_neg_pi_div_two_iff.mp goal
}

/-this is pretty much all (or at least most of) the "basic" stuff about angles.
Later, more properties will be shown.-/
