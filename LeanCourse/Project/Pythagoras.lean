import LeanCourse.Project.Perpendiculars
import Mathlib

open Function Set Classical

noncomputable section

/-In this section we introduce right angled triangles and prove the pythagorean theorem.-/

/-For simplicity RIGHT TRIANGLES HAVE THE RIGHT ANGLE IN A-/

def RightTriangle(T : Triangle): Prop :=
  Perpendicular (tri_ab T) (tri_ca T)

lemma righttriangle_perp_points{T : Triangle}(h: RightTriangle T): perp_points T.a T.b T.a T.c := by{
  unfold RightTriangle at h
  apply perp_all h
  exact tri_a_on_ab T
  exact tri_b_on_ab T
  exact tri_a_on_ca T
  exact tri_c_on_ca T
}

/-I am a bit lazy and prove pythogoras by calculation.
This is of the main reasons complex numbers are so useful in planar geometry.-/

theorem pythagoras_points{a b c : Point}(h : perp_points a b a c): (point_abs b c)^2  = (point_abs a b)^2 + (point_abs c a)^2 := by{
  rw[point_abs_symm c a]
  unfold perp_points at h
  by_cases ac: a = c
  · rw[ac]
    rw[point_abs_self c, point_abs_symm b c]
    ring

  obtain ⟨a1,a2⟩ := a
  obtain ⟨b1,b2⟩ := b
  obtain ⟨c1,c2⟩ := c
  unfold point_abs Complex.abs
  simp at *
  obtain h|h := h
  swap
  exfalso
  by_cases h0: a1 = c1
  rw[h0] at h
  simp at h
  have : a2 = c2 := by{linarith}
  tauto

  have : a1 - c1 ≠ 0 := by {
    contrapose h0
    simp at *
    linarith
  }
  have : 0 < (a1 - c1) ^ 2 + (a2 - c2) ^ 2 := by{
    calc
      0 < (a1-c1)^2 := by{exact pow_two_pos_of_ne_zero this}
        _= (a1-c1)^2 + 0 := by{ring}
        _≤ (a1-c1)^2 + (a2-c2)^2 := by{apply add_le_add;rfl;exact sq_nonneg (a2 - c2)}
  }
  rw[h] at this
  linarith




  have slemma{x y : ℝ}: (√ (x*x + y*y))^2 = x*x + y*y := by{
    refine Real.sq_sqrt ?h
    rw[← add_zero 0]
    apply add_le_add
    exact mul_self_nonneg x
    exact mul_self_nonneg y
  }
  rw[slemma,slemma,slemma]
  clear slemma
  by_cases a1c1: a1 = c1
  rw[a1c1] at h
  rw[a1c1]
  simp [*] at *
  obtain h|h := h
  rw[h]
  have a2b2: a2 = b2 := by{linarith}
  rw[a2b2]
  simp
  ring

  have a2c2: a2=c2 := by{linarith}
  rw[a2c2]
  simp
  ring

  clear ac
  have a1c1sub: a1-c1 ≠ 0 := by{
    contrapose a1c1
    simp at *
    linarith
  }
  have b1cool: b1 = a1 + (((a2-b2)*(a2-c2))/(a1-c1)) := by{
    field_simp
    linarith
  }
  rw[b1cool]
  field_simp
  ring
}

/-Now for right triangles:-/

theorem pythagoras {T : Triangle}(h : RightTriangle T): (abs_tri_bc T)^2 = (abs_tri_ab T)^2 + (abs_tri_ca T)^2 := by{
  unfold abs_tri_ab abs_tri_ca abs_tri_bc
  apply pythagoras_points
  exact righttriangle_perp_points h
}

/-pythagorean theorem will be *very* useful. In particular, in the next file we will prove the existance
of a circumcircle purely geomtrically using it.
First though, as promised in the file "Triangles", we prove that "in_between" implies colinear-/

--Maybe actually remove this bruh
lemma foot_abs_less{a p : Point}{L : Line}(ha: Lies_on a L)(hp: ¬Lies_on p L): point_abs a (foot p L) < point_abs a p := by{
  suffices : (point_abs a (foot p L))^2 < (point_abs a p)^2
  contrapose this
  simp at *
  have tt: 0 ≤ point_abs a p := by{exact point_abs_pos a p}
  nlinarith

  have goal: perp_points (foot p L) a (foot p L) p :=by{
    have pl: Perpendicular L (perp_through L p) := by{
      exact perp_through_is_perp L p
    }
    apply perp_all pl
    exact foot_on_line L p
    exact ha
    exact foot_on_perp L p
    exact point_lies_on_perp_through L p
  }
  rw[pythagoras_points goal]
  rw[point_abs_symm]
  simp
  have : point_abs p (foot p L) ≠ 0 := by{
    by_contra h0
    have : p = foot p L := by{
      exact abs_zero_imp_same p (foot p L) h0
    }
    have : p ≠ foot p L := by{
      exact Ne.symm (foot_point_not_on_line hp)
    }
    contradiction
  }
  exact pow_two_pos_of_ne_zero this
}

/-So as proven before point_line_abs is the infimum of distances, or in language not too make it too complicated:-/

lemma point_line_abs_leq_point_abs(p a : Point){L : Line}(h : Lies_on a L): point_line_abs p L ≤ point_abs p a := by{
  by_cases ha: a = foot p L
  rw[ha]
  unfold point_line_abs
  rfl

  unfold point_line_abs
  by_cases hp: Lies_on p L
  have : p = foot p L := by{exact Eq.symm (foot_point_on_line hp)}
  nth_rw 1[this]
  rw[point_abs_self (foot p L)]
  exact point_abs_pos p a

  suffices : point_abs p (foot p L) < point_abs p a
  · linarith
  have goal: perp_points (foot p L) a (foot p L) p :=by{
    have pl: Perpendicular L (perp_through L p) := by{
      exact perp_through_is_perp L p
    }
    apply perp_all pl
    exact foot_on_line L p
    exact h
    exact foot_on_perp L p
    exact point_lies_on_perp_through L p
  }
  suffices : (point_abs p (foot p L))^2 < (point_abs p a)^2
  contrapose this
  simp at *
  have tt: 0 ≤ point_abs p a := by{exact point_abs_pos p a}
  nlinarith
  rw[point_abs_symm p a, pythagoras_points goal]
  simp
  have : point_abs (foot p L) a ≠ 0 := by{
    contrapose ha
    simp at *
    symm
    exact abs_zero_imp_same (foot p L) a ha
  }
  exact pow_two_pos_of_ne_zero this
}

lemma point_line_abs_eq_point_abs_iff(p a : Point)(L : Line)(ah : Lies_on a L) : point_abs p a = point_line_abs p L ↔ a = foot p L := by{
  constructor
  intro h
  contrapose h
  simp at *
  unfold point_line_abs
  suffices : (point_abs p a)^2 ≠ (point_abs p (foot p L))^2
  contrapose this
  simp at *
  rw[this]
  have goal: perp_points (foot p L) a (foot p L) p :=by{
    have pl: Perpendicular L (perp_through L p) := by{
      exact perp_through_is_perp L p
    }
    apply perp_all pl
    exact foot_on_line L p
    exact ah
    exact foot_on_perp L p
    exact point_lies_on_perp_through L p
  }
  rw[point_abs_symm p a, pythagoras_points goal]
  simp
  contrapose h
  simp at *
  symm
  exact abs_zero_imp_same (foot p L) a h

  intro h
  unfold point_line_abs
  rw[h]
}

/-for practical purposes the following lemma is useful in that sense:-/
lemma sqrt_sum_eq_og{x y : ℝ}(h: √(x^2+y^2)≤y): x = 0 := by{
  have hy : 0 ≤ y := by{
    calc
      0 ≤ √(x ^ 2 + y ^ 2) := by{exact Real.sqrt_nonneg (x ^ 2 + y ^ 2)}
        _≤ y := by{assumption}
  }
  have hxy: 0 ≤ x^2+y^2 := by{nlinarith}
  suffices : x^2 + y^2 ≤ y^2
  · nlinarith
  calc
    x^2+y^2 = √(x^2+y^2) * √(x^2+y^2) := by{simp [*]}
      _≤ y*y := by{apply mul_le_mul; assumption; assumption; exact Real.sqrt_nonneg (x ^ 2 + y ^ 2); assumption}
      _= y^2 := by{ring}
}

/-Another use case is the promised reversion of colinear_imp_in_between-/

lemma in_between_imp_colinear{a b x : Point}(h : in_between a b x): colinear a b x := by{
  by_cases ab : a = b
  · apply colinear_self
    tauto

  suffices : (Lies_on x (Line_through ab))
  unfold Lies_on Line_through at this
  simp at this
  assumption

  by_contra p0
  have fx: foot x (Line_through ab) ≠ x := by{
    by_contra h0
    have : foot x (Line_through ab) ≠ x := by{exact foot_point_not_on_line p0}
    contradiction
  }
  unfold in_between at h
  have : point_abs a b < point_abs a x + point_abs x b := by{
    calc
      point_abs a b ≤ point_abs a (foot x (Line_through ab)) + point_abs (foot x (Line_through ab)) b := by{exact point_abs_triangle a (foot x (Line_through ab)) b}
        _< point_abs a x + point_abs x b := by{
          apply add_lt_add
          apply foot_abs_less
          exact line_through_mem_left ab
          assumption

          rw[point_abs_symm, point_abs_symm x b]
          apply foot_abs_less
          exact line_through_mem_right ab
          assumption
        }
  }
  rw[h] at this
  linarith
}

/-This also gives us a way to relative quickly show something is the midpoint:-/
lemma pmidpoint_simp {a b p : Point}(ah: point_abs p a = 1/2 * point_abs a b)(bh: point_abs p b = 1/2 * point_abs a b): p = pmidpoint a b := by{
  by_cases ab : a = b
  · rw[ab, point_abs_self] at ah
    simp at ah
    have : p = b := by{exact abs_zero_imp_same p b ah}
    rw[ab,this]
    symm
    exact pmidpoint_self b
  have s1: colinear a b p := by{
    apply in_between_imp_colinear
    unfold in_between
    rw[point_abs_symm a p, ah, bh]
    ring
  }
  apply colinear_perm23 at s1
  apply (colinear_alt2 a p b).1 at s1
  simp [*] at s1

  obtain ⟨t,th⟩ := s1
  have ph: p = go_along a b (t * point_abs a b) := by{
    rw[th]
    unfold go_along dir padd p_scal_mul
    simp
    have : point_abs a b ≠ 0 := by{
      contrapose ab
      simp at *
      exact abs_zero_imp_same a b ab
    }
    have : (↑(point_abs a b) : ℂ) ≠ 0 := by{
      contrapose this
      simp at *
      assumption
    }
    field_simp
    ring
  }
  rw[point_abs_symm p a, ph, go_along_abs1 ab (t*(point_abs a b))] at ah
  have t1: abs t = 1 / 2 := by{
    have u1: 0 < point_abs a b := by{exact point_abs_neq ab}
    have u2: 0 ≤ point_abs a b := by{linarith}
    have t3: |t * point_abs a b| = abs t * point_abs a b := by{
      calc
        abs (t* point_abs a b) = abs t * abs (point_abs a b) := by{exact abs_mul t (point_abs a b)}
          _= abs t * point_abs a b := by{rw[abs_of_nonneg u2]}
    }
    rw[t3] at ah
    field_simp at ah
    have : abs t = 1/2 * (1/(point_abs a b)) *(abs t * point_abs a b * 2) := by{
      field_simp
      ring
    }
    rw[this,ah]
    field_simp
    ring
  }
  rw[point_abs_symm p b, ph, go_along_abs2] at bh
  have t4: abs (1-t) = 1 /2 := by{
    have :  |point_abs a b - t * point_abs a b| = abs (1-t) * point_abs a b := by{
      calc
        |point_abs a b - t * point_abs a b| = abs ((1-t)*(point_abs a b)) := by{ring_nf}
          _= abs (1-t) * abs (point_abs a b) := by{exact abs_mul (1-t) (point_abs a b)}
          _= abs (1-t) * point_abs  a b := by{rw[abs_of_nonneg (point_abs_pos a b)]}
    }
    rw[bh] at this
    have e: 0 < point_abs a b := by{exact point_abs_neq ab}
    calc
      (abs (1-t)) = (1/(point_abs a b)) * (abs (1-t) * point_abs a b) := by{field_simp}
        _= 1/(point_abs a b) * (1/2 * point_abs a b) := by{rw[this]}
        _= 1 / 2 := by{field_simp}
  }
  apply eq_or_eq_neg_of_abs_eq at t1
  apply eq_or_eq_neg_of_abs_eq at t4
  obtain t1|t1 := t1
  swap
  rw[t1] at t4
  simp at t4
  contrapose t4
  norm_num

  rw[t1] at th
  rw[th]
  ext
  unfold pmidpoint
  simp
  ring
  assumption
}

/-To simplify usage, we finish off with a few specifications for pythagoras:-/

lemma pythagoras_points_bc {a b c : Point}(h : perp_points a b a c): (point_abs b c)  = √((point_abs a b)^2 + (point_abs c a)^2) := by{
  rw[← pythagoras_points h]
  have : 0 ≤ point_abs b c := by{exact point_abs_pos b c}
  simp [*]
}

lemma pythagoras_points_ab {a b c : Point}(h : perp_points a b a c): (point_abs a b)  = √((point_abs b c)^2 - (point_abs c a)^2) := by{
  rw[pythagoras_points h]
  simp
  have : 0 ≤ point_abs a b := by{exact point_abs_pos a b}
  simp [*]
}

lemma pythagoras_points_ca {a b c : Point}(h : perp_points a b a c): (point_abs c a)  = √((point_abs b c)^2 - (point_abs a b)^2) := by{
  rw[pythagoras_points h]
  simp
  have : 0 ≤ point_abs c a := by{exact point_abs_pos c a}
  simp [*]
}

lemma pythagoras_bc {T : Triangle}(h: RightTriangle T): (abs_tri_bc T) = √((abs_tri_ab T)^2 + (abs_tri_ca T)^2) := by{
  rw[← pythagoras h]
  have : 0 ≤ abs_tri_bc T := by{unfold abs_tri_bc; exact point_abs_pos T.b T.c}
  simp [*]
}

lemma pythagoras_ab {T : Triangle}(h: RightTriangle T): (abs_tri_ab T) = √((abs_tri_bc T)^2 - (abs_tri_ca T)^2) := by{
  rw[pythagoras h]
  have : 0 ≤ abs_tri_ab T := by{unfold abs_tri_ab; exact point_abs_pos T.a T.b}
  simp [*]
}

lemma pythagoras_ca {T : Triangle}(h: RightTriangle T): (abs_tri_ca T) = √((abs_tri_bc T)^2 - (abs_tri_ab T)^2) := by{
  rw[pythagoras h]
  have : 0 ≤ abs_tri_ca T := by{unfold abs_tri_ca; exact point_abs_pos T.c T.a}
  simp [*]
}

/-Some stuff also of interest using pythagoras:-/

/- Read this as: "in perp triangles, the foots are just the corner"-/
lemma foot_if_perp_points{p a b : Point}(ab : a ≠ b)(h: perp_points a p a b): foot p (Line_through ab) = a := by{
  by_cases ap: a = p
  · rw[← ap]
    exact foot_point_on_line (line_through_mem_left ab)
  have u: Parallel (perp_through (Line_through ab) p) (perp_through (Line_through ab) a) := by{
    apply perp_perp (Line_through ab)
    exact perp_through_is_perp (Line_through ab) p
    exact perp_through_is_perp (Line_through ab) a
  }
  apply abs_zero_imp_same
  have r: perp_points a (foot p (Line_through ab)) a p:= by{
    exact perp_all (perp_symm ((perp_quot ap ab).2 h)) (line_through_mem_left ab) (foot_on_line (Line_through ab) p) (line_through_mem_left ap) (line_through_mem_right ap)
  }
  have le: √(point_abs a (foot p (Line_through ab)) ^ 2 + point_abs p a ^ 2) ≤ point_abs p a := by{
    rw[← pythagoras_points_bc r]
    have : point_line_abs p (Line_through ab) ≤ point_abs p a := by{exact point_line_abs_leq_point_abs p a (line_through_mem_left ab)}
    unfold point_line_abs at this
    rwa[point_abs_symm]
  }
  rw[point_abs_symm]
  exact sqrt_sum_eq_og le
}
