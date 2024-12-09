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
