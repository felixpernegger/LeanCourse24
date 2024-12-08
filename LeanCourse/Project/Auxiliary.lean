import LeanCourse.Project.Circles
import Mathlib

open Function Set Classical

noncomputable section

/-In this rather auxiliary sections we introduce what it means to be "inside a circle/triangle", etc.
Some of this may seem pointless but it is indeed important:
For example, the incircle is unqiue only in the sense that it lies inside of the triangle,
otherwise there would be *4* incircles.-/

/-We also introduce reflexion along stuff.-/

/- we want to introduce the notion of a point being on the same side
as another of a line.
We say two points lie on the same side of a line iff the segment between them
does interesect the line:-/

def same_side(L : Line)(a b : Point): Prop :=
  ∀(t : ℝ), (0 ≤ t)∧(t ≤ 1) → ¬Lies_on (padd (p_scal_mul t a) (p_scal_mul (1-t) b)) L

/-For this two make sense, a and b cannot lie on L. If this is
the case, we have an equivalence relation (we techincally only need it for reflexivity):-/

lemma same_side_refl{L : Line}{a : Point}(ha: ¬Lies_on a L): same_side L a a := by{
  unfold same_side
  intro t ⟨ht0, ht1⟩
  unfold padd p_scal_mul
  simp at *
  have : ({ x := ↑t * a.x + (1 - ↑t) * a.x } : Point)= a := by{
    ext
    simp
    ring
  }
  rw[this]
  assumption
}

lemma same_side_symm{L : Line}{a b : Point}(h : same_side L a b): same_side L b a := by{
  unfold same_side at *
  intro t ht1
  have : 0 ≤ 1-t ∧ 1-t ≤ 1 := by{
    constructor
    linarith
    linarith
  }
  specialize h (1-t) this
  simp at h
  rwa[padd_comm (p_scal_mul (↑t) b) (p_scal_mul (1 - ↑t) a)]
}

lemma same_side_trans{L : Line}{a b c : Point}(ab : same_side L a b)(bc : same_side L b c): same_side L a c := by{
  unfold same_side
  by_contra h
  simp at h
  obtain ⟨t,ht1,ht2,r⟩ := h
  sorry -- note this is equivalent to this triangle axiom thing, therefore quite complicated
}

/-If a doesnt lie on the same side as b and c, b and c lie on the same side:
For this a cannot lie on the line.-/
lemma not_same_side_not_same_side{L : Line}{a b c : Point}(ha: ¬Lies_on a L)(ab : ¬same_side L a b)(ac: ¬ same_side L a c): same_side L b c := by{
  have abh: a ≠ b := by{
    contrapose ab
    simp at *
    rw[← ab]
    exact same_side_refl ha
  }
  have ach: a ≠ c := by{
    contrapose ac
    simp at *
    rw[← ac]
    exact same_side_refl ha
  }
  unfold same_side at *
  simp at *
  obtain ⟨x,xh0,xh1,xh⟩ := ab
  obtain ⟨y,yh0,yh1,yh⟩ := ac
  by_cases h0: (padd (p_scal_mul (↑x) a) (p_scal_mul (1 - ↑x) b)) = (padd (p_scal_mul (↑y) a) (p_scal_mul (1 - ↑y) c))
  have abcol: colinear a b (padd (p_scal_mul (↑x) a) (p_scal_mul (1 - ↑x) b)) := by{
    unfold padd p_scal_mul colinear det conj
    simp
    ring
  }
  have accol: colinear a c (padd (p_scal_mul (↑x) a) (p_scal_mul (1 - ↑x) b)) := by{
    rw[h0]
    unfold padd p_scal_mul colinear det conj
    simp
    ring
  }
  apply colinear_perm13 at abcol
  apply colinear_perm13 at accol
  apply colinear_perm23 at abcol
  apply colinear_perm23 at accol
  have tt: (padd (p_scal_mul (↑x) a) (p_scal_mul (1 - ↑x) b)) ≠ a := by{
    contrapose ha
    simp at *
    rwa[← ha]
  }
  have col: colinear a b c := by{
    exact colinear_trans (padd (p_scal_mul (↑x) a) (p_scal_mul (1 - ↑x) b)) a b c abcol accol tt
  }
}
