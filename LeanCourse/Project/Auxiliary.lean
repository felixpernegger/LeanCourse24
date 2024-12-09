import LeanCourse.Project.Perpendiculars
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
  intro t ht hht
  by_contra p0
  have coll: colinear b c (padd (p_scal_mul (↑t) b) (p_scal_mul (1 - ↑t) c)) := by{
    unfold padd p_scal_mul colinear det conj
    simp
    ring
  }

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
    sorry
  }
  have gg: (padd (p_scal_mul (↑t) b) (p_scal_mul (1 - ↑t) c)) = padd (p_scal_mul (↑x) a) (p_scal_mul (1 - ↑x) b) := by{
    by_contra p1
    sorry--this cannot be because of in between stuff but its annoying
  }
  sorry

  have hL: L = Line_through h0 := by{
    apply line_through_unique
    constructor
    assumption
    assumption
  }
  sorry
}
--actually make this prove a lot nicer please, this is horrible.
--maybe give following characterization:
--b c not on the same side, is the same as that in_between b c (Intersection L (Line_through bc))

/-With this we get a relatively nice notion for the inside of the Triangle:-/

/-Same side of ab as c, etc.-/

def inside_triangle (T : Triangle)(p : Point): Prop :=
  same_side (tri_ab T) T.c p ∧ same_side (tri_bc T) T.a p ∧ same_side (tri_ca T) T.b p


/-The inside of a circle is shorter to define:-/
def inside_circle(a : Point)(C : CCircle) : Prop :=
  point_abs a (Center C) < Radius C