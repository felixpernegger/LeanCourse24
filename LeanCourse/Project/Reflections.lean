import LeanCourse.Project.Auxiliary
import Mathlib

open Function Set Classical

noncomputable section


/- In this rather short section, we introduce reflections along points and lines.
Nothing too spectacular, but never the less good to have.-/

/-Notation: reflection_object1_object2 mean we reflect object2 along object1.
We do all cases except object1 being a circle:
The respective reflection would be inversion, but that would be too much and hard too define for now-/

def reflection_point_point: Point → Point → Point :=
  fun a b ↦ padd (p_scal_mul 2 b) (pneg a)
--so just 2*b-a

/-This does nothing too surprising:-/
@[simp] lemma reflection_point_point_self (a : Point): reflection_point_point a a = a := by{
  unfold reflection_point_point padd p_scal_mul pneg
  ext
  simp
  ring
}

lemma reflection_point_point_same_imp_same {a b : Point}(h : a = reflection_point_point a b): a = b := by{
  obtain ⟨a1,a2⟩ := a
  obtain ⟨b1,b2⟩ := b
  unfold reflection_point_point padd pneg p_scal_mul at h
  simp at *
  have s1:  ({ re := a1, im := a2 }:ℂ).re = (2 * { re := b1, im := b2 } + -({ re := a1, im := a2 } : ℂ)).re := by{
    nth_rw 1[h]
  }
  simp at s1
  have s2:  ({ re := a1, im := a2 }:ℂ).im = (2 * { re := b1, im := b2 } + -({ re := a1, im := a2 } : ℂ)).im := by{
    nth_rw 1[h]
  }
  simp at s2
  constructor
  linarith
  linarith
}

/-the reflection is colinear:-/

lemma reflection_point_point_colinear (a b : Point): colinear a (reflection_point_point a b) b := by{
  unfold reflection_point_point padd pneg p_scal_mul
  unfold colinear det conj
  simp
  ring
}

/-reflecting 3 colinear points stays colinear:-/
lemma reflection_point_point_colinear2 (p : Point){a b c : Point}(h : colinear a b c): colinear (reflection_point_point a p) (reflection_point_point b p) (reflection_point_point c p) := by{
  obtain ⟨a1,a2⟩ := a
  obtain ⟨b1,b2⟩ := b
  obtain ⟨c1,c2⟩ := c
  obtain ⟨p1,p2⟩ := p
  unfold colinear det conj reflection_point_point padd pneg p_scal_mul at *
  simp at *
  ring_nf
  rw[← h]
  ring
}

@[simp] lemma reflection_point_point_twice (a b : Point) : reflection_point_point (reflection_point_point a b) b  = a := by{
  ext
  unfold reflection_point_point padd pneg p_scal_mul
  simp
}

/-Reflecting a point along a line is the same as reflection along the foot-/

def reflection_point_line: Point → Line → Point :=
  fun a L ↦ reflection_point_point a (foot a L)

/-Reflection is the same iff it lies on the line:-/

theorem reflection_point_line_on_line (a : Point)(L : Line): reflection_point_line a L = a ↔ Lies_on a L := by{
  constructor
  intro h
  unfold reflection_point_line at h
  have : foot a L = a := by{exact Eq.symm (reflection_point_point_same_imp_same (id (Eq.symm h)))}
  rw[← this]
  exact foot_on_line L a

  intro h
  have : foot a L = a := by{exact foot_point_on_line h}
  unfold reflection_point_line
  rw[this]
  exact reflection_point_point_self a
}

@[simp] lemma reflection_point_line_foot (a : Point)(L : Line): foot (reflection_point_line a L) L = foot a L := by{
  have t: ¬Parallel L (perp_through L a) := by{exact perp_through_not_parallel L a}
  have fi: foot a L = Intersection t := by{
    apply intersection_unique
    constructor
    exact foot_on_line L a
    exact foot_on_perp L a
  }
  rw[fi]
  apply intersection_unique
  constructor
  exact foot_on_line L (reflection_point_line a L)

  have goal: perp_through L (reflection_point_line a L) = perp_through L a := by{
    symm
    apply perp_through_unique
    constructor
    exact perp_through_is_perp L a
    by_cases h0: Lies_on a L
    have : reflection_point_line a L = a := by{exact (reflection_point_line_on_line a L).mpr h0}
    rw[this]
    exact point_lies_on_perp_through L a
    have tt: foot a L ≠ a := by{exact foot_point_not_on_line h0}
    have : perp_through L a = Line_through tt := by{exact Eq.symm (foot_line_through h0)}
    rw[this]
    unfold Lies_on Line_through
    simp
    unfold reflection_point_line
    apply colinear_perm12
    apply colinear_perm23
    exact reflection_point_point_colinear a (foot a L)
  }
  rw[← goal]
  exact foot_on_perp L (reflection_point_line a L)
}

@[simp] lemma reflection_point_line_twice (a : Point)(L : Line) : reflection_point_line (reflection_point_line a L) L = a := by{
  unfold reflection_point_line
  have : foot (reflection_point_line a L) L = foot a L := by{exact reflection_point_line_foot a L}
  unfold reflection_point_line at this
  rw[this]
  exact reflection_point_point_twice a (foot a L)
}

/-Now lets define the reflection_line_point-/

def reflection_line_point : Line → Point → Line :=
  fun L a ↦ ⟨{p : Point | ∃ (s : Point), Lies_on s L ∧ p = reflection_point_point s a}, by{
    obtain ⟨S,u,v,uv,hS⟩ := L
    use reflection_point_point u a
    use reflection_point_point v a

    constructor
    contrapose uv
    simp at *
    rw[← reflection_point_point_twice u a, ← reflection_point_point_twice v a, uv]

    ext r
    simp
    constructor
    intro h
    obtain ⟨s,hs1,hs2⟩ := h
    rw[hs2]
    apply reflection_point_point_colinear2
    unfold Lies_on at hs1
    simp at hs1
    rw[hS] at hs1
    simp at hs1
    assumption

    intro h
    use reflection_point_point r a
    constructor
    unfold Lies_on
    simp
    rw[hS]
    simp
    rw[← reflection_point_point_twice u a, ← reflection_point_point_twice v a]
    apply reflection_point_point_colinear2
    assumption

    simp
  }⟩

  /-same properties as usual:-/

lemma reflection_line_point_twice (L : Line)(a : Point): reflection_line_point (reflection_line_point L a) a = L := by{
  sorry
}
