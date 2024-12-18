import LeanCourse.Project.Circumcircle
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

lemma reflection_point_point_pmidpoint(a b : Point): pmidpoint (reflection_point_point a b) a = b := by{
  unfold pmidpoint reflection_point_point padd pneg p_scal_mul
  ext
  simp
}

lemma reflection_point_point_same_imp_same {a b : Point}(h : a = reflection_point_point a b): a = b := by{
  obtain ⟨a1,a2⟩ := a
  obtain ⟨b1,b2⟩ := b
  unfold reflection_point_point padd pneg p_scal_mul at h
  simp at *
  have s1:  ({ re := a1, im := a2 }:ℂ).re = (2 * { re := b1, im := b2 } + -({ re := a1, im := a2 } : ℂ)).re := by{
    nth_rw 1[h]
    rfl
  }
  simp at s1
  have s2:  ({ re := a1, im := a2 }:ℂ).im = (2 * { re := b1, im := b2 } + -({ re := a1, im := a2 } : ℂ)).im := by{
    nth_rw 1[h]
    rfl
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

lemma reflection_point_abs(a b : Point) : point_abs (reflection_point_point a b) b = point_abs a b := by{
  unfold reflection_point_point padd pneg p_scal_mul point_abs
  simp
  ring_nf
  obtain ⟨a1,a2⟩ := a
  obtain ⟨b1,b2⟩ := b
  simp
  unfold Complex.abs Complex.normSq
  simp
  ring_nf
}

lemma reflection_point_abs2(a b : Point) : point_abs (reflection_point_point a b) a = 2*(point_abs a b) := by{
  unfold reflection_point_point padd p_scal_mul pneg point_abs Complex.abs Complex.normSq
  simp
  ring_nf
  have : (-(b.x.re * a.x.re * 8) + b.x.re ^ 2 * 4 + (a.x.re ^ 2 * 4 - b.x.im * a.x.im * 8) + b.x.im ^ 2 * 4 + a.x.im ^ 2 * 4) = 4*(-(b.x.re * a.x.re * 2) + b.x.re ^ 2 + (a.x.re ^ 2 - b.x.im * a.x.im * 2) + b.x.im ^ 2 + a.x.im ^ 2) := by{ring}
  rw[this]
  simp
  have : √4 = 2 := by{
    refine Real.sqrt_eq_cases.mpr ?_
    left
    ring_nf
    simp
  }
  rw[this]
  ring
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

lemma reflection_point_line_pmidpoint(a : Point)(L : Line): pmidpoint (reflection_point_line a L) a = foot a L := by{
  unfold reflection_point_line
  exact reflection_point_point_pmidpoint a (foot a L)
}

lemma reflection_point_line_abs(a : Point)(L : Line): point_line_abs (reflection_point_line a L) L = point_line_abs a L := by{
  unfold point_line_abs
  simp [*]
  rw[← reflection_point_line_pmidpoint a L, point_abs_pmidpoint,pmidpoint_symm, point_abs_pmidpoint,point_abs_symm]
}

/-Reflection along the real line is the same as conjugating:-/
lemma reflection_point_line_real_line(a : Point): reflection_point_line a real_line = pconj a := by{
  unfold reflection_point_line
  rw[foot_real_line]
  unfold reflection_point_point padd p_scal_mul pneg pconj conj
  simp
  obtain ⟨a1,a2⟩ := a
  simp
  have : (starRingEnd ℂ) { re := a1, im := a2 } = { re := a1, im := -a2} := by{rfl}
  rw[this]
  have : 2 * (↑a1:ℂ) = 2*{re := a1, im := 0} := by{
    simp
    exact rfl
  }
  rw[this]
  have : 2*{re := a1, im := 0} = ({re := 2*a1, im := 0}:ℂ) := by{
    refine Complex.ext_iff.mpr ?_
    simp
  }
  rw[this]
  simp
  ring
}

/-this is perp in the following sense:-/

lemma reflection_point_line_perp_through{a : Point}{L : Line}(h: ¬Lies_on a L): qLine_through (reflection_point_line a L) a = perp_through L a := by{
  have s1: (reflection_point_line a L) ≠ a := by{
    contrapose h
    simp at *
    exact (reflection_point_line_on_line a L).mp h
  }
  have s2: qLine_through (reflection_point_line a L) a = Line_through s1 := by{
    apply line_through_unique
    constructor
    exact qline_through_mem_left (reflection_point_line a L) a
    exact qline_through_mem_right (reflection_point_line a L) a
  }
  rw[s2, ← foot_line_through h]
  apply line_through_unique
  constructor
  unfold Lies_on Line_through
  simp
  unfold reflection_point_line reflection_point_point p_scal_mul pneg padd colinear det conj
  simp
  ring

  exact line_through_mem_right s1
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

/-from definitions we get sort of a universal property:-/

lemma reflection_line_point_lies_on (L : Line)(a p : Point): Lies_on (reflection_point_point p a) (reflection_line_point L a) ↔ Lies_on p L := by{
  obtain ⟨u,v,uv,h1,h2⟩ := ex_points_on_line L
  have hL: L = Line_through uv := by{
    apply line_through_unique
    tauto
  }
  have uv2: reflection_point_point u a ≠ reflection_point_point v a := by{
    by_contra p0
    have : u = v := by{
      rw[← reflection_point_point_twice u a, ← reflection_point_point_twice v a]
      rw[p0]
    }
    contradiction
  }
  have g: reflection_line_point L a = Line_through uv2 := by{
    apply line_through_unique
    constructor
    unfold reflection_line_point Lies_on
    simp
    use u
    constructor
    unfold Lies_on at h1
    assumption
    rfl

    unfold reflection_line_point Lies_on
    simp
    use v
    constructor
    unfold Lies_on at h2
    assumption
    rfl
  }
  constructor
  intro h
  rw[g] at h
  unfold Line_through Lies_on at h
  simp at h
  rw[hL]
  unfold Lies_on Line_through
  simp
  rw[← reflection_point_point_twice u a, ← reflection_point_point_twice v a, ← reflection_point_point_twice p a]
  exact reflection_point_point_colinear2 a h

  intro h
  rw[hL] at h
  rw[g]
  unfold Lies_on Line_through
  unfold Lies_on Line_through at h
  simp at *
  exact reflection_point_point_colinear2 a h
}

  /-same properties as usual:-/

lemma reflection_line_point_twice (L : Line)(a : Point): reflection_line_point (reflection_line_point L a) a = L := by{
  ext p
  constructor
  intro h
  suffices : Lies_on p L
  unfold Lies_on at this
  assumption

  have tt: Lies_on p (reflection_line_point (reflection_line_point L a) a) := by{
    unfold Lies_on
    assumption
  }
  have zw: Lies_on (reflection_point_point p a) (reflection_line_point L a) := by{
    rw[← reflection_point_point_twice p a] at tt
    exact (reflection_line_point_lies_on (reflection_line_point L a) a (reflection_point_point p a)).1 tt
  }
  exact (reflection_line_point_lies_on L a p).1 zw

  intro h
  suffices : Lies_on p (reflection_line_point (reflection_line_point L a) a)
  unfold Lies_on at this
  assumption

  have ll: Lies_on p L := by{
    unfold Lies_on
    assumption
  }
  have zw: Lies_on (reflection_point_point p a) (reflection_line_point L a) := by{
    exact (reflection_line_point_lies_on L a p).2 ll
  }
  rw[← reflection_point_point_twice p a]
  exact (reflection_line_point_lies_on (reflection_line_point L a) a (reflection_point_point p a)).2 zw
}
/-You can do much more with reflections:
For example show circles reflection are still circles, reflect lines across lines etc.
However this becomes so repetitive, I skip it, as reflections wont actually be used much at all.

Parallel lines stay parallel, tangents tangents and so on and so forth.-/
