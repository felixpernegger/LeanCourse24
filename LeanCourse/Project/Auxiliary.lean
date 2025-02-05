import LeanCourse.Project.Pythagoras
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

/-Proving same_side_trans is more or less the same as proving Pasch's axiom, which is surprisingly difficult and not done here (or anywhere else in this project...).-/





/-With this we get a relatively nice notion for the inside of the Triangle:-/

/-Same side of ab as c, etc.-/

def inside_triangle (T : Triangle)(p : Point): Prop :=
  same_side (tri_ab T) T.c p ∧ same_side (tri_bc T) T.a p ∧ same_side (tri_ca T) T.b p


/-The inside of a circle is shorter to define:-/
def inside_circle(a : Point)(C : CCircle) : Prop :=
  point_abs a (Center C) < Radius C

/-Similar the outside:-/

def outside_circle(a : Point)(C : CCircle) : Prop :=
  Radius C < point_abs a (Center C)

/-Now we do some tautological stuff, to simplify proving Lines are Copunctual and stuff-/

def pairwise_different_point3 (a b c : Point): Prop :=
  (a ≠ b)∧(b ≠ c)∧(c ≠ a)

lemma pairwise_different_point3_perm12 {a b c : Point}(h: pairwise_different_point3 a b c): pairwise_different_point3 b a c := by{
  unfold pairwise_different_point3 at *
  tauto
}

lemma pairwise_different_point3_perm13 {a b c : Point}(h: pairwise_different_point3 a b c): pairwise_different_point3 c b a := by{
  unfold pairwise_different_point3 at *
  tauto
}

lemma pairwise_different_point3_perm23 {a b c : Point}(h: pairwise_different_point3 a b c): pairwise_different_point3 a c b := by{
  unfold pairwise_different_point3 at *
  tauto
}

def pairwise_different_lines3 (L R T : Line): Prop :=
  (L ≠ R)∧(R ≠ T)∧(T ≠ L)

lemma pairwise_different_lines3_perm12 {L R T : Line}(h: pairwise_different_lines3 L R T): pairwise_different_lines3 R L T := by{
  unfold pairwise_different_lines3 at *
  tauto
}

lemma pairwise_different_lines3_perm13 {L R T : Line}(h: pairwise_different_lines3 L R T): pairwise_different_lines3 T R L := by{
  unfold pairwise_different_lines3 at *
  tauto
}

lemma pairwise_different_lines3_perm23 {L R T : Line}(h: pairwise_different_lines3 L R T): pairwise_different_lines3 L T R := by{
  unfold pairwise_different_lines3 at *
  tauto
}

def lines_int_nonempty(L R T : Line) : Prop :=
  ∃p : Point, Lies_on p L ∧ Lies_on p R ∧ Lies_on p T

lemma lines_int_nonempty_perm12{L R T : Line}(h: lines_int_nonempty L R T): lines_int_nonempty R L T := by{
  unfold lines_int_nonempty at *
  tauto
}

lemma lines_int_nonempty_perm13{L R T : Line}(h: lines_int_nonempty L R T): lines_int_nonempty T R L := by{
  unfold lines_int_nonempty at *
  tauto
}

lemma lines_int_nonempty_perm23{L R T : Line}(h: lines_int_nonempty L R T): lines_int_nonempty L T R := by{
  unfold lines_int_nonempty at *
  tauto
}

def lines_not_same(L R T : Line): Prop :=
  (L ≠ R) ∨ (R ≠ T) ∨ (T ≠ L)

lemma lines_not_same_perm12{L R T : Line}(h: lines_not_same L R T): lines_not_same R L T := by{
  unfold lines_not_same at *
  tauto
}

lemma lines_not_same_perm13{L R T : Line}(h: lines_not_same L R T): lines_not_same T R L := by{
  unfold lines_not_same at *
  tauto
}

lemma lines_not_same_perm23{L R T : Line}(h: lines_not_same L R T): lines_not_same L T R := by{
  unfold lines_not_same at *
  tauto
}

lemma lines_not_same_simp(L R T : Line)(h : ∃(p : Point), Lies_on p L ∧ ¬Lies_on p R): lines_not_same L R T := by{
  unfold lines_not_same
  left
  by_contra p0
  rw[p0] at h
  tauto
}

/-the above get useful here:-/

lemma copunctal_simp{L R T : Line}(h: lines_not_same L R T)(h': lines_int_nonempty L R T): Copunctal L R T := by{
  unfold Copunctal
  apply le_antisymm
  swap
  refine one_le_encard_iff_nonempty.mpr ?intro.a.a
  obtain ⟨p,ph⟩ := h'
  have hp': p ∈ L.range ∩ R.range ∩ T.range := by{
    unfold Lies_on at ph
    tauto
  }
  use p

  contrapose h
  unfold lines_not_same
  simp at *
  obtain ⟨a,b,ah,bh,ab⟩ := one_lt_encard_iff.mp h
  simp at ah bh
  obtain ⟨ah12,ah3⟩ := ah
  obtain ⟨ah1,ah2⟩ := ah12
  obtain ⟨bh12,bh3⟩ := bh
  obtain ⟨bh1,bh2⟩ := bh12
  have hL: L = Line_through ab := by{
    apply line_through_unique
    unfold Lies_on
    tauto
  }
  have hR: R = Line_through ab := by{
    apply line_through_unique
    unfold Lies_on
    tauto
  }
  have hT: T = Line_through ab := by{
    apply line_through_unique
    unfold Lies_on
    tauto
  }
  rw[hL,hR,hT]
  tauto
}

/-And a final one with nonparallel lines:-/

lemma lines_not_same_parallel(L R T : Line)(h: ¬Parallel L R): lines_not_same L R T := by{
  unfold lines_not_same
  left
  contrapose h
  simp at *
  apply (parallel_def L R).2
  right
  rw[h]
}

/-We make a fancy way to write the intersercion on copunctal lines:-/
/-for lack of a better word, the intersection if called line_center-/

lemma line_center_ex {L R T : Line}(h : Copunctal L R T): ∃(p : Point), Lies_on p L ∧ Lies_on p R ∧ Lies_on p T := by{
  unfold Copunctal at h
  have : (L.range ∩ R.range ∩ T.range).Nonempty := by{
    apply Set.encard_ne_zero.1
    rw[h]
    norm_num
  }
  obtain ⟨p,hp⟩ := this
  use p
  unfold Lies_on
  obtain ⟨hp12,hp3⟩ := hp
  obtain ⟨hp1,hp2⟩ := hp12
  tauto
}

def Line_center {L R T : Line}(h : Copunctal L R T) : Point :=
  (line_center_ex h).choose

/-This lies on all 3 lines:-/
lemma line_center_on_line {L R T : Line}(h : Copunctal L R T): Lies_on (Line_center h) L ∧ Lies_on (Line_center h) R ∧ Lies_on (Line_center h) T := by{
  exact (Classical.choose_spec (line_center_ex h))
}

lemma line_center_on_line1 {L R T : Line}(h : Copunctal L R T): Lies_on (Line_center h) L := by{
  exact (line_center_on_line h).1
}

lemma line_center_on_line2 {L R T : Line}(h : Copunctal L R T): Lies_on (Line_center h) R := by{
  exact (line_center_on_line h).2.1
}

lemma line_center_on_line3 {L R T : Line}(h : Copunctal L R T): Lies_on (Line_center h) T := by{
  exact (line_center_on_line h).2.2
}

/-And of course it is unique-/

theorem line_center_unique {L R T : Line}{p : Point}(h : Copunctal L R T)(hp : Lies_on p L ∧ Lies_on p R ∧ Lies_on p T) : p = Line_center h := by{
  by_contra p0
  unfold Copunctal at h
  have : 1 < (L.range ∩ R.range ∩ T.range).encard := by{
    apply Set.one_lt_encard_iff.2
    use p
    use Line_center h
    constructor
    unfold Lies_on at hp
    tauto

    have : Lies_on (Line_center h) L ∧ Lies_on (Line_center h) R ∧ Lies_on (Line_center h) T := line_center_on_line h
    unfold Lies_on at this
    tauto
  }
  rw[h] at this
  tauto
}

/-Also at this point maybe note perp triangle points are noncolinear:-/

lemma perp_points_not_colinear{a b p : Point}(h: pairwise_different_point3 a b p)(h': perp_points p a p b): noncolinear a b p := by{
  contrapose h
  unfold pairwise_different_point3 noncolinear perp_points at *
  simp at *

  apply colinear_perm12 at h
  apply colinear_perm13 at h
  apply (colinear_alt p a b).1 at h
  have n: (p.x - a.x) / (p.x - b.x) = 0 := by{exact Eq.symm (Complex.ext (id (Eq.symm h')) (id (Eq.symm h)))}
  simp at n
  obtain n|n := n
  · have : p = a := by{
    ext
    calc
      p.x = p.x - (p.x - a.x) := by{rw[n];ring}
        _= a.x := by{ring}
    }
    tauto
  have : p = b := by{
    ext
    calc
      p.x = p.x - (p.x - b.x) := by{rw[n];ring}
        _= b.x := by{ring}
    }
  tauto
}
