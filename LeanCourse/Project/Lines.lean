import LeanCourse.Project.Basic
import Mathlib

open Function Set Classical

noncomputable section


/- Now we feel confident enough to define Lines:-/

@[ext] structure Line where
  range : Set Point
  span : ∃ a b : Point, a ≠ b ∧ range = {c : Point | colinear a b c}

/- A shorthand for a point lying on a line:-/
def Lies_on (a : Point)(L : Line) : Prop :=
  a ∈ L.range

lemma ex_unique_line_mem {a b : Point}(h: a ≠ b) : ∃! L : Line, Lies_on a L ∧ Lies_on b L := by{
  unfold Lies_on at *
  --Note: Maybe redo this prove properly with Line_through
  let C := {c : Point| colinear a b c}
  have : ∃ x y : Point, x ≠ y ∧ C = {c : Point| colinear x y c} := by{
    use a
    use b
  }
  use Line.mk C this
  simp
  unfold C
  simp
  constructor
  constructor
  have h: a=b ∨ b=a ∨ a=a := by tauto
  exact colinear_self a b a h
  have h: a=b ∨ b=b ∨ b=a := by tauto
  exact colinear_self a b b h

  intro J ah bh
  ext x
  constructor
  intro xh
  simp at *
  obtain ⟨Jc,⟨u,v,⟨uv,sp⟩⟩⟩ := J
  simp at *
  rw[sp] at *
  simp at *
  have vab: colinear v a b := by{exact colinear_trans u v a b ah bh uv}
  have vbx: colinear v b x := by{exact colinear_trans u v b x bh xh uv}
  apply colinear_perm12
  apply colinear_perm13 at vab
  apply colinear_perm12 at vab
  apply colinear_perm13 at vab
  by_cases p : v = b
  · rw[← p]
    exact colinear_trans u v a x ah xh uv
  · exact colinear_trans v b a x vab vbx p

  intro hx
  obtain ⟨J1,J2⟩ := J
  obtain ⟨c,d,cd,gen⟩ := J2
  simp at *
  rw[gen] at *
  simp at *
  have dab : colinear d a b := by{exact colinear_trans c d a b ah bh cd}
  apply colinear_perm13 at dab
  apply colinear_perm12 at hx
  have ba: ¬b = a := by{exact fun a_1 ↦ h (id (Eq.symm a_1))}
  have adx : colinear a d x := by{exact colinear_trans b a d x dab hx ba}
  apply colinear_perm13 at ah
  apply colinear_perm12
  by_cases ad : a = d
  · rw[← ad]
    clear ah
    clear adx
    clear dab
    rw[← ad] at bh
    apply colinear_perm13 at bh
    exact colinear_trans b a c x bh hx ba
  · exact colinear_trans a d c x ah adx ad
  }

/-Now lets define the unqiue Line going through two Lines:-/

def Line_through {a b : Point} (h : a ≠ b) : Line where
  range := {c | colinear a b c}
  span := by{
    use a
    use b
  }

/-Some small observations:-/
lemma line_through_mem_left {a b : Point} (h: a ≠ b): Lies_on a (Line_through h) := by{
  unfold Lies_on
  unfold Line_through
  simp
  apply colinear_self
  right;right
  rfl
}

lemma line_through_mem_right {a b : Point}(h: a ≠ b) : Lies_on b (Line_through h) := by{
  unfold Lies_on
  unfold Line_through
  simp
  apply colinear_self
  right;left
  rfl
}

/-Above Lemma can now be stated much nicer:-/

theorem line_through_unique (a b : Point)(L : Line)(ab: a≠ b)(Lh : Lies_on a L ∧ Lies_on b L): L = Line_through ab := by{
apply ex_unique_line_mem at ab
obtain ⟨U,Uh1,Uh2⟩ := ab
simp at Uh2
have LU: L = U := by{exact Uh2 L Lh.1 Lh.2}
have LTU: Line_through ab = U := by{specialize Uh2 (Line_through ab) (line_through_mem_left ab) (line_through_mem_right ab);assumption}
rw[LU,LTU]
}

/-We can use this to show that two Lines are already the same if they intersect in more than one Point:-/
theorem lines_eq (L R : Line)(a b : Point)(ab : a ≠ b)(ah : Lies_on a L ∧ Lies_on a R)(bh : Lies_on b L ∧ Lies_on b R) : L = R := by{
  obtain ⟨aL,aR⟩ := ah
  obtain ⟨bL, bR⟩ := bh
  apply ex_unique_line_mem at ab
  obtain ⟨U,⟨Uh1,Uh2⟩⟩ := ab
  simp at Uh2
  have LU: L = U := by{exact Uh2 L aL bL}
  have RU: R = U := by{exact Uh2 R aR bR}
  rw[LU,RU]
}

/-same theorem in a form we can use maybe more often:-/

theorem lines_eq_ex (L R : Line)(h: ∃a b : Point, a ≠ b ∧ Lies_on a L ∧ Lies_on a R ∧ Lies_on b L ∧ Lies_on b R) : L = R := by{
  obtain ⟨a,b,h1,h2,h3,h4,h5⟩ := h
  have ah : Lies_on a L ∧ Lies_on a R := by{tauto}
  have bh : Lies_on b L ∧ Lies_on b R := by{tauto}
  exact lines_eq L R a b h1 ah bh
}

/-Finally, every line can be interpreted as a "Line through":-/
lemma line_eq_line_through (L : Line) (a b : Point)(h: Lies_on a L ∧ Lies_on b L)(ab: a ≠ b): L = Line_through ab := by{
  apply line_through_unique a b
  assumption
}
/-There exist two different points on a Line:-/
lemma ex_points_on_line (L : Line): ∃(u v : Point), (u ≠ v) ∧ (Lies_on u L) ∧ (Lies_on v L) := by{
  obtain ⟨S,a,b,ab,r⟩ := L
  use a
  use b
  constructor
  exact ab
  constructor
  unfold Lies_on
  simp
  rw[r]
  simp
  apply colinear_self
  right
  right
  rfl

  unfold Lies_on
  simp
  rw[r]
  simp
  apply colinear_self
  right
  left
  rfl
}

/-Sometimes we just need a single Point on a Line:-/
lemma ex_point_on_line(L:Line): ∃(a : Point), Lies_on a L := by{
  obtain ⟨u,_,_,h,_⟩ := ex_points_on_line L
  use u
}

/-We can also conjugate lines:-/
def line_conj : Line → Line :=
  fun L ↦ ⟨set_conj L.range, by{
    obtain ⟨s,t,st,stL⟩ := L.2
    use pconj s
    use pconj t
    constructor
    by_contra h0
    rw[← pconj_twice s, ← pconj_twice t] at st
    tauto
    unfold set_conj
    simp
    ext x
    constructor
    intro xh
    simp at *
    obtain ⟨a,ah1,ah2⟩ := xh
    rw[ah2]
    rw[stL] at ah1
    simp at ah1
    exact colinear_conj ah1

    intro xh
    simp at *
    use pconj x
    constructor
    rw[stL]
    simp
    rw[← pconj_twice s, ← pconj_twice t]
    apply colinear_conj
    assumption

    simp
  }⟩

  @[simp] lemma line_conj_twice (L : Line) : line_conj (line_conj L) = L := by{
    unfold line_conj
    simp
  }

/-An intermediate goal is to prove Ceva's theorem. For this we first need a definition for sLines being copunctal,
lenght proportions and how they realtie to areas proportions-/

def Copunctal (L R S : Line) : Prop :=
  Set.encard (L.range ∩ R.range ∩ S.range) = 1

/- With those two lemmas together every Line can be written as a Line_through (i couldnt manage to get it into one lemma, which would have been nice of course)-/

/-We can shift Lines. These are exactly the parallel lines:-/
def shift_line: Line → Point → Line :=
  fun L p ↦ ⟨{s : Point | ∃l : L.range, s = padd l p}, by{
    obtain ⟨S,a,b,ab,r⟩ := L
    use (padd a p)
    use (padd b p)
    constructor
    unfold padd
    simp
    contrapose ab
    simp at *
    ext
    assumption

    ext s
    simp
    rw[r]
    simp
    constructor
    intro h
    obtain ⟨l,lh1,lh2⟩ := h
    rw[lh2]
    exact colinear_shift p lh1

    intro h
    use padd s (pneg p)
    constructor
    swap
    unfold pneg padd
    simp

    have : colinear (padd (padd a p) (pneg p)) (padd (padd b p) (pneg p)) (padd s (pneg p)) := by{
      exact colinear_shift (pneg p) h
    }
    have sla : (padd (padd a p) (pneg p)) = a := by{
      unfold padd pneg
      simp
    }
    have slb : (padd (padd b p) (pneg p)) = b := by{
      unfold padd pneg
      simp
    }
    rw[sla,slb] at this
    assumption
  }⟩

/-Shifting line a group operation:-/
lemma shift_line_zero (L : Line): shift_line L (Point.mk (0 : ℂ)) = L := by{
  unfold shift_line
  simp [padd_zero]
}


lemma shift_line_trans (L : Line)(p q : Point) : shift_line (shift_line L p) q = shift_line L (padd p q) := by {
  unfold shift_line
  simp
  ext x
  constructor
  intro xh
  simp at *
  obtain ⟨a,⟨⟨b,⟨bh1,bh2⟩⟩,ah⟩⟩ := xh
  use b
  constructor
  assumption
  rw[← padd_assoc]
  rw[← bh2]
  rw[ah]

  intro xh
  simp at *
  obtain ⟨a,ah1,ah2⟩ := xh
  use padd a p
  constructor
  use a
  rw[padd_assoc]
  assumption
}

--lemma shift_line_conj (L : Line)(p : Point): shift_line

/-Shifting a point of a line by the same vector is in the shifted line:-/

lemma mem_line_shift (a p : Point)(L : Line)(h: Lies_on a L): Lies_on (padd a p) (shift_line L p) := by{
  unfold Lies_on
  unfold shift_line
  simp
  use a
  constructor
  exact h
  rfl
}

@[simp] lemma shift_line_conj (L : Line)(a : Point) : line_conj (shift_line L a) = shift_line (line_conj L) (pconj a) := by{
  unfold line_conj shift_line
  ext x
  simp
  constructor
  intro xh
  unfold set_conj at *
  simp at *
  obtain ⟨u,uh1,uh2⟩ := xh
  obtain ⟨v,vh1,vh2⟩ := uh1
  rw[uh2]
  clear uh2 x
  use pconj v
  constructor
  use v
  rw[vh2]
  unfold pconj
  unfold padd
  simp

  intro xh
  obtain ⟨u,uh1,uh2⟩ := xh
  unfold set_conj
  simp
  use pconj x
  constructor
  use pconj u
  constructor
  swap
  rw[uh2]
  unfold pconj padd
  simp
  swap
  simp

  rw[← pconj_twice u] at uh1
  exact (set_conj_def (pconj u) L.range).mpr uh1
}

/-Now we introduce the notion of going between two points in a cetain direction a certain distance:-/

def go_along : Point → Point → ℝ → Point :=
  fun a b R ↦ padd a (p_scal_mul R (dir a b))

/-This is always colinear:-/

lemma go_along_colinear (a b : Point)(R : ℝ): colinear a b (go_along a b R) := by{
  apply colinear_perm23
  apply (colinear_alt2 a (go_along a b R) b).2
  by_cases ab: a = b
  · tauto
  right

  use R / point_abs a b
  have absub: a.x - b.x ≠ 0 := by{exact sub_neq_zero ab}
  unfold go_along p_scal_mul dir padd
  ext
  simp
  have : ↑(point_abs a b : ℂ) ≠ 0 := by{
    contrapose ab
    simp at *
    exact abs_zero_imp_same a b ab
  }
  field_simp
  ring
}

/-And we the distance from a is exactly R, if a ≠ b and R positive:-/

lemma go_along_abs{a b : Point}(ab : a ≠ b)(R : ℝ): point_abs a (go_along a b R) = abs R := by{
  unfold go_along point_abs padd
  simp
  have t:  Complex.abs (p_scal_mul (↑R) (dir a b)).x = Complex.abs R * Complex.abs (dir a b).x := by{exact IsAbsoluteValue.abv_mul (⇑Complex.abs) (↑R) (dir a b).x}
  rw[Complex.abs_ofReal R] at t
  have : pabs (dir a b) = 1 := by{exact dir_one ab}
  unfold pabs at this
  rw[this] at t
  simp at t
  assumption
}
