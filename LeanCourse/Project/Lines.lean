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

/-And sometimes this point has two be different to another point:-/
lemma ex_different_point_on_line(p : Point)(L : Line): ∃(a : Point), Lies_on a L ∧ a ≠ p := by{
  obtain ⟨a,b,ab,ah,bh⟩ := ex_points_on_line L
  by_cases a0: a = p
  use b
  constructor
  assumption
  contrapose ab
  simp at *
  rw[a0,ab]

  use a
}

lemma line_through_symm{a b : Point}(ab : a ≠ b): Line_through (Ne.symm ab) = Line_through ab := by{
  ext x
  unfold Line_through
  simp
  constructor
  · intro h
    exact colinear_perm12 b a x h
  intro h
  exact colinear_perm12 a b x h
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

/-We can permutate those:-/
lemma copunctal_perm12(L R S : Line)(h: Copunctal L R S): Copunctal R L S := by{
  unfold Copunctal at *
  rw[inter_assoc, inter_comm, inter_assoc, inter_comm S.range, ← inter_assoc, h]
}

lemma copunctal_perm23(L R S : Line)(h: Copunctal L R S): Copunctal L S R := by{
  unfold Copunctal at *
  rw[inter_assoc, inter_comm S.range, ←inter_assoc, h]
}

lemma copunctal_perm13(L R S : Line)(h: Copunctal L R S): Copunctal S R L := by{
  unfold Copunctal at *
  rw[inter_assoc, inter_comm, inter_comm R.range, h]
}

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

/-Going along yourself does nothing:-/
@[simp] lemma go_along_self(a : Point)(R : ℝ) : go_along a a R = a := by{
  ext
  unfold go_along p_scal_mul padd
  simp
  unfold zero
  simp
}

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

/-Going along a to b is similar to going along b to a in the following sense:-/
lemma go_along_symm(a b : Point)(R : ℝ): go_along b a R = go_along a b (point_abs a b - R):= by{
  unfold go_along p_scal_mul padd dir
  rw[point_abs_symm b a]
  simp
  by_cases ab: a = b
  · rw[ab]
    simp

  have : (↑(point_abs a b) : ℂ) ≠ 0 := by{
    contrapose ab
    simp at *
    exact abs_zero_imp_same a b ab
  }
  field_simp
  ring
}

/-And we the distance from a is exactly R, if a ≠ b and R positive:-/

lemma go_along_abs1{a b : Point}(ab : a ≠ b)(R : ℝ): point_abs a (go_along a b R) = abs R := by{
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

/-If R is negative, the distance from b is R + point_abs a b-/
lemma go_along_abs2{a b : Point}(ab : a ≠ b)(R : ℝ): point_abs b (go_along a b R) = abs (point_abs a b - R) := by{
  have : R = point_abs a b - (point_abs a b - R) := by{ring}
  nth_rw 1 [this]
  rw[← go_along_symm a b (point_abs a b - R)]
  rw[go_along_abs1]
  tauto
}

lemma colinear_go_along {a b c : Point}(ab : a ≠ b)(h : colinear a b c ): ∃R:ℝ, c = go_along a b R := by{
  apply colinear_perm23 at h
  apply (colinear_alt2 a c b).1 at h
  simp [*] at h
  obtain ⟨t,ht⟩ := h
  use (t* (point_abs a b))
  unfold go_along
  rw[ht]
  unfold padd p_scal_mul dir
  ext
  simp
  have : (↑(point_abs a b) : ℂ) ≠ 0 := by{
    contrapose ab
    simp at *
    exact abs_zero_imp_same a b ab
  }
  field_simp
  ring
}

lemma go_along_lies_on{a b : Point}{L : Line}(R : ℝ)(h : Lies_on a L ∧ Lies_on b L): Lies_on (go_along a b R) L := by{
  by_cases ab : a=b
  rw[ab]
  simp
  tauto

  have hL: L = Line_through ab := by{
    apply line_through_unique
    assumption
  }
  rw[hL]
  unfold Lies_on Line_through
  simp
  exact go_along_colinear a b R
}

lemma go_along_inj{a b : Point}(ab : a ≠ b){r r' : ℝ}(h: go_along a b r = go_along a b r') : r = r' := by{
  unfold go_along dir padd p_scal_mul at *
  simp at h
  obtain h|h|h := h
  · · assumption
  · contrapose h
    exact sub_neq_zero (Ne.symm ab)
  contrapose ab
  simp
  exact abs_zero_imp_same a b h
}

@[simp] lemma go_along_zero(a b : Point): go_along a b 0 = a := by{
  unfold go_along
  unfold padd p_scal_mul
  simp
}

@[simp] lemma go_along_point_abs(a b : Point): go_along a b (point_abs a b) = b := by{
  rw[go_along_symm, point_abs_symm]
  simp
}

/-Three points on a given line are colinear:-/

lemma three_point_line_colinear{L : Line}{a b c : Point}(ha: Lies_on a L)(hb: Lies_on b L)(hc: Lies_on c L): colinear a b c := by{
  by_cases bc : b = c
  · apply colinear_self
    tauto
  have hL: L = Line_through bc := by{
    apply line_through_unique
    tauto
  }
  rw[hL] at ha
  unfold Lies_on Line_through at ha
  simp at ha
  apply colinear_perm13
  apply colinear_perm12
  assumption
}
