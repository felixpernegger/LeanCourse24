import LeanCourse.Project.Circles
import Mathlib

open Function Set Classical

noncomputable section

/-This section is for introducing perpendiculars. Goals are to highilght how Parallel and Perpenduclar
are connected, show every point and line has a unique perpendicular line and finishing off with the orthocenter.-/

/-As Perpendicular is way too long of a word to not mistype all the type, the word "perpendicular" will be abbreviated to "perp" in all but one case-/

/-Some lemmas about complex numbers that will be cinvenient here-/
#check complex_real_mul

lemma complex_im_mul{x y : ℂ}(hx: x.re = 0)(hy : y.re = 0): (x*y).im=0 := by{
  obtain ⟨x1,x2⟩ := x
  obtain ⟨y1,y2⟩ := y
  simp at *
  rw[hx,hy]
  ring
}

lemma complex_real_im_mul{x y : ℂ}(hx: x.im = 0)(hy: y.re = 0): (x*y).re = 0 := by{
  obtain ⟨x1,x2⟩ := x
  obtain ⟨y1,y2⟩ := y
  simp at *
  rw[hx,hy]
  ring
}

lemma complex_im_real_mul{x y : ℂ}(hx: x.re = 0)(hy: y.im = 0): (x*y).re = 0 := by{
  obtain ⟨x1,x2⟩ := x
  obtain ⟨y1,y2⟩ := y
  simp at *
  rw[hx,hy]
  ring
}

lemma complex_real_recip {x : ℂ}(h : x.im = 0): (1/x).im = 0 := by{
  obtain ⟨x1,x2⟩ := x
  simp at *
  tauto
}

lemma complex_im_recip {x : ℂ}(h : x.re = 0): (1/x).re = 0 := by{
  obtain ⟨x1,x2⟩ := x
  simp at *
  tauto
}

/-For the convenience the last two lemma as fractions:-/
lemma complex_real_recip_quot {x y : ℂ}(h: (x/y).im = 0): (y/x).im = 0 := by{
  have: y/x = 1/(x/y) := by{
    field_simp
  }
  rw[this]
  exact complex_real_recip h
}

lemma complex_im_recip_quot {x y : ℂ}(h: (x/y).re = 0): (y/x).re = 0 := by{
  have: y/x = 1/(x/y) := by{
    field_simp
  }
  rw[this]
  exact complex_im_recip h
}

/-First we define perpedicular "points"-/
def perp_points(a b c d : Point) : Prop :=
  ((a.x-b.x)/(c.x-d.x)).re = 0

/-We have three ways to permutate this:-/

lemma perp_points_perm_front{a b c d : Point}(h : perp_points a b c d) : perp_points b a c d := by{
  unfold perp_points at *
  have : -((a.x - b.x) / (c.x - d.x)).re = 0 := by{linarith}
  rw[← this]
  by_cases h0: c.x-d.x = 0
  rw[h0]
  ring_nf
  norm_num


  clear this h
  calc
    ((b.x - a.x) / (c.x - d.x)).re = (-1* (a.x-b.x)/(c.x-d.x)).re := by{ring_nf}
      _= -1* (((a.x-b.x)/(c.x-d.x)).re) := by{ -- I am getting trolled here fr
        have : -1 * (a.x - b.x) / (c.x - d.x) = -1 * ((a.x - b.x) / (c.x - d.x)) := by{
          exact mul_div_assoc (-1) (a.x - b.x) (c.x - d.x)
        }
        rw [this]
        clear this
        simp
      }
      _= -((a.x - b.x) / (c.x - d.x)).re := by{exact Eq.symm (neg_eq_neg_one_mul ((a.x - b.x) / (c.x - d.x)).re)}
}

lemma perp_points_perm_switch{a b c d : Point}(h : perp_points a b c d): perp_points c d a b := by{
  unfold perp_points at *
  exact complex_im_recip_quot h
}

lemma perp_points_perm_back{a b c d : Point}(h: perp_points a b c d): perp_points a b d c := by{
  apply perp_points_perm_switch
  apply perp_points_perm_front
  exact perp_points_perm_switch h
}

/-Nice to quickly get rid of edge cases:-/
lemma perp_points_self{a b c d : Point}(h : a = b ∨ c = d): perp_points a b c d := by{
  unfold perp_points
  obtain h|h := h
  rw[h]
  simp
  rw[h]
  simp
}

/-This is, in a way, transitive / we can stay on a line:-/

lemma perp_on_line{a b c d p : Point}(h:perp_points a b c d)(ab: a ≠ b)(ph: colinear a b p): perp_points b p c d := by{
  have ba: b ≠ a := by{tauto}
  apply perp_points_perm_front at h
  apply colinear_perm12 at ph
  apply colinear_perm23 at ph
  apply (colinear_alt b p a).1 at ph
  unfold perp_points at *
  apply sub_neq_zero at ba
  have : ((b.x - p.x) / (c.x - d.x)) = ((b.x - p.x) / (b.x - a.x)) * ((b.x - a.x) / (c.x - d.x)) := by{
    field_simp
  }
  rw[this]
  exact complex_real_im_mul ph h
}

/-Now we feel ready to define perpendicular lines:-/
/-As usual, we use a "weak" version of the definition and improve it later-/

def Perpendicular(L R : Line) : Prop :=
  ∃ (a b c d : Point), (a ≠ b) ∧ (c ≠ d) ∧ (Lies_on a L) ∧ (Lies_on b L) ∧ (Lies_on c R) ∧ (Lies_on d R) ∧ (perp_points a b c d)

/-This obviously is nowhere near an equivalence relations, it is merely symmetric:-/
lemma perp_symm{L R : Line}(h: Perpendicular L R) : Perpendicular R L := by{
  unfold Perpendicular at *
  obtain ⟨u,v,s,r,uv,sr,uh,vh,sh,rh,h⟩ := h
  use s
  use r
  use u
  use v
  repeat
    constructor
    tauto
  exact perp_points_perm_switch h
}

/-This implies all pairs of points on the lines are perpendicular:-/
/-The prve doesnt use calculations, just a lot of colinear_trans and perp_on_line-/
lemma perp_all {L R : Line}{a b c d : Point}(LR: Perpendicular L R)(ah: Lies_on a L)(bh: Lies_on b L)(ch: Lies_on c R)(dh: Lies_on d R): perp_points a b c d := by{
  unfold Perpendicular at LR
  obtain ⟨u,v,s,r,uv,sr,uh,vh,sh,rh,h⟩ := LR
  have hL: L = Line_through uv := by{
    apply line_through_unique
    tauto
  }
  have hR: R = Line_through sr := by{
    apply line_through_unique
    tauto
  }
  rw[hL] at ah bh
  rw[hR] at ch dh
  unfold Lies_on Line_through at ah bh ch dh
  simp at ah bh ch dh
  have vasr : perp_points v a s r := by{
    exact perp_on_line h uv ah
  }
  have vbsr : perp_points v b s r := by{
    exact perp_on_line h uv bh
  }
  by_cases va: v=a
  symm at va
  rw[va]
  by_cases vb: v=b
  symm at vb
  rw[vb]
  apply perp_points_self
  left
  rfl
  apply perp_points_perm_switch
  apply perp_points_perm_switch at vbsr
  have rcvb : perp_points r c v b := by{
    exact perp_on_line vbsr sr ch
  }
  by_cases rc: r=c
  rw[rc] at vbsr rcvb dh sr
  exact perp_on_line vbsr sr dh

  have rcd: colinear r c d := by{
    exact colinear_trans s r c d ch dh sr
  }
  exact perp_on_line rcvb rc rcd

  have vab: colinear v a b := by{
    exact colinear_trans u v a b ah bh uv
  }
  have absr : perp_points a b s r := by{
    exact perp_on_line vasr va vab
  }
  apply perp_points_perm_switch at absr
  apply perp_points_perm_switch
  have rcab: perp_points r c a b := by{
    exact perp_on_line absr sr ch
  }
  have rcd: colinear r c d := by{
    exact colinear_trans s r c d ch dh sr
  }
  by_cases rc: r = c
  · rw[rc] at sr absr dh
    exact perp_on_line absr sr dh
  exact perp_on_line rcab rc rcd
}

lemma perp_line_through_points{a b c d}{ab : a ≠ b}{cd : c ≠ d}(h : Perpendicular (Line_through ab) (Line_through cd)): perp_points a b c d := by{
  apply perp_all h
  exact line_through_mem_left ab
  exact line_through_mem_right ab
  exact line_through_mem_left cd
  exact line_through_mem_right cd
}

lemma perp_quot{a b c d : Point}(ab : a ≠ b)(cd : c ≠ d): Perpendicular (Line_through ab) (Line_through cd) ↔ perp_points a b c d := by{
  constructor
  intro h
  apply perp_all h
  repeat
    unfold Lies_on Line_through
    simp
    apply colinear_self
    tauto

  intro h
  unfold Perpendicular
  use a
  use b
  use c
  use d
  constructor
  assumption
  constructor
  assumption
  repeat
    constructor
    unfold Lies_on Line_through
    simp
    apply colinear_self
    tauto
  assumption
}

/-A simple but important statement we will need for inersections on perpendicular lines:
Perpendicular lines aren't parallel.-/

lemma perp_not_parallel (L R : Line)(h : Perpendicular L R): ¬ Parallel L R := by{
  obtain ⟨a,b,ab,ah,bh⟩ := ex_points_on_line L
  obtain ⟨c,d,cd,ch,dh⟩ := ex_points_on_line R
  have hL: L = Line_through ab := by{
    apply line_through_unique
    tauto
  }
  have hR: R = Line_through cd := by{
    apply line_through_unique
    tauto
  }
  rw[hL,hR] at h
  apply (perp_quot ab cd).1 at h
  unfold perp_points at h
  rw[hL,hR]
  by_contra h0
  apply (parallel_quot ab cd).1 at h0
  have zero: (a.x-b.x)/(c.x-d.x) = 0 := by{
    exact Eq.symm (Complex.ext (id (Eq.symm h)) (id (Eq.symm h0)))
  }
  simp at zero
  obtain z|z := zero
  have : a=b := by{
    ext
    calc
      a.x = a.x - 0 := by{ring}
        _= a.x - (a.x-b.x) := by{rw[z]}
        _= b.x := by{ring}
  }
  contradiction

  have : c=d := by{
    ext
    calc
      c.x = c.x - 0 := by{ring}
        _= c.x - (c.x-d.x) := by{rw[z]}
        _= d.x := by{ring}
  }
  contradiction
}

/-Now we feel ready to get to the spicy stuff: the relationship of parallel and perpendicular lines-/

theorem parallel_perp (L : Line) {R S : Line}(LR : Parallel L R)(LS : Perpendicular L S): Perpendicular R S := by{
  obtain ⟨a,b,ab,ah,bh⟩ := ex_points_on_line L
  obtain ⟨c,d,cd,ch,dh⟩ := ex_points_on_line R
  obtain ⟨u,v,uv,uh,vh⟩ := ex_points_on_line S
  have hL: L = Line_through ab := by{
    apply line_through_unique
    tauto
  }
  have hR: R = Line_through cd := by{
    apply line_through_unique
    tauto
  }
  have hS: S = Line_through uv := by{
    apply line_through_unique
    tauto
  }
  rw[hL] at LR LS ah bh
  rw[hR] at LR ch dh
  rw[hR]
  rw[hS] at LS uh vh
  rw[hS]
  clear L hL R hR S hS
  apply (parallel_quot ab cd).1 at LR
  apply (perp_quot ab uv).1 at LS
  apply (perp_quot cd uv).2
  clear ah bh ch dh uh vh
  apply complex_real_recip_quot at LR
  unfold perp_points at *
  apply sub_neq_zero at ab
  have : (c.x - d.x) / (u.x - v.x) = ((c.x - d.x) / (a.x - b.x)) * ((a.x-b.x)/(u.x-v.x)) := by{
    field_simp
  }
  rw[this]
  exact complex_real_im_mul LR LS
}

/-Perpendicular is "antitransitive" in a way-/
/-Following proof is almost identitcal with the last one-/

lemma perp_perp (L : Line) {R S : Line}(LR: Perpendicular L R)(LS : Perpendicular L S): Parallel R S := by{
  obtain ⟨a,b,ab,ah,bh⟩ := ex_points_on_line L
  obtain ⟨c,d,cd,ch,dh⟩ := ex_points_on_line R
  obtain ⟨u,v,uv,uh,vh⟩ := ex_points_on_line S
  have hL: L = Line_through ab := by{
    apply line_through_unique
    tauto
  }
  have hR: R = Line_through cd := by{
    apply line_through_unique
    tauto
  }
  have hS: S = Line_through uv := by{
    apply line_through_unique
    tauto
  }
  rw[hL] at LR LS ah bh
  rw[hR] at LR ch dh
  rw[hR]
  rw[hS] at LS uh vh
  rw[hS]
  clear L hL R hR S hS
  apply (perp_quot ab uv).1 at LS
  apply (perp_quot ab cd).1 at LR
  apply (parallel_quot cd uv).2
  apply perp_points_perm_switch at LR
  clear ah bh ch dh uh vh
  unfold perp_points at *
  apply sub_neq_zero at ab
  have : (c.x - d.x) / (u.x - v.x) = ((c.x - d.x) / (a.x - b.x)) * ((a.x-b.x)/(u.x-v.x)) := by{
    field_simp
  }
  rw[this]
  exact complex_im_mul LR LS
}

/-"parallel_parallel" is just parallel_trans, so the last of those theorems is perpendicular_parallel (for completeness' sake)-/

lemma perp_parallel(L : Line) {R S : Line}(LR: Perpendicular L R)(LS : Parallel L S): Perpendicular R S := by{
  apply perp_symm
  exact parallel_perp L LS LR
}

/-Now we proof that for any line and point, there is a unique line going throught he point perpendicular to the first line.
We use some tricks:

-Every line can be written as Lien_through two point
-For Line_through we can get an explicit formula for the complex foot
-Uniqueness follows from the stuff we've discussed above and parallel_def

Due to that, we have to proceed slowly: -/


--oh god i messed up ooops still gotta turn by 90 deg, this is very ugly lol
lemma sub_neq_zero_point(a b p : Point)(ab : a ≠ b): p ≠ Point.mk (({re := 0, im := 1}:ℂ)*(a.x-b.x)+p.x) := by{
  contrapose ab
  simp at *
  obtain ⟨a1,a2⟩ := a
  obtain ⟨b1,b2⟩ := b
  obtain ⟨p1,p2⟩ := p
  ext
  simp at *
  constructor
  linarith
  linarith
}
def perp_line_points (a b p : Point)(ab: a ≠ b) : Line :=
  Line_through (sub_neq_zero_point a b p ab)

lemma perp_line_points_is_perp(a b p : Point)(ab : a ≠ b): Perpendicular (Line_through ab) (perp_line_points a b p ab) := by{
  unfold perp_line_points
  apply (perp_quot ab (sub_neq_zero_point a b p ab)).2
  unfold perp_points
  obtain ⟨a1,a2⟩ := a
  obtain ⟨b1,b2⟩ := b
  simp at *
  have : -({ re := b2 - a2, im := a1 - b1 }:ℂ) = ({re := a2-b2, im := b1-a1}:ℂ) := by{
    rw [@neg_eq_iff_add_eq_zero]
    simp
    rfl
  }
  rw[this]
  simp
  ring_nf
  tauto
}

lemma lies_on_perp_line_points (a b p)(ab: a ≠ b): Lies_on p (perp_line_points a b p ab) := by{
  unfold perp_line_points
  exact line_through_mem_left (sub_neq_zero_point a b p ab)
}

lemma ex_perp_through_point(L : Line)(p : Point): ∃(R: Line), Perpendicular L R ∧ Lies_on p R := by{
  obtain ⟨a,b,ab,ah,bh⟩ := ex_points_on_line L
  have hL: L = Line_through ab := by{
    apply line_through_unique
    tauto
  }
  rw[hL]
  clear L ah bh hL
  use perp_line_points a b p ab
  constructor
  exact perp_line_points_is_perp a b p ab
  exact lies_on_perp_line_points a b p ab
}

/-Similar as with parallel_through  beforewe can now define Perpendicular through:-/
/-(Note: you could call this "Altitude" if you want to, we will reserve this word for later usage in triangles though)-/

def perp_through : Line → Point → Line :=
  fun L p ↦ (ex_perp_through_point L p).choose

/-This really has the properties we want:-/

lemma perp_through_is_perp_through (L : Line)(p : Point): Perpendicular L (perp_through L p) ∧ Lies_on p (perp_through L p) := by{
  unfold perp_through
  exact Exists.choose_spec (ex_perp_through_point L p)
}

lemma perp_through_is_perp (L : Line)(p : Point): Perpendicular L (perp_through L p) := by{
  exact (perp_through_is_perp_through L p).1
}

lemma point_lies_on_perp_through (L : Line)(p : Point): Lies_on p (perp_through L p) := by{
  exact (perp_through_is_perp_through L p).2
}

/-With some trickery we now get that this is unique:-/
theorem perp_through_unique (L R : Line)(p : Point)(h: Perpendicular L R ∧ Lies_on p R): R = perp_through L p := by{
  have hR: Parallel R (perp_through L p) := by{
    refine perp_perp L ?_ ?_
    exact h.1
    exact perp_through_is_perp L p
  }
  apply (parallel_def R (perp_through L p)).1 at hR
  obtain ⟨h1,h2⟩ := h
  obtain h|h := hR
  exfalso
  have hp: p ∈ R.range ∩ (perp_through L p).range := by{
    constructor
    unfold Lies_on at h2
    assumption

    have : Lies_on p (perp_through L p) := by{exact point_lies_on_perp_through L p}
    unfold Lies_on at this
    assumption
  }
  rw[h] at hp
  contradiction

  ext
  rw[h]
}

/-The perpendicular through any point is never parallel, which we will use afterwards:-/
lemma perp_through_not_parallel(L : Line)(p : Point): ¬ Parallel L (perp_through L p) := by{
  apply perp_not_parallel L (perp_through L p)
  exact perp_through_is_perp L p
}

/-We define the foot of a point on a line as the intersection of the line and the perpendicular through the point -/

def foot : Point → Line → Point :=
  fun p L ↦ Intersection (perp_through_not_parallel L p)

/-foot really satisfies what we want: It is on L and perp_through L p:-/

lemma foot_on_line(L : Line)(p : Point): Lies_on (foot p L) L := by{
  unfold foot
  exact (intersection_mem (perp_through_not_parallel L p)).1
}

lemma foot_on_perp(L : Line)(p : Point): Lies_on (foot p L) (perp_through L p) := by{
  unfold foot
  exact (intersection_mem (perp_through_not_parallel L p)).2
}

/-It is unique (this is just uniqueness of intersection):-/

lemma foot_unique{L : Line}{p q : Point}(h: Lies_on q L ∧ Lies_on q (perp_through L p)): q = foot p L := by{
  unfold foot
  exact intersection_unique (perp_through_not_parallel L p) h
}

/-If p lies on L, foot p L = p:-/
lemma foot_point_on_line{L : Line}{p : Point}(h : Lies_on p L): foot p L = p := by{
  symm
  apply foot_unique
  constructor
  · assumption
  exact point_lies_on_perp_through L p
}

/-otherwise this is not the case:-/
lemma foot_point_not_on_line{L : Line}{p : Point}(h : ¬Lies_on p L): foot p L ≠ p := by{
  contrapose h
  simp at *
  rw[← h]
  exact foot_on_line L p
}

/-Therefore the perpendicular line is the line_through p and foot p L:-/

lemma foot_line_through{L : Line}{p : Point}(h: ¬Lies_on p L): Line_through (foot_point_not_on_line h) = perp_through L p := by{
  symm
  apply line_through_unique
  constructor
  exact foot_on_perp L p
  exact point_lies_on_perp_through L p
}

/-The foot is consant in the following sense:-/

lemma foot_point_on_perp{L : Line}{a b : Point}(h: Lies_on b (perp_through L a)): foot b L = foot a L := by{
  apply foot_unique
  constructor
  exact foot_on_line L b

  have p: perp_through L b = perp_through L a := by{
    symm
    apply perp_through_unique
    constructor
    exact perp_through_is_perp L a
    assumption
  }
  rw[← p]
  exact foot_on_perp L b
}

lemma foot_perp_through(L : Line)(p : Point): perp_through L (foot p L) = perp_through L p := by{
  have par: Parallel (perp_through L (foot p L)) (perp_through L p) := by{
    apply perp_perp L
    exact perp_through_is_perp L (foot p L)
    exact perp_through_is_perp L p
  }
  apply (parallel_def (perp_through L (foot p L)) (perp_through L p)).1 at par
  obtain h|h := par
  exfalso
  have footbad: (foot p L) ∈ (perp_through L (foot p L)).range ∩ (perp_through L p).range := by{
    suffices : Lies_on (foot p L) (perp_through L p) ∧ Lies_on (foot p L) (perp_through L (foot p L))
    unfold Lies_on at this
    tauto

    constructor
    exact foot_on_perp L p
    exact point_lies_on_perp_through L (foot p L)
  }
  rw[h] at footbad
  tauto

  ext
  rw[h]
}

/-We finish off with a confusing but occassionally useful lemma:-/

lemma foot_perp_through2{a b : Point}(ab : a ≠ b): foot a (perp_through (Line_through ab) b) = b := by{
  symm
  apply foot_unique
  constructor
  exact point_lies_on_perp_through (Line_through ab) b
  have : perp_through (perp_through (Line_through ab) b) a = Line_through ab := by{
    symm
    apply perp_through_unique
    constructor
    apply perp_symm
    exact perp_through_is_perp (Line_through ab) b
    exact line_through_mem_left ab
  }
  rw[this]
  exact line_through_mem_right ab
}

/-and a nice lemma about perpendiular points with foot:-/
lemma perp_points_foot{L : Line}(a p : Point)(ha: Lies_on a L): perp_points a (foot p L) p (foot p L) := by{
  apply perp_all (perp_through_is_perp L p) ha (foot_on_line L p) (point_lies_on_perp_through L p) (foot_on_perp L p)
}

/-Similar to intersections, there is an explicit formula for foots on lines.
Once again, I dont recommend this fo general usage though.-/
/-The proof is basically just using perp_through_unique and brute force calculations, nothing particular to add-/

lemma foot_explicit(p : Point){a b : Point}(ab : a ≠ b): foot p (Line_through ab) = Point.mk (((conj a.x - conj b.x)*(p.x)+(a.x-b.x)*(conj p.x)+(conj a.x)*(b.x)-(a.x)*(conj b.x))/(2*(conj a.x - conj b.x))) := by{
  symm
  let n := (conj a.x - conj b.x)*(p.x)+(a.x-b.x)*(conj p.x)+(conj a.x)*(b.x)-(a.x)*(conj b.x)
  let m := 2*(conj a.x - conj b.x)
  have ndef: n = (conj a.x - conj b.x)*(p.x)+(a.x-b.x)*(conj p.x)+(conj a.x)*(b.x)-(a.x)*(conj b.x) := rfl
  have mdef : m = 2*(conj a.x - conj b.x) := rfl
  have s1: m ≠ 0 := by{
    unfold m
    simp
    suffices : a.x - b.x ≠ (0:ℂ)
    contrapose this
    · simp at *
      rw[← conj_sub] at this
      rw[← conj_twice (a.x-b.x)]
      rw[this]
      unfold conj
      simp
    exact sub_neq_zero ab
  }
  have s2: conj m ≠ 0 := by{
    contrapose s1
    simp at *
    rw[← conj_twice m]
    rw[s1]
    unfold conj
    simp
  }
  rw[← ndef, ← mdef]
  apply foot_unique
  constructor
  unfold Lies_on Line_through colinear
  simp
  suffices : detproper a.x (conj a.x) 1 b.x (conj b.x) 1 (n/m) (conj n / conj m) 1 = 0
  · rw[det_detproper a b ({x := n / m}: Point)]
    simp
    rw[this]
    simp
  unfold detproper
  simp
  field_simp
  unfold m
  simp
  have : conj 2 = 2 := by{
    unfold conj
    have : (2:ℂ)= ({re := 2, im := 0}:ℂ) :=by{rfl}
    rw[this]
    calc
      (starRingEnd ℂ) { re := 2, im := 0 } = { re := 2, im := -0 } := by{rfl}
        _= {re := 2, im := 0} := by{ring_nf}

  }
  rw[this]
  unfold n
  simp
  ring

  have : Line_through (sub_neq_zero_point a b p ab) = perp_through (Line_through ab) p := by{
    apply perp_through_unique
    constructor
    exact perp_line_points_is_perp a b p ab

    unfold Line_through Lies_on
    simp
    apply colinear_self
    tauto
  }
  rw[← this]
  clear this
  unfold Lies_on Line_through
  simp
  unfold colinear
  rw[det_detproper]
  suffices : (detproper p.x (conj p.x) 1 ({ x := { re := 0, im := 1 } * (a.x - b.x) + p.x } : Point).x
      (conj ({ x := { re := 0, im := 1 } * (a.x - b.x) + p.x } : Point).x) 1 ({ x := n / m }: Point).x (conj ({ x := n / m } : Point).x) 1) = 0
  · rw[this]
    rfl
  unfold detproper
  simp
  field_simp
  have : conj { re := 0, im := 1 } = {re := 0, im := -1} := by{
    unfold conj
    rfl
  }
  rw[this]
  have : conj 2 = 2 := by{
    unfold conj
    have : (2:ℂ)= ({re := 2, im := 0}:ℂ) :=by{rfl}
    rw[this]
    calc
      (starRingEnd ℂ) { re := 2, im := 0 } = { re := 2, im := -0 } := by{rfl}
        _= {re := 2, im := 0} := by{ring_nf}

  }
  unfold n m
  simp
  rw[this]
  clear this s1 s2
  obtain ⟨a1,a2⟩ := a
  have : conj ({ x := { re := a1, im := a2 }} : Point).x = ({ re := a1, im := -a2} : ℂ) := by{
    unfold conj
    simp
    rfl
  }
  rw[this]
  clear this
  simp
  obtain ⟨b1,b2⟩ := b
  have : conj ({ x := { re := b1, im := b2 }} : Point).x = ({ re := b1, im := -b2} : ℂ) := by{
    unfold conj
    simp
    rfl
  }
  rw[this]
  clear this
  simp
  obtain ⟨p1,p2⟩ := p
  have : conj ({ x := { re := p1, im := p2 }} : Point).x = ({ re := p1, im := -p2} : ℂ) := by{
    unfold conj
    simp
    rfl
  }
  rw[this]
  clear this
  simp
  have {x y : ℝ}: 2*({ re := x, im := y}: ℂ)= ({ re := 2*x, im := 2*y}:ℂ) := by{
    have: 2 = ({ re := 2, im := 0} : ℂ) := by{
      rfl
    }
    rw[this]
    simp
  }
  repeat
    rw[this]
    simp
  ring_nf
  rfl
  }

/-This is pretty much all there is to say about perpendicular lines in general, so in the next file we
focus on triangles (3 noncolinear points) and perpendicular lines, in particular the orthocenter!-/

/-This motivates following definition:-/

def point_line_abs : Point → Line → ℝ :=
  fun p L ↦ point_abs p (foot p L)

/-This is nonneg:-/

lemma point_line_abs_nonneg{p : Point}{L : Line}: 0 ≤ point_line_abs p L := by{
  unfold point_line_abs
  exact point_abs_pos p (foot p L)
}

/-And its zero iff p lies on the line:-/

lemma point_line_abs_zero_iff{p : Point}{L : Line} : point_line_abs p L = 0 ↔ Lies_on p L := by{
  constructor
  intro h
  unfold point_line_abs at h
  have hp: p = foot p L := by{exact abs_zero_imp_same p (foot p L) h}
  rw[hp]
  exact foot_on_line L p

  intro h
  have hp: p = foot p L := by{
    exact Eq.symm (foot_point_on_line h)
  }
  unfold point_line_abs
  nth_rw 1[hp, point_abs_self (foot p L)]
}
