/- It is fine to import all of Mathlib in your project.
This might make the loading time of a file a bit longer. If you want a good chunk of Mathlib, but not everything, you can `import Mathlib.Tactic` and then add more imports as necessary. -/
import Mathlib

/- open namespaces that you use to shorten names and enable notation. -/
open Function Set Classical

/- recommended whenever you define anything new. -/
noncomputable section

/- Now write definitions and theorems. -/


/-The following is an approach to two dimensional euclidean geometry in a rather unorthodox way
It defines everything via complex numbers in a similar fashion how they are commonly used in math olympiads.
This has the upside of giving us many things almost automatically and let us get to harder theorems rather quickly.
Points are just complex numbers.
Lines and Circles are not structures of their own, but just sets in ℂ (actually a function from two points into Set ℂ).
This makes some stuff a bit annoying, in particular special cases when points fall together.
Similarly, angles are defined in between points and not lines.

The obvious downside of this approach is that is doesn't generalise at all.
I do however believe, it is the most sensible way to deal with classical two dimensional euclidean geometry as formal axioms do not pose
any problem with this approach at all.

The way colinearity is defined may be confusing at first, however it is the same as the usually motion, as will be seen later (in particual herons formula should "justify" it sufficiently)
The other definitions should more or less come natural.

The end goal of this is to prove Feuerbach's theorem.
-/


@[ext] structure Point where
  x : ℂ

/- It will be convinient to multiply and add Points-/

def pmul : Point → Point → Point :=
  fun a b ↦ Point.mk (a.x * b.x)

def padd : Point → Point → Point :=
  fun a b ↦ Point.mk (a.x+b.x)

/-Also midpoints are neat-/
def pmidpoint : Point → Point → Point :=
  fun a b ↦ Point.mk ((a.x+b.x)/2)

def conj : ℂ → ℂ :=
  fun z ↦ (starRingEnd ℂ) z

def p_scal_mul : ℂ → Point → Point :=
  fun c a ↦ Point.mk (c*a.x)

lemma conj_add (x:ℂ) (y:ℂ) : conj (x+y) = conj x + conj y := by{
  unfold conj
  exact RingHom.map_add (starRingEnd ℂ) x y
}

lemma conj_mul' (x:ℂ) (y:ℂ) : conj (x*y) = (conj x) * (conj y) := by{
  unfold conj
  exact RingHom.map_mul (starRingEnd ℂ) x y
}

/- Here we introduce the distance between two complex numbers and show the axioms of a metric-/
def point_abs : Point → Point → ℝ :=
  fun a b ↦ Complex.abs (a.x - b.x)

lemma abs_zero_imp_same (a a' : Point)(h: point_abs a a' = 0): a=a' := by{
  unfold point_abs at h
  ext
  have : a.x-a'.x = 0 := by exact (AbsoluteValue.eq_zero Complex.abs).mp h
  calc
    a.x = a.x - a'.x + a'.x := by ring
      _= 0+a'.x := by rw[this]
      _=a'.x := by ring
}

lemma point_abs_pos (a b : Point): 0 ≤ point_abs a b := by{
  unfold point_abs
  exact AbsoluteValue.nonneg Complex.abs (a.x - b.x)
}

lemma point_abs_self (a : Point) : point_abs a a = 0 := by{
  unfold point_abs
  ring
  exact AbsoluteValue.map_zero Complex.abs
}

lemma point_abs_symm (a b : Point) : point_abs a b = point_abs b a := by{
  unfold point_abs
  exact AbsoluteValue.map_sub Complex.abs a.x b.x
}

lemma point_abs_triangle (a b c : Point) : point_abs a b + point_abs b c ≥ point_abs a c := by{
  unfold point_abs
  calc
    Complex.abs (a.x - b.x) + Complex.abs (b.x - c.x) ≥ Complex.abs ((a.x-b.x) + (b.x-c.x)) := by exact AbsoluteValue.add_le Complex.abs (a.x - b.x) (b.x - c.x)
      _= Complex.abs (a.x-c.x) := by ring
}

def pconj : Point → Point :=
  fun a ↦ Point.mk (conj a.x)

def det : Point → Point → Point → ℝ :=
  fun a b c ↦ (a.x * (conj b.x) + c.x * (conj a.x) + b.x * (conj c.x) - a.x * (conj c.x) - c.x * (conj b.x) - b.x * (conj a.x)).im

/- Notice: taking the imaginary part here is by no means necessary. To make this more compaitble to areas which are introduced later
for which it is in turn useful to use real numbers for similar traingles,we take the imaginary part here.
In fact the real part of above expression is always 0:-/

example (a b c : ℂ): (a * (conj b) + c * (conj a) + b * (conj c) - a * (conj c) - c * (conj b) - b * (conj a)).re = 0 := by{
  unfold conj
  obtain ⟨x1,x2⟩ := a
  obtain ⟨y1,y2⟩ := b
  obtain ⟨z1,z2⟩ := c
  simp
  ring
}

lemma detperm1 (a b c : Point) : det a b c = -1* (det b a c) := by{unfold det;ring}

lemma detperm2 (a b c : Point) : det a b c = -1* det c b a := by{unfold det;ring}

lemma det_self(a b c : Point)(h: a=b ∨ b=c ∨ a=c): det a b c = 0 := by{
  obtain h|h|h := h
  repeat
    rw[h]
    unfold det
    ring
}

def linear (a b c : Point) : Prop :=
  det a b c = 0

def Nonlinear (a b c : Point) : Prop :=
  ¬linear a b c

/- This notion of colinearity is the same as the usual one:-/

theorem linear_def {a b c : Point}: (Nonlinear a b c) ↔ (∀ x y z : ℝ, (↑x * a.x + ↑y * b.x + ↑z * c.x = 0) → (x=0 ∧ y=0 ∧ z=0)) := by{
  sorry
}

lemma linear_ex {a b c : Point}(h: linear a b c) : ∃ x y z : ℝ, ¬(x=0 ∧ y=0 ∧ z=0) ∧ (↑x * a.x + ↑y * b.x + ↑z * c.x = 0) :=by{
  by_contra p
  push_neg at p
  have : Nonlinear a b c := by{
    apply linear_def.2
    intro x y z h
    specialize p x y z
    tauto
  }
  tauto
}

--lemma linear_alt (a:Point)(b: Point)(c:Point)(h: a≠ b ∧ b≠ c ∧ c≠ a): linear a b c ⇔ (a.x-b.x)/()

lemma linear_trans (a b c d : Point)(h: linear a b c) (h': linear a b d)(nab: a ≠ b):  linear b c d := by{
  unfold linear at *
  unfold det at *
  unfold conj at *
  obtain ⟨x,y⟩ := a
  obtain ⟨z,v⟩ := b
  obtain ⟨n,m⟩ := c
  obtain ⟨k,r⟩ := d
  simp at *
  congr
  sorry
}

lemma linear_trans_test (a b c d : Point)(h: linear a b c) (h': linear a b d)(nab: a ≠ b):  linear b c d := by{
  contrapose nab
  have bcd: Nonlinear b c d := by{exact nab}
  clear nab
  push_neg
  apply linear_def.1 at bcd
  apply linear_ex at h
  apply linear_ex at h'
  obtain ⟨x1,y1,z1,⟨h1,h2⟩⟩ := h
  obtain ⟨x2,y2,z2,⟨h'1,h'2⟩⟩ := h'
  simp at *
  sorry
}

lemma linear_perm1 (a b c : Point)(h: linear a b c) : linear b a c := by{
  unfold linear at *
  rw[detperm1,h]
  ring
}

lemma linear_perm2 (a b c : Point)(h: linear a b c) : linear c b a := by{
  unfold linear at *
  rw[detperm2,h]
  ring
}

lemma linear_self(a b c : Point)(h: a=b ∨ b=c ∨ a=c): linear a b c := by{
  unfold linear
  exact det_self a b c h
}

def Line : Point → Point → Set Point :=
  fun a b ↦ {c | linear a b c}

lemma self_in_line (a b : Point): a ∈ Line a b ∧ b ∈ Line a b := by{
  unfold Line
  simp
  constructor
  · apply linear_self
    right
    right
    rfl
  · apply linear_self
    right
    left
    rfl
}

lemma mem_line_colinear (a b c : Point)(h : c ∈ Line a b) : linear a b c := by{
  unfold Line at h
  simp at h
  assumption
}

lemma same_line_imp_colinear{a b c : Point}(h : Line a b = Line b c) : linear a b c := by{
  have : c ∈ Line a b := by{
    rw[h]
    exact (self_in_line b c).2
  }
  exact mem_line_colinear a b c this
}
/-Line generats by itself-/
lemma line_made_by_mems(a b c d : Point)(h: a ≠ b)(h': c ≠ d)(hc : c ∈ Line a b)(hd : d ∈ Line a b): Line c d = Line a b := by{
  ext x
  constructor
  · intro u
    simp [Line] at *
    have bcd: linear b c d := by exact linear_trans a b c d hc hd h
    apply linear_perm2 at bcd
    apply linear_perm1 at bcd
    have bdx: linear d b x := by exact linear_trans c d b x bcd u h'
    apply linear_perm2 at hd
    by_cases p: d=b
    rw[p] at u
    rw[p] at h'
    clear bdx bcd hd
    apply linear_perm2 at hc
    apply linear_perm1
    exact linear_trans c b a x hc u h'

    apply linear_perm1
    exact linear_trans d b a x hd bdx p

  · unfold Line at *
    simp at *
    intro abx
    have bcd: linear b c d := by exact linear_trans a b c d hc hd h
    have bcx: linear b c x := by exact linear_trans a b c x hc abx h
    by_cases p: b = c
    clear bcd bcx hc
    rw[← p]
    rw[← p] at h'
    exact linear_trans a b d x hd abx h

    exact linear_trans b c d x bcd bcx p
  }


/- Line parallel to line ab thorugh line c-/
def parallel_line : Point → Point → Point → Set Point :=
  fun a b c ↦ Line c (Point.mk (c.x + a.x - b.x))

def Circle1 : Point → ℝ → Set Point :=
  fun z R ↦ {a : Point | point_abs z a = R}

lemma circle_of_neg_rad (z : Point)(R : ℝ)(h : R < 0): Circle1 z R = ∅ := by{
  unfold Circle1
  ext x
  constructor
  intro hx
  simp at *
  have : 0 ≤ point_abs z x := by exact point_abs_pos z x
  linarith

  intro h
  simp at h
}

lemma circle_diameter (z a b : Point)(R : ℝ) (ha : a ∈ Circle1 z R) (hb : b ∈ Circle1 z R) : point_abs a b ≤ 2*R := by{
  unfold Circle1 at *
  simp at *
  calc
    point_abs a b ≤ point_abs a z + point_abs z b := by exact point_abs_triangle a z b
      _= point_abs z a + point_abs z b := by rw[point_abs_symm]
      _= R + R := by rw[ha,hb]
      _=2*R := by ring
}

/- two short useful lemmas for determining uniqueness of circles-/
lemma upmem_circle (z : Point)(R : ℝ)(hR : 0≤ R): (Point.mk (z.x + R) ∈ Circle1 z R) := by{
  unfold Circle1
  unfold point_abs
  simp
  assumption
}

lemma downmem_circle (z : Point)(R : ℝ)(hR : 0≤ R): (Point.mk (z.x - R) ∈ Circle1 z R) := by{
  unfold Circle1
  unfold point_abs
  simp
  assumption
}

lemma circle_of_pos_rad_nonempty (z : Point)(R : ℝ)(h : 0≤ R): Set.Nonempty (Circle1 z R) := by{
  use Point.mk (z.x + R)
  exact upmem_circle z R h
}

/- Now a surprisingly difficult proof circles have unique cirumcenters and radii-/

theorem circle_unique (z z' : Point)(R R' : ℝ)(h : Circle1 z R = Circle1 z' R')(h' : R≥ 0): z = z' ∧  R = R' := by{
  by_cases p: R'<0
  have : Circle1 z' R' = ∅ := by{
    exact circle_of_neg_rad z' R' p
  }
  rw[this] at h
  have : Set.Nonempty (Circle1 z R) := by{exact circle_of_pos_rad_nonempty z R h'}
  apply Set.nonempty_iff_ne_empty.1 at this
  tauto

  simp at p
  have same_rad : R = R' := by{
    apply le_antisymm
    · let uz := Point.mk (z.x + R)
      let dz := Point.mk (z.x - R)
      have u_mem : uz ∈ Circle1 z R := by exact upmem_circle z R h'
      have d_mem : dz ∈ Circle1 z R := by exact downmem_circle z R h'
      have : point_abs uz dz ≤ 2* R' := by{
        rw[h] at u_mem
        rw[h] at d_mem
        exact circle_diameter z' uz dz R' u_mem d_mem
      }
      have : point_abs uz dz = 2*R := by{
        unfold point_abs uz dz
        simp
        calc
          Complex.abs (↑R + ↑R) = Complex.abs (2* ↑R) := by{norm_cast; ring_nf}
          _= Complex.abs 2 * Complex.abs R := by rw [@AbsoluteValue.map_mul]
          _= 2 * Complex.abs R := by rw [Complex.abs_two]
          _= 2 * R := by{rw [Complex.abs_of_nonneg h']}
      }
      linarith

    · let uz' := Point.mk (z'.x + R')
      let dz' := Point.mk (z'.x - R')
      have u_mem : uz' ∈ Circle1 z' R' := by exact upmem_circle z' R' p
      have d_mem : dz' ∈ Circle1 z' R' := by exact downmem_circle z' R' p
      have : point_abs uz' dz' ≤ 2* R := by{
        rw[← h] at u_mem
        rw[← h] at d_mem
        exact circle_diameter z uz' dz' R u_mem d_mem
      }
      have : point_abs uz' dz' = 2*R' := by{
        unfold point_abs uz' dz'
        simp
        calc
          Complex.abs (↑R' + ↑R') = Complex.abs (2* ↑R') := by{norm_cast; ring_nf}
          _= Complex.abs 2 * Complex.abs R' := by rw [@AbsoluteValue.map_mul]
          _= 2 * Complex.abs R' := by rw [Complex.abs_two]
          _= 2 * R' := by{rw [Complex.abs_of_nonneg p]}
      }
      linarith

  }
  constructor
  rw[← same_rad] at h
  by_cases p : z=z'
  · assumption
  let t := (R / Complex.abs (z.x-z'.x))* (z.x-z'.x)
  let P := Point.mk (z.x + t)
  have : P ∈ Circle1 z R := by{
    have : z.x-z'.x ≠ 0 := by{
      have : z.x ≠ z'.x := by{
          by_contra u
          have : z=z' :=by{
            ext
            assumption
          }
          contradiction
      }
      by_contra i
      have : z.x = z'.x := by
        calc
          z.x = z.x - 0 := by ring
            _= z.x - (z.x - z'.x) := by rw[i]
            _=z'.x := by ring
      contradiction
    }
    have : Complex.abs (z.x - z'.x) ≠ 0 := by{
      exact (AbsoluteValue.ne_zero_iff Complex.abs).mpr this
    }
    unfold P
    unfold Circle1
    simp
    unfold point_abs
    simp
    unfold t
    simp
    calc
      |R| / Complex.abs (z.x - z'.x) * Complex.abs (z.x - z'.x) = |R| := by rw [div_mul_cancel₀ |R|
          this]
        _= R := by exact abs_of_nonneg h'
  }
  rw[h] at this
  unfold Circle1 at this
  unfold point_abs at this
  simp at this
  unfold t at this
  symm at this
  sorry

  assumption
}

lemma ex_circumcircle {a b c : Point} (h : Nonlinear a b c) :
  ∃! z : (Point × ℝ), {a,b,c} ⊆ Circle1 z.1 z.2 := by{
    sorry
  }


/-def Circumcircle (a b c : Point) : Set Point :=
  if h : linear a b c then
    if a = b ∨ b = c ∨ c = a then ∅
    else Line a b
  sorry
  --else by
    --{let z := ex_circumcircle a b c (by { unfold Nonlinear; assumption }) sorry --???? Circle1 z.1 z.2
-/

/- Natural definition for tangential-/
def tangential (s v : Set Point) : Prop :=
  Set.encard (s ∩ v) = 1

/- We actually wont use the following structure too much, but it is nice to keep it in mind-/

@[ext] structure Triangle where
  a : Point
  b : Point
  c : Point
  notline : Nonlinear a b c

/- We will use the lenghts of sides of triangles often-/

def tri_ab: Triangle → ℝ :=
  fun T ↦ (point_abs T.a T.b)

def tri_bc: Triangle → ℝ :=
  fun T ↦ (point_abs T.b T.c)

def tri_ca: Triangle → ℝ :=
  fun T ↦ (point_abs T.c T.a)

/- We now introduce Area, first for points in general, then for our triangle structure-/
def area_points : Point → Point → Point → ℝ :=
  fun a b c ↦ -1/4  * det a b c

def area_tri : Triangle → ℂ :=
  fun T ↦ area_points T.a T.b T.c

/- It is very important that the above expression is the *signed* area, not the abosulte value. So it can take negative values-/

lemma area_zero_iff (a b c : Point): area_points a b c = 0 ↔ linear a b c := by{
  unfold area_points
  unfold linear
  constructor
  · intro h
    linarith
  · intro h
    linarith
}

/- While an definitional equality to the standard measure is left a fever dream, we will show equivalence of this definition to others soon.
First though, a small sanity check:-/

example : area_points (Point.mk (0:ℂ)) (Point.mk (1:ℂ)) (Point.mk (Complex.I :ℂ)) = (1/2 : ℝ) := by{
  unfold area_points
  unfold det
  unfold conj
  simp
  ring
}

/- A classical result of euclidean geometry is the so called heron formula:-/

def perimiter_points : Point → Point → Point → ℝ :=
  fun a b c ↦ point_abs a b + point_abs b c + point_abs c a

/- For reasons of compactness we introduce an unnecessary variable here-/

theorem heron{a b c : Point}{s : ℝ}(h: s = 1/2 * (perimiter_points a b c)) : |(area_points a b c)| = Real.sqrt (s*(s - (point_abs a b))*(s - (point_abs b c))*(s - point_abs c a)) := by{
  refine Eq.symm ((fun {x y} hx hy ↦ (Real.sqrt_eq_iff_mul_self_eq hx hy).mpr) ?hx ?hy ?_)
  sorry
  exact abs_nonneg (area_points a b c)
  sorry
}

/- Now some stuff about adding the areas of triangles-/
 lemma area_add (a b c x : Point): area_points a b c = area_points a b x + area_points x b c + area_points a x c := by{
  unfold area_points
  have : det a b c = det a b x + det x b c + det a x c := by
    unfold det
    unfold conj
    obtain ⟨a1,a2⟩ := a
    obtain ⟨b1,b2⟩ := b
    obtain ⟨c1,c2⟩ := c
    obtain ⟨x1,x2⟩ := x
    simp
    ring
  linarith
 }

/- An important speical case is when X lies on the side of a triangle-/

lemma area_add_side (a b c x : Point)(h : x ∈ Line b c): area_points a b c = area_points a b x + area_points a x c := by{
  rw[area_add a b c x]
  have : area_points x b c = 0 := by{
    refine (area_zero_iff x b c).mpr ?_
    unfold Line at h
    simp at h
    apply linear_perm2
    apply linear_perm1
    assumption
  }
  linarith
}

/-An intermediate goal is to prove Ceva's theorem. For this we first need a definition for Lines being copunctal,
lenght proportions and how they realtie to areas proportions-/

def Copunctal (a d b e c f : Point) : Prop :=
  Set.encard (Line a d ∩ Line b e ∩ Line c f) = 1


/- A short notion for a point being in between other:-/

def in_between (a b x : Point) : Prop :=
  point_abs  a x + point_abs x b = point_abs a b

/-A sweet consequence is that this can only happen when x already lies on the line between a b-/

lemma in_between_imp_colinear {a b x : Point} (h: in_between a b x) : linear a b x := by{
  sorry
}


--def signed_quotient (a b c d : Point) : ℝ :=
  --if Nonlinear a b c ∨ Nonlinear a

  /-def Circumcircle (a b c : Point) : Set Point :=
  if h : linear a b c then
    if a = b ∨ b = c ∨ c = a then ∅
    else Line a b
  sorry
  --else by
    --{let z := ex_circumcircle a b c (by { unfold Nonlinear; assumption }) sorry --???? Circle1 z.1 z.2
-/

/- A crucial definition in planar geometry are similar triangles:-/

def Similar (T Q : Triangle) : Prop :=
  ∃z : ℂ, (z* T.a.x = Q.a.x) ∧ (z* T.b.x = Q.b.x) ∧ (z* T.c.x = Q.c.x)

/-Note that the scaling factor cant be 0:-/
lemma similar_neq_zero {T Q : Triangle}(z : ℂ)(zh : (z* T.a.x = Q.a.x) ∧ (z* T.b.x = Q.b.x) ∧ (z* T.c.x = Q.c.x)) : z≠ 0 := by{
  by_contra p
  rw[p] at zh
  simp at zh
  obtain ⟨a,b,c, q⟩ := Q
  simp at zh
  unfold Nonlinear at q
  unfold linear at q
  unfold det at q
  unfold conj at q
  push_neg at q
  obtain ⟨zh1,zh2,zh3⟩ := zh
  rw[← zh1 ,← zh2,← zh3] at q
  simp at q
}

/-Lets show being similar is an equivalence relation:-/

lemma similar_self (T : Triangle) : Similar T T := by{
  use 1
  simp
}

lemma similar_symm (T Q : Triangle) (h : Similar T Q) : Similar Q T := by{
  obtain ⟨z,zh⟩ := h
  have : z ≠ 0 := by{
    exact similar_neq_zero T Q z zh
    }
  use z⁻¹
  obtain ⟨zh1,zh2,zh3⟩ := zh
  rw[← zh1, ← zh2, ← zh3]
  field_simp [this]
}

lemma similar_trans {T Q R: Triangle} (h : Similar T Q) (h': Similar Q R): Similar T R := by{
  obtain ⟨z,zh⟩ := h
  obtain ⟨v, vh⟩ := h'
  use v*z
  obtain ⟨zh1,zh2,zh3⟩ := zh
  obtain ⟨vh1,vh2,vh3⟩ := vh
  repeat
    rw[mul_assoc]
  rw[zh1, zh2, zh3, vh1, vh2, vh3]
  tauto
}

/-To obtain the scaling factor we define a function for arbitrary triangles. This works as at there has to be at least one "pair" where eahc coordinates are nonzero-/

def scale_factor : Triangle → Triangle → ℝ :=
  fun T Q ↦ max (max (Complex.abs (T.a.x / Q.a.x)) (Complex.abs (T.b.x / Q.b.x))) (Complex.abs (T.c.x / Q.c.x))

/-With this we can prove that lengths scale according to this:-/
lemma ab_scal (T Q : Triangle)(h : Similar T Q) : (tri_ab T) = (scale_factor T Q) * (tri_ab Q) := by{
  apply similar_symm at h
  unfold scale_factor
  unfold tri_ab
  unfold Similar at h
  unfold point_abs
  obtain ⟨z,⟨zh1,zh2,zh3⟩⟩ := h
  rw[← zh1]
  rw[← zh2]
  rw[← zh3]
  have this (i : ℂ) (h: ¬(i = 0)): Complex.abs z * Complex.abs i / Complex.abs i = Complex.abs z := by{field_simp [h]}
  by_cases u1: Q.a.x = 0
  rw[u1]
  simp
  by_cases u2: Q.b.x = 0
  right
  assumption
  left
  rw[this Q.b.x u2]
  by_cases u3: Q.c.x = 0
  rw[u3]
  simp

  rw[this Q.c.x u3]
  simp

  simp
  rw[this Q.a.x u1]
  by_cases u2: Q.b.x = 0
  rw[u2]
  simp
  left
  by_cases u3: Q.c.x = 0
  rw[u3]
  simp
  rw[this Q.c.x u3]
  simp

  rw[this Q.b.x u2]
  simp
  by_cases u3: Q.c.x = 0
  rw[u3]
  simp
  calc
    Complex.abs (z * Q.a.x - z * Q.b.x) = Complex.abs (z * (Q.a.x - Q.b.x)) := by ring
      _= (Complex.abs z) * Complex.abs (Q.a.x -Q.b.x) := by exact AbsoluteValue.map_mul Complex.abs z (Q.a.x - Q.b.x)
}
/-ommitted-/
