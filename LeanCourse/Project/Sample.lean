/- It is fine to import all of Mathlib in your project.
This might make the loading time of a file a bit longer. If you want a good chunk of Mathlib, but not everything, you can `import Mathlib.Tactic` and then add more imports as necessary. -/
import Mathlib

/- open namespaces that you use to shorten names and enable notation. -/
open Function Set Classical

/- recommended whenever you define anything new. -/
noncomputable section

/- Now write definitions and theorems. -/


/-The following is an approach to two dimensional euclidean geometry in a rather unorthodox way
It defines everything via complex numbers in a oldsimilar fashion how they are commonly used in math olympiads.
This has the upside of giving us many things almost automatically and let us get to harder theorems rather quickly.
Points are just complex numbers.
sLines and Circles are not structures of their own, but just sets in ℂ (actually a function from two points into Set ℂ).
This makes some stuff a bit annoying, in particular special cases when points fall together.
oldSimilarly, angles are defined in between points and not lines.

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
for which it is in turn useful to use real numbers for oldsimilar traingles,we take the imaginary part here.
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

lemma det_self(a b c : Point)(h: a=b ∨ b=c ∨ c=a): det a b c = 0 := by{
  obtain h|h|h := h
  repeat
    rw[h]
    unfold det
    ring
}

def colinear (a b c : Point) : Prop :=
  det a b c = 0

def Noncolinear (a b c : Point) : Prop :=
  ¬colinear a b c

/- This notion of colinearity is the same as the usual one:-/

theorem colinear_def {a b c : Point}: (Noncolinear a b c) ↔ (∀ x y z : ℝ, (↑x * a.x + ↑y * b.x + ↑z * c.x = 0) → (x=0 ∧ y=0 ∧ z=0)) := by{
  sorry
}

lemma colinear_ex {a b c : Point}(h: colinear a b c) : ∃ x y z : ℝ, ¬(x=0 ∧ y=0 ∧ z=0) ∧ (↑x * a.x + ↑y * b.x + ↑z * c.x = 0) :=by{
  by_contra p
  push_neg at p
  have : Noncolinear a b c := by{
    apply colinear_def.2
    intro x y z h
    specialize p x y z
    tauto
  }
  tauto
}

--lemma colinear_alt (a:Point)(b: Point)(c:Point)(h: a≠ b ∧ b≠ c ∧ c≠ a): colinear a b c ⇔ (a.x-b.x)/()

lemma colinear_trans (a b c d : Point)(h: colinear a b c) (h': colinear a b d)(nab: a ≠ b):  colinear b c d := by{
  unfold colinear at *
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

lemma colinear_trans_test (a b c d : Point)(h: colinear a b c) (h': colinear a b d)(nab: a ≠ b):  colinear b c d := by{
  contrapose nab
  have bcd: Noncolinear b c d := by{exact nab}
  clear nab
  push_neg
  apply colinear_def.1 at bcd
  apply colinear_ex at h
  apply colinear_ex at h'
  obtain ⟨x1,y1,z1,⟨h1,h2⟩⟩ := h
  obtain ⟨x2,y2,z2,⟨h'1,h'2⟩⟩ := h'
  simp at *
  sorry
}

lemma colinear_perm1 (a b c : Point)(h: colinear a b c) : colinear b a c := by{
  unfold colinear at *
  rw[detperm1,h]
  ring
}

lemma colinear_perm2 (a b c : Point)(h: colinear a b c) : colinear c b a := by{
  unfold colinear at *
  rw[detperm2,h]
  ring
}

lemma colinear_self(a b c : Point)(h: a=b ∨ b=c ∨ c=a): colinear a b c := by{
  unfold colinear
  exact det_self a b c h
}

/- Now we feel confident enough to define Lines:-/

@[ext] structure Line where
  range : Set Point
  span : ∃ a b : Point, a ≠ b ∧ range = {c : Point | colinear a b c}

--example (G: PythTriple) (k: ℕ): ∃G' : PythTriple, G'.x=k*G.x ∧ G'.y=k*G.y ∧ G'.z=k*G.z := by
--  have h': (k*G.x)^2+(k*G.y)^2 = (k*G.z)^2 := by exact ktrip G k
--  use PythTriple.mk (k*G.x) (k*G.y) (k*G.z) h'

lemma ex_unique_line_mem {a b : Point}(h: a ≠ b) : ∃! L : Line, a ∈ L.range ∧ b ∈ L.range := by{
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
  apply colinear_perm1
  apply colinear_perm2 at vab
  apply colinear_perm1 at vab
  apply colinear_perm2 at vab
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
  apply colinear_perm2 at dab
  apply colinear_perm1 at hx
  have ba: ¬b = a := by{exact fun a_1 ↦ h (id (Eq.symm a_1))}
  have adx : colinear a d x := by{exact colinear_trans b a d x dab hx ba}
  apply colinear_perm2 at ah
  apply colinear_perm1
  by_cases ad : a = d
  · rw[← ad]
    clear ah
    clear adx
    clear dab
    rw[← ad] at bh
    apply colinear_perm2 at bh
    exact colinear_trans b a c x bh hx ba
  · exact colinear_trans a d c x ah adx ad
  }

/- Lets define parallel lines. We say a line is parallel to itself, so we can get a nice equivalence relation-/
def Parallel(L R : Line) : Prop :=
  L.range ∩ R.range = ∅ ∨ L.range = R.range

lemma parallel_refl (L : Line) : Parallel L L := by{
  right
  rfl
}

lemma parallel_symm (L R : Line)(h : Parallel L R) : Parallel R L := by{
  unfold Parallel at *
  obtain h|h := h
  · left
    rw[Set.inter_comm]
    assumption
  · right
    symm
    assumption
}

lemma parallel_trans (L R S : Line)(LR : Parallel L R)(RS : Parallel R S) : Parallel LS := by{
  sorry
}

/- It will be convenient to lay parallels thorugh points:-/
lemma through_lemma (L : Line)(a : Point) : ∃

def parallel_through : Line → Point → Line :=
  fun L a ↦ sorry

/-This indeed is a parallel to the original Line:-/

lemma parallel_through_is_parallel (L : Line)(a : Point) : Parallel L (parallel_through L a) := by{
  sorry
}

/- We can now state and prove the parallel postulate:-/

theorem parallel_postulate (L : Line)(a : Point) : ∃! R : Line, a ∈ R.range ∧ Parallel L R := by{
  use parallel_through L a
  simp
  constructor
  constructor
  sorry
  exact parallel_through_is_parallel L a

  sorry
}

def sLine : Point → Point → Set Point :=
  fun a b ↦ {c | colinear a b c}

lemma self_in_line (a b : Point): a ∈ sLine a b ∧ b ∈ sLine a b := by{
  unfold sLine
  simp
  constructor
  · apply colinear_self
    right
    right
    rfl
  · apply colinear_self
    right
    left
    rfl
}

lemma mem_line_colinear (a b c : Point)(h : c ∈ sLine a b) : colinear a b c := by{
  unfold sLine at h
  simp at h
  assumption
}

lemma same_line_imp_colinear{a b c : Point}(h : sLine a b = sLine b c) : colinear a b c := by{
  have : c ∈ sLine a b := by{
    rw[h]
    exact (self_in_line b c).2
  }
  exact mem_line_colinear a b c this
}
/-sLine generats by itself-/
lemma line_made_by_mems(a b c d : Point)(h: a ≠ b)(h': c ≠ d)(hc : c ∈ sLine a b)(hd : d ∈ sLine a b): sLine c d = sLine a b := by{
  ext x
  constructor
  · intro u
    simp [sLine] at *
    have bcd: colinear b c d := by exact colinear_trans a b c d hc hd h
    apply colinear_perm2 at bcd
    apply colinear_perm1 at bcd
    have bdx: colinear d b x := by exact colinear_trans c d b x bcd u h'
    apply colinear_perm2 at hd
    by_cases p: d=b
    rw[p] at u
    rw[p] at h'
    clear bdx bcd hd
    apply colinear_perm2 at hc
    apply colinear_perm1
    exact colinear_trans c b a x hc u h'

    apply colinear_perm1
    exact colinear_trans d b a x hd bdx p

  · unfold sLine at *
    simp at *
    intro abx
    have bcd: colinear b c d := by exact colinear_trans a b c d hc hd h
    have bcx: colinear b c x := by exact colinear_trans a b c x hc abx h
    by_cases p: b = c
    clear bcd bcx hc
    rw[← p]
    rw[← p] at h'
    exact colinear_trans a b d x hd abx h

    exact colinear_trans b c d x bcd bcx p
  }


/- sLine parallel to line ab thorugh line c-/
def parallel_line : Point → Point → Point → Set Point :=
  fun a b c ↦ sLine c (Point.mk (c.x + a.x - b.x))

/- Natural definition for tangential-/
def Tangential (s v : Set Point) : Prop :=
  Set.encard (s ∩ v) = 1

/- We actually wont use the following structure too much, but it is nice to keep it in mind-/

@[ext] structure Triangle where
  a : Point
  b : Point
  c : Point
  notline : Noncolinear a b c

/- We will use the lenghts of sides of triangles often-/

def tri_ab: Triangle → ℝ :=
  fun T ↦ (point_abs T.a T.b)

def tri_bc: Triangle → ℝ :=
  fun T ↦ (point_abs T.b T.c)

def tri_ca: Triangle → ℝ :=
  fun T ↦ (point_abs T.c T.a)

/- It will be useful to quickly access the triangle mirrored across the real line.-/

/-sorry-/

/- We now introduce Area, first for points in general, then for our triangle structure-/
def area_points : Point → Point → Point → ℝ :=
  fun a b c ↦ -1/4  * det a b c

def area_tri : Triangle → ℂ :=
  fun T ↦ area_points T.a T.b T.c

/- It is very important that the above expression is the *signed* area, not the abosulte value. So it can take negative values-/

lemma area_zero_iff (a b c : Point): area_points a b c = 0 ↔ colinear a b c := by{
  unfold area_points
  unfold colinear
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

lemma area_add_side (a b c x : Point)(h : x ∈ sLine b c): area_points a b c = area_points a b x + area_points a x c := by{
  rw[area_add a b c x]
  have : area_points x b c = 0 := by{
    refine (area_zero_iff x b c).mpr ?_
    unfold sLine at h
    simp at h
    apply colinear_perm2
    apply colinear_perm1
    assumption
  }
  linarith
}

/-An intermediate goal is to prove Ceva's theorem. For this we first need a definition for sLines being copunctal,
lenght proportions and how they realtie to areas proportions-/

def Copunctal (L R S : Line) : Prop :={
  Set.encard (L.range ∩ R.range ∩ S.range) = 1
}


/- A short notion for a point being in between other:-/

def in_between (a b x : Point) : Prop :=
  point_abs  a x + point_abs x b = point_abs a b

/-A sweet consequence is that this can only happen when x already lies on the line between a b-/

lemma in_between_imp_colinear {a b x : Point} (h: in_between a b x) : colinear a b x := by{
  sorry
}


--def signed_quotient (a b c d : Point) : ℝ :=
  --if Noncolinear a b c ∨ Noncolinear a

  /-def Circumcircle (a b c : Point) : Set Point :=
  if h : colinear a b c then
    if a = b ∨ b = c ∨ c = a then ∅
    else sLine a b
  sorry
  --else by
    --{let z := ex_circumcircle a b c (by { unfold Noncolinear; assumption }) sorry --???? Circle1 z.1 z.2
-/

/- A crucial definition in planar geometry are similar triangles:-/
/- Similar means same rotation as here well! This helps us deal better with area. "Antisimilarity" will be introduced after-/

def Similar (T Q : Triangle) : Prop :=
  sorry

def oldSimilar (T Q : Triangle) : Prop :=
  ∃z : ℂ, (z* T.a.x = Q.a.x) ∧ (z* T.b.x = Q.b.x) ∧ (z* T.c.x = Q.c.x)

/-Note that the scaling factor cant be 0:-/
lemma oldsimilar_neq_zero {T Q : Triangle}(z : ℂ)(zh : (z* T.a.x = Q.a.x) ∧ (z* T.b.x = Q.b.x) ∧ (z* T.c.x = Q.c.x)) : z≠ 0 := by{
  by_contra p
  rw[p] at zh
  simp at zh
  obtain ⟨a,b,c, q⟩ := Q
  simp at zh
  unfold Noncolinear at q
  unfold colinear at q
  unfold det at q
  unfold conj at q
  push_neg at q
  obtain ⟨zh1,zh2,zh3⟩ := zh
  rw[← zh1 ,← zh2,← zh3] at q
  simp at q
}

/-Lets show being oldsimilar is an equivalence relation:-/

lemma oldsimilar_self (T : Triangle) : oldSimilar T T := by{
  use 1
  simp
}

lemma oldsimilar_symm (T Q : Triangle) (h : oldSimilar T Q) : oldSimilar Q T := by{
  obtain ⟨z,zh⟩ := h
  have : z ≠ 0 := by{
    exact oldsimilar_neq_zero T Q z zh
    }
  use z⁻¹
  obtain ⟨zh1,zh2,zh3⟩ := zh
  rw[← zh1, ← zh2, ← zh3]
  field_simp [this]
}

lemma oldsimilar_trans {T Q R: Triangle} (h : oldSimilar T Q) (h': oldSimilar Q R): oldSimilar T R := by{
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
lemma ab_scal (T Q : Triangle)(h : oldSimilar T Q) : (tri_ab T) = (scale_factor T Q) * (tri_ab Q) := by{
  apply oldsimilar_symm at h
  unfold scale_factor
  unfold tri_ab
  unfold oldSimilar at h
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


/- Now introduce circles:-/
@[ext] structure CCircle where
  range : Set Point
  span := ∃ (z : Point) (R : ℝ), R ≥ 0 ∧ range = {p : Point | point_abs z p = R}

/-And tangents to circles-/
#check Tangential

def LineCircleTangent (C: CCircle) (L : Line) : Prop :=
  Tangential C.range L.range

/-Note: I wanna use "Circle" for real and not this odd mathlib thing. So i have to find out how to remove stuff imported-/

/-ommitted-/


/-Trash section about circles:
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

lemma ex_circumcircle {a b c : Point} (h : Noncolinear a b c) :
  ∃! z : (Point × ℝ), {a,b,c} ⊆ Circle1 z.1 z.2 := by{
    sorry
  }


/-def Circumcircle (a b c : Point) : Set Point :=
  if h : colinear a b c then
    if a = b ∨ b = c ∨ c = a then ∅
    else sLine a b
  sorry
  --else by
    --{let z := ex_circumcircle a b c (by { unfold Noncolinear; assumption }) sorry --???? Circle1 z.1 z.2
-/-/
