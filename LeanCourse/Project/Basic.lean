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

open Classical -- In order to take intersections and stuff

@[ext] structure Point where
  x : ℂ

/- Natural definition for tangential of sets in a general manner-/
def Tangential (s v : Set Point) : Prop :=
  Set.encard (s ∩ v) = 1


/- It will be convinient to multiply and add Points-/

/-Sometimes we might want to use the negatives of point (for vectors)-/

def pneg : Point → Point :=
  fun a ↦ Point.mk (-a.x)

def pmul : Point → Point → Point :=
  fun a b ↦ Point.mk (a.x * b.x)

def padd : Point → Point → Point :=
  fun a b ↦ Point.mk (a.x+b.x)

/-Adding zero stays constant-/
lemma padd_zero (a : Point) : padd a (Point.mk 0) = a := by{
  unfold padd
  simp
}
/-Adding is commutative:-/
lemma padd_comm (a b : Point) : padd a b = padd b a := by{
  unfold padd
  ring
}

/-And associative:-/

lemma padd_assoc (a b c : Point): padd (padd a b) c = padd a (padd b c) := by{
  unfold padd
  ring
}

/-So we have an abelian group:-/

lemma padd_neg (a : Point): padd a (pneg a) = Point.mk 0 := by{
  unfold pneg
  unfold padd
  simp
}

/-Also midpoints are neat-/
def pmidpoint : Point → Point → Point :=
  fun a b ↦ Point.mk ((a.x+b.x)/2)

def conj : ℂ → ℂ :=
  fun z ↦ (starRingEnd ℂ) z

def p_scal_mul : ℂ → Point → Point :=
  fun c a ↦ Point.mk (c*a.x)

@[simp] lemma conj_add (x:ℂ) (y:ℂ) : conj (x+y) = conj x + conj y := by{
  unfold conj
  exact RingHom.map_add (starRingEnd ℂ) x y
}

@[simp] lemma conj_mul' (x:ℂ) (y:ℂ) : conj (x*y) = (conj x) * (conj y) := by{
  unfold conj
  exact RingHom.map_mul (starRingEnd ℂ) x y
}

@[simp] lemma conj_sub (x y : ℂ) : conj (x -y) = conj x - conj y := by{
  unfold conj
  exact RingHom.map_sub (starRingEnd ℂ) x y
}

@[simp] lemma conj_div (x y : ℂ) : conj (x / y) = (conj (x)) / (conj (y)) := by{
  unfold conj
  exact RCLike.conj_div x y
}

/-conjugating twice is self:-/

@[simp] lemma conj_twice (x : ℂ) : conj (conj x) = x := by{
  unfold conj
  simp
}

/-A small lemma about complex numbers we will occasionally use is the following:-/
lemma complex_real_mul {x y : ℂ}(hx: x.im = 0)(hy: y.im = 0) : (x*y).im = 0 := by{
  obtain ⟨a,b⟩ := x
  obtain ⟨c,d⟩ := y
  simp at *
  rw[hx,hy]
  ring
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

/-Mirroring twice gives original:-/

@[simp] lemma pconj_twice (a : Point) : pconj (pconj a) = a := by{
  unfold pconj
  simp
}

/-We can conjugate arbitriry sets with this:-/
def set_conj : Set Point → Set Point :=
  fun S ↦ {s | ∃p : S, s = pconj p}

lemma set_conj_def (a : Point)(S : Set Point) : a ∈ S ↔ pconj a ∈ set_conj S := by{
  unfold set_conj
  constructor
  intro ah
  simp
  use a
  intro ah
  simp at ah
  obtain ⟨v,vh1,vh2⟩ := ah
  have : a=v := by{
    calc
      a = pconj (pconj a) := by simp
        _= pconj (pconj v) := by rw[vh2]
        _= v := by simp
  }
  rw[this]
  assumption
}

@[simp] lemma set_conj_twice (S : Set Point) : set_conj (set_conj S) = S := by{
  ext s
  constructor
  intro sh
  unfold set_conj at sh
  simp at sh
  obtain ⟨a,ah1,ah2⟩ := sh
  obtain ⟨b,bh1,bh2⟩ := ah1
  rw[ah2,bh2]
  simp
  assumption
  intro sh
  unfold set_conj
  simp
  use pconj s
  constructor
  use s
  simp
}

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

lemma detperm1 (a b c : Point) : det a b c = -1* (det b a c) := by{
  unfold det
  unfold conj
  obtain ⟨a1,a2⟩ := a
  obtain ⟨b1,b2⟩ := b
  obtain ⟨c1,c2⟩ := c
  simp
  ring
  }

lemma detperm2 (a b c : Point) : det a b c = -1* det c b a := by{
  unfold det
  unfold conj
  obtain ⟨a1,a2⟩ := a
  obtain ⟨b1,b2⟩ := b
  obtain ⟨c1,c2⟩ := c
  simp
  ring
  }

lemma det_self(a b c : Point)(h: a=b ∨ b=c ∨ c=a): det a b c = 0 := by{
  obtain h|h|h := h
  repeat
    rw[h]
    unfold det
    ring
    rfl
}

/-det stay constantt under shifting-/
lemma det_shift (a b c p : Point): det (padd a p) (padd b p) (padd c p) = det a b c := by{
  unfold det
  unfold padd
  unfold conj
  simp
  ring
}

/- We can also conjugate / mirror point:-/
lemma det_conj (a b c : Point): det (pconj a) (pconj b) (pconj c) = - det a b c := by{
  unfold pconj
  unfold det
  simp
  ring
}

/-When deteermining intersections, normal ring and simp tactics wont be enough for plain brute force unfortunately.
Therefore we introduce 3x3 determinant properly here and how to simplify them-/
def detproper: ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℂ :=
  fun a b c x y z r s t ↦ a*y*t+b*z*r+x*s*c-a*s*z-x*b*t-r*y*c

lemma det_detproper(a b c : Point): det a b c = (detproper a.x (conj a.x) 1 b.x (conj b.x) 1 c.x (conj c.x) (1:ℂ)).im := by{
  unfold det detproper
  ring
}

/-Scalar multiplication with rows:-/
lemma detproper_row1 (a b c x y z r s t factor : ℂ): detproper (factor*a) (factor*b) (factor*c) x y z r s t = factor * detproper a b c x y z r s t := by{
  unfold detproper
  ring
}

lemma detproper_row2 (a b c x y z r s t factor : ℂ): detproper a b c (factor*x) (factor*y) (factor*z) r s t = factor * detproper a b c x y z r s t := by{
  unfold detproper
  ring
}

lemma detproper_row3 (a b c x y z r s t factor : ℂ): detproper a b c x y z (factor*r) (factor*s) (factor*t) = factor * detproper a b c x y z r s t := by{
  unfold detproper
  ring
}

/-Scalar multiplication with columns;-/

lemma detproper_column1 (a b c x y z r s t factor : ℂ): detproper (factor*a) b c (factor*x) y z (factor*r) s t = factor * detproper a b c x y z r s t := by{
  unfold detproper
  ring
}

lemma detproper_column2 (a b c x y z r s t factor : ℂ): detproper a (factor*b) c x (factor*y) z r (factor*s) t = factor * detproper a b c x y z r s t := by{
  unfold detproper
  ring
}

lemma detproper_column3 (a b c x y z r s t factor : ℂ): detproper a b (factor*c) x y (factor*z) r s (factor*t) = factor * detproper a b c x y z r s t := by{
  unfold detproper
  ring
}

def colinear (a b c : Point) : Prop :=
  det a b c = 0

def noncolinear (a b c : Point) : Prop :=
  ¬colinear a b c

/-An alternative very useful notion will be given shorty -/

lemma colinear_perm12 (a b c : Point)(h: colinear a b c) : colinear b a c := by{
  unfold colinear at *
  rw[detperm1,h]
  ring
}

lemma colinear_perm13 (a b c : Point)(h: colinear a b c) : colinear c b a := by{
  unfold colinear at *
  rw[detperm2,h]
  ring
}

lemma colinear_perm23 (a b c : Point)(h : colinear a b c) : colinear a c b := by{
  apply colinear_perm13
  apply colinear_perm12
  apply colinear_perm13
  assumption
}

lemma colinear_self(a b c : Point)(h: a=b ∨ b=c ∨ c=a): colinear a b c := by{
  unfold colinear
  exact det_self a b c h
}

/-Some lemmas i added to simp because for some reason they werent included, despite ebing useful for my calculations:-/

@[simp] lemma wtf(x y z v : ℝ): {re := x, im := y} + ({re := z, im := v}:ℂ) = ({re := (x+z), im := (y+v)} : ℂ) := by{
  exact rfl
}

@[simp] lemma wtf2(x y z v : ℝ): {re := x, im := y} - ({re := z, im := v}:ℂ) = ({re := (x-z), im := (y-v)} : ℂ) := by{
  exact rfl
}

@[simp] lemma wtf3(x y z v : ℝ): {re := x, im := y} * ({re := z, im := v}:ℂ) = ({re := (x*z-y*v), im := (x*v+y*z)} : ℂ) := by{
  exact rfl
}

@[simp] lemma wtf4(x y z v : ℝ): {re := x, im := y} / ({re := z, im := v}:ℂ) = ({re := (x*z+y*v)/(z^2+v^2), im := (-x*v+y*z)/(z^2+v^2)} : ℂ) := by{
  calc
    {re := x, im := y} / ({re := z, im := v}:ℂ) = {re := x, im := y} * ((1:ℂ)/({re := z, im := v}:ℂ)) := by ring
      _=  {re := x, im := y} * ({re := z/(z^2+v^2), im := -v/(z^2+v^2)}) := by{
        have : ((1:ℂ) / { re := z, im := v }) = { re := z / (z ^ 2 + v ^ 2), im := -v / (z ^ 2 + v ^ 2) } := by{
          by_cases h0:  { re := z, im := v } = (0:ℂ)
          rw[h0]
          simp
          have : ({ re := z, im := v }:ℂ).re=(0:ℂ) ∧ ({ re := z, im := v }:ℂ).im=(0:ℂ) := by{
            have : { re := z, im := v } = ({re := 0, im := 0}:ℂ) := by{
              rw[h0]
              rfl
            }
            rw[this]
            simp
          }
          simp at this
          rw[this.1]
          rw[this.2]
          simp
          rfl

          field_simp
          ring
          have : z ^ 2 * (z ^ 2 + v ^ 2)⁻¹ + v ^ 2 * (z ^ 2 + v ^ 2)⁻¹ = 1 := by{
            have : (z ^ 2 + v ^ 2) ≠ 0 := by{
              have : z≠0 ∨ v ≠ 0 := by{
                by_contra h1
                simp at *
                rw[h1.1] at h0
                rw[h1.2] at h0
                tauto
              }
              have : 0<z^2+v^2 := by{
                obtain h|h := this
                calc
                  0 < z^2 := by exact pow_two_pos_of_ne_zero h
                    _= z^2 + 0 := by ring
                    _≤ z^2 + v^2 := by apply add_le_add;rfl;exact sq_nonneg v

                calc
                  0 < v^2 := by exact pow_two_pos_of_ne_zero h
                    _= 0+v^2 := by ring
                    _≤ z^2 + v^2 := by apply add_le_add;exact sq_nonneg z;rfl
              }
              exact Ne.symm (ne_of_lt this)
            }
            field_simp
          }
          rw[this]
          rfl
        }
        rw[this]
      }
      _=  ({re := (x*z+y*v)/(z^2+v^2), im := (-x*v+y*z)/(z^2+v^2)} : ℂ) := by simp; ring; tauto
}


/-The alternative (nonsymmetric) notion of colinear is now the following:-/
/-Dont use fucking cyclyic rotation you weirdo-/
lemma colinear_alt (a b c : Point): colinear a b c ↔ ((a.x-b.x)/(a.x-c.x)).im = 0 := by{
  by_cases p : a=c
  rw[p]
  simp
  apply colinear_self
  right
  right
  rfl

  constructor
  intro h
  have ac : a.x-c.x ≠ 0 := by{
    contrapose p
    simp at *
    ext
    calc
      a.x = a.x - 0 := by ring
        _= a.x - (a.x-c.x) := by rw[p]
        _= c.x := by ring
  }

  unfold colinear det at h
  unfold conj at *
  simp at *
  obtain ⟨x,y⟩ := a
  obtain ⟨z,r⟩ := b
  obtain ⟨u,v⟩ := c
  simp at *
  left
  by_cases h0: x= u
  have yv : y ≠ v := by{
    tauto
  }
  have yvsub: y-v≠ 0 := by{
    contrapose yv
    simp at *
    linarith
  }
  --test
  have : 2*(z - x) * (y - v) + (y - r) * (x - u) = 0 := by{
    rw[← h]
    rw[h0]
    ring
  }
  linarith

  have xusub: x-u ≠ 0 := by{
    contrapose h0
    simp at *
    linarith
  }
  have :  2*(x-u)*r =  y * z + (-(u * y) + v * x) + (-(z * v) ) - (-(x * v) + y * u) - (v * z) -
    (-(z * y) )
  := by{
    linarith
  }
  have : r = (y * z + (-(u * y) + v * x) + (-(z * v) ) - (-(x * v) + y * u) - (v * z) -
    (-(z * y) ))/(2*(x-u)) := by{
      field_simp
      linarith
    }
  rw[this]
  field_simp
  ring
  --OMG I DID ITTTTT


  intro h
  have ac : a.x-c.x ≠ 0 := by{
    contrapose p
    simp at *
    ext
    calc
      a.x = a.x - 0 := by ring
        _= a.x - (a.x-c.x) := by rw[p]
        _= c.x := by ring
  }

  unfold colinear det at *
  unfold conj at *
  simp at *
  obtain ⟨x,y⟩ := a
  obtain ⟨z,r⟩ := b
  obtain ⟨u,v⟩ := c
  simp at *
  obtain h|h := h
  swap
  exfalso
  by_cases h0: x=u
  have : y-v ≠ 0 := by{
    contrapose p
    simp at *
    constructor
    assumption
    linarith
  }
  rw[h0] at h
  simp at h
  contradiction

  have xusub : x-u ≠ 0 := by{
    contrapose h0
    simp at *
    linarith
  }
  have : 0 < (x-u)^2+(y-v)^2 := by{
    calc
      0 < (x-u)^2 := by exact pow_two_pos_of_ne_zero xusub
        _= (x-u)^2 + 0 := by ring
        _≤ (x-u)^2+(y-v)^2 := by apply add_le_add; rfl; exact sq_nonneg (y - v)
  }
  rw[h] at this
  linarith


  by_cases h0: x=u
  have yv : y ≠ v := by{
    tauto
  }
  have yvsub: y-v≠ 0 := by{
    contrapose yv
    simp at *
    linarith
  }
  rw[h0]
  ring
  rw[h0] at h
  simp at h
  obtain h|h := h
  have : z = u := by{linarith}
  rw[this]
  ring
  contradiction

  have xusub: x-u ≠ 0 := by{
    contrapose h0
    simp at *
    linarith
  }
  have : (z - x) * (y - v) = (r-y)*(x-u) := by{
    linarith
  }
  have : r=(z-x)*(y-v) / (x-u) + y := by{
    field_simp
    linarith
  }
  rw[this]
  field_simp
  ring
  }

/-With this we can now give the "intuitive" version of colinear:-/
/-We chose this specific formulation, so we have to reindex the least, all others are quite obviously equivalent-/
/-We also wont use this at all, its just a demonstration that our notion with the determinant is indeed "correct" in the usual sense-/
lemma colinear_alt2 (a b c : Point): colinear a b c ↔ a=c ∨ ∃(t : ℝ), b = Point.mk (a.x-(t*(a.x-c.x))) := by{
  constructor
  intro h
  by_cases ac: a=c
  left
  assumption
  have : a.x-c.x ≠ 0 := by{
    contrapose ac
    simp at *
    ext
    calc
      a.x=a.x-0 := by ring
        _= a.x - (a.x-c.x) := by rw[ac]
        _=c.x := by ring
  }
  right
  use ((a.x-b.x)/(a.x-c.x)).re
  have alt: ((a.x-b.x)/(a.x-c.x)).im = 0 := by{exact (colinear_alt a b c).mp h}
  have : (↑((a.x - b.x) / (a.x - c.x)).re : ℂ) = {re := ((a.x - b.x) / (a.x - c.x)).re, im := 0} := by{rfl}
  rw[this]
  rw[← alt]
  simp
  ext
  field_simp

  intro h
  obtain h|h := h
  apply colinear_self
  tauto

  obtain ⟨t,ht⟩ := h
  rw[ht]
  unfold colinear det conj
  simp
  ring
}

/-Going along a vector stays colinear:-/

lemma colinear_add(a b c : Point): colinear a b c ↔ colinear a b (Point.mk (c.x + a.x -b.x)) := by{
  obtain ⟨x,y⟩ := a
  obtain ⟨z,v⟩ := b
  obtain ⟨r,t⟩ := c
  unfold colinear at *
  unfold det at *
  unfold conj at *
  simp at *
  constructor
  intro h
  linarith
  intro h
  linarith
}

/- We can shift colinear points-/

lemma colinear_shift {a b c : Point} (p: Point)(h : colinear a b c): colinear (padd a p) (padd b p) (padd c p) := by{
  unfold colinear at *
  rw[← h]
  exact det_shift a b c p
}

lemma colinear_shift_bw (a b c p : Point)(h : colinear (padd a p) (padd b p) (padd c p)): colinear a b c := by{
  unfold colinear at *
  rw[← h]
  unfold padd det conj
  simp
  ring
}

/-Mirroring colinear points stay colinear:-/

lemma colinear_conj {a b c : Point}(h: colinear a b c): colinear (pconj a) (pconj b) (pconj c) := by{
  unfold colinear at *
  rw[det_conj]
  linarith
}

/-Similarly if they are not colinear:-/
lemma noncolinear_shift {a b c : Point} (p: Point)(h : noncolinear a b c): noncolinear (padd a p) (padd b p) (padd c p) := by{
  unfold noncolinear at *
  unfold colinear at *
  rw[det_shift a b c p]
  assumption
}

lemma noncolinear_conj {a b c : Point}(h: noncolinear a b c): noncolinear (pconj a) (pconj b) (pconj c) := by{
  unfold noncolinear at *
  unfold colinear at *
  rw[det_conj] at *
  contrapose h
  simp at *
  assumption
}


/-The following took me over a week (!) to formalise. It is extremely gruesome and mostly brute force calculations with determinants
However it is central for everything else. Maybe one can simplify the proof significantly, i do not know -/

lemma colinear_trans (a b c d : Point)(h: colinear a b c) (h': colinear a b d)(nab: a ≠ b):  colinear b c d := by{
  by_cases cd: c=d
  apply colinear_self
  right
  left
  assumption
  apply colinear_perm13 at h
  apply colinear_perm12 at h
  apply (colinear_alt b c a).1 at h
  apply colinear_perm12 a b d at h'
  apply (colinear_alt b a d).1 at h'
  apply (colinear_alt b c d).2
  have cool: (((b.x - c.x) / (b.x - a.x)) * ((b.x - a.x) / (b.x - d.x))).im = 0 := by{
    exact complex_real_mul h h'
  }
  have : b.x-a.x ≠ 0 := by{
    by_contra h0
    have: a.x = b.x := by{
      calc
        a.x = a.x + 0 := by ring
          _= a.x + (b.x-a.x) := by rw[h0]
          _= b.x := by ring
    }
    have : a = b := by{ext;assumption}
    contradiction
  }
  have : ((b.x - c.x) / (b.x - a.x)) * ((b.x - a.x) / (b.x - d.x)) = ((b.x - c.x) / (b.x - d.x)) := by{
    field_simp
  }
  rw[this] at cool
  assumption
}

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

/- Lets define parallel lines. We say a line is parallel to itself, so we can get a nice equivalence relation-/
def Parallel(L R : Line) : Prop :=
  ∃p : Point, R = shift_line L p

lemma shift_line_parallel (L : Line)(a : Point): Parallel L (shift_line L a) := by{
  unfold Parallel
  use a
}

/-With colinear alt we can give a neat alternative notion of colinear:-/
lemma parallel_quot {a b c d : Point}(ab : a ≠ b)(cd : c ≠ d): Parallel (Line_through ab) (Line_through cd) ↔ ((a.x-b.x)/(c.x-d.x)).im = 0 := by{
  constructor
  intro h
  unfold Parallel at h
  obtain ⟨p,ph⟩ := h
  have cmem: Lies_on c (Line_through cd) := by {exact line_through_mem_left cd}
  have dmem: Lies_on d (Line_through cd) := by {exact line_through_mem_right cd}
  rw[ph] at cmem
  rw[ph] at dmem
  unfold shift_line at cmem dmem
  unfold Lies_on at cmem dmem
  simp at *
  obtain ⟨r,rh1,rh2⟩ := cmem
  obtain ⟨s,sh1,sh2⟩ := dmem
  by_cases sbo : b=s
  have as: a ≠ s := by{
    rw[sbo] at ab
    assumption
  }
  have uwu: Line_through ab = Line_through as := by{
    apply line_through_unique
    constructor
    exact line_through_mem_left ab
    rw[← sbo]
    exact line_through_mem_right ab
  }
  rw[uwu]at sh1 rh1 ph
  clear ab uwu
  have : b.x = s.x := by{
    rw[sbo]
  }
  rw[this]
  clear this b sbo
  rw[rh2,sh2]
  unfold padd
  simp
  have rs: r ≠ s := by{
    by_contra rs
    have : c=d := by{
      rw[rh2,sh2]
      ext
      unfold padd
      simp
      rw[rs]
    }
    contradiction
  }
  clear ph rh2 sh2 cd c d sh1
  unfold Line_through at rh1
  simp at rh1
  apply colinear_perm12 at rh1
  apply (colinear_alt s a r).1 at rh1
  rw[← rh1]
  obtain ⟨a1,a2⟩ := a
  obtain ⟨s1,s2⟩ := s
  obtain ⟨r1,r2⟩ := r
  simp
  ring


  unfold Line_through at sh1 rh1
  simp at *
  rw[rh2,sh2]
  unfold padd
  simp
  have brs : colinear b r s := by{exact colinear_trans a b r s rh1 sh1 ab}
  have : ((a.x - b.x) / (s.x - r.x)).im = 0 := by{
    apply colinear_perm13 at brs
    apply colinear_perm23 at brs
    apply colinear_perm12 at sh1
    apply (colinear_alt s b r).1 at brs
    apply (colinear_alt b a s).1 at sh1
    have : (b.x - a.x) / (b.x - s.x) = (a.x-b.x)/(s.x-b.x) := by{
      by_cases bs: b.x=s.x
      rw[bs]
      simp

      have bssub: b.x-s.x ≠ 0 := by{
        contrapose bs
        simp at *
        calc
          b.x = b.x - 0 := by ring
            _= b.x - (b.x-s.x) := by{rw[bs]}
            _= s.x := by{ring}
      }
      have sbsub: s.x-b.x ≠ 0 := by{
        contrapose bs
        simp at *
        calc
          b.x = b.x + 0 := by{ring}
            _= b.x + (s.x-b.x) := by{rw[bs]}
            _= s.x := by{ring}
      }
      field_simp
      ring
    }
    rw[this] at sh1
    clear this
    by_cases sbsub: s.x-b.x = 0
    swap
    have : (a.x - b.x) / (s.x - r.x) = (a.x - b.x) / (s.x - b.x) * ((s.x - b.x) / (s.x - r.x)) := by{field_simp}
    rw[this]
    clear this
    exact complex_real_mul sh1 brs

    have sb: s = b := by{
      ext
      calc
        s.x = s.x - 0 := by{ring}
          _= s.x - (s.x-b.x) := by{rw[sbsub]}
          _= b.x := by ring
    }
    tauto
  }
  calc
    ((a.x - b.x) / (r.x - s.x)).im = -1 * ((a.x - b.x) / (s.x - r.x)).im := by{
      obtain ⟨a1,a2⟩ := a
      obtain ⟨b1,b2⟩ := b
      obtain ⟨s1,s2⟩ := s
      obtain ⟨r1,r2⟩ := r
      simp
      ring
    }
      _= -1*0 := by{rw[this]}
      _= 0 := by ring



  intro h
  unfold Parallel
  let p := Point.mk (c.x-a.x)
  use p
  have nice: colinear a b (padd d (pneg p)) := by{
    apply (colinear_alt a b (padd d (pneg p))).2
    unfold padd pneg p
    simp
    rw[← h]
    obtain ⟨a1,a2⟩ := a
    obtain ⟨b1,b2⟩ := b
    obtain ⟨c1,c2⟩ := c
    obtain⟨d1,d2⟩ := d
    simp
    ring
  }
  symm
  apply line_through_unique
  unfold Lies_on shift_line Line_through
  simp
  constructor
  use a
  unfold p
  constructor
  apply colinear_self
  right
  right
  rfl
  ext
  unfold padd
  ring

  use (padd d (pneg p))
  constructor
  assumption
  unfold padd pneg
  ext
  simp
  ring
}

/- A big Lemma is the following: Two Lines are parallel, if one is the other one shifted:
 The cool thing about this, that we have defined enough for this to be proven (almost) purely geometrically-/
 /-It still is quite a bummer though, unfortunately-/

theorem parallel_def (L R : Line) : Parallel L R ↔ L.range ∩ R.range = ∅ ∨ L.range = R.range := by{
  unfold Parallel
  constructor
  intro h
  obtain ⟨p,ph⟩ := h
  obtain ⟨a,ah⟩ := ex_point_on_line L
  by_cases ap: Lies_on (padd a p) L
  have : R = L := by{
    by_cases h0: p = Point.mk (0)
    rw[h0] at ph
    rw[ph]
    exact shift_line_zero L


    apply lines_eq_ex
    use a
    use (padd a p)
    constructor
    contrapose h0
    simp at *
    unfold padd at h0
    have : a.x = a.x + p.x := by{
      nth_rw 1 [h0]
    }
    ext
    simp
    calc
      p.x = -a.x + (a.x + p.x) := by ring
        _= -a.x + a.x := by rw[← this]
        _= 0 := by ring
    constructor
    unfold Lies_on
    rw[ph]
    unfold shift_line
    simp
    use padd a (pneg p)
    have aap: a ≠ padd a p := by{
      contrapose h0
      unfold padd at h0
      simp at *
      ext
      simp
      have : a.x = ({ x := a.x + p.x } : Point).x := by{rw[← h0]}
      simp at this
      assumption
    }
    have Lh: L = Line_through aap := by{
      apply line_through_unique
      constructor
      assumption
      assumption
    }
    constructor
    rw[Lh]
    unfold Line_through
    simp
    unfold padd pneg colinear det conj
    simp
    ring

    ext
    unfold pneg padd
    simp

    constructor
    assumption
    constructor
    rw[ph]
    exact mem_line_shift a p L ah
    assumption
  }
  rw[this]
  right
  rfl

  left
  by_contra h0
  have : (L.range ∩ R.range).Nonempty := by{exact nonempty_iff_ne_empty.mpr h0}
  apply Set.nonempty_def.1 at this
  obtain ⟨b,bh⟩ := this
  have ab: a ≠ b := by{
    by_contra u
    rw[← u] at bh
    clear u b
    have aR: a ∈ R.range := by exact bh.2
    clear bh
    rw[ph] at aR
    unfold shift_line at aR
    simp at aR
    obtain ⟨c,ch1,ch2⟩ := aR
    rw[ch2] at ah
    rw[ch2] at ap
    contrapose ap
    simp
    clear ch2 ap a h0 ph R
    have cL: Lies_on c L := by{
      unfold Lies_on
      assumption
    }
    clear ch1
    by_cases p0: p= Point.mk 0
    rw[p0]
    simp [padd_comm, padd_zero, cL]

    have ccp: c ≠ padd c p := by{
      contrapose p0
      simp at *
      ext
      simp
      unfold padd at p0
      have : c.x = ({ x := c.x + p.x } : Point).x := by{rw[← p0]}
      simp at this
      assumption
    }
    have hL: L = Line_through ccp := by{
      apply line_through_unique
      constructor
      assumption
      assumption
    }
    rw[hL]
    clear ah L hL cL
    unfold Line_through Lies_on padd colinear det conj
    simp
    ring
  }
  obtain ⟨bh1,bh2⟩ := bh
  rw[ph] at bh2
  unfold shift_line at bh2
  simp at bh2
  obtain ⟨c,⟨ch1,ch2⟩⟩ := bh2
  rw[ch2] at bh1
  clear ab ch2 b ph
  have hp: p ≠ Point.mk (0) := by{
    contrapose ap
    simp at *
    rw[ap]
    rw[padd_zero a]
    assumption
  }
  have ccp: c ≠ padd c p := by{
    contrapose hp
    simp at *
    unfold padd at hp
    have : c.x = ({ x := c.x + p.x } : Point).x := by{rw[← hp]}
    simp at this
    ext
    assumption
  }
  have hL : L = Line_through ccp := by{
    apply line_through_unique
    constructor
    assumption
    assumption
  }
  contrapose ap
  simp
  clear h0 ap
  rw[hL] at ah
  rw[hL]
  unfold Line_through at *
  unfold Lies_on at *
  simp at *
  clear hL ccp hp ch1 bh1 L R
  unfold colinear at *
  rw[← ah]
  unfold padd det conj
  simp
  ring

  intro h
  obtain h|h := h
  swap
  have : L = R := by{
    ext x
    rw[h]
  }
  rw[this]
  use Point.mk 0
  rw[shift_line_zero R]

  obtain ⟨a,b,ab,aL,bL⟩ := ex_points_on_line L
  obtain ⟨c,ch⟩ := ex_point_on_line R
  let p := Point.mk (c.x-a.x)
  use p
  have : L = Line_through ab := by{
    apply line_through_unique
    constructor
    assumption
    assumption
  }
  rw[this]
  let d := padd b p
  have cd: c ≠ d := by{
    unfold d
    have p0: p ≠ Point.mk (0) := by{
      unfold p
      simp
      contrapose h
      simp at h
      have : a.x = c.x := by{
        calc
          a.x = a.x + (0:ℂ) := by ring
            _=a.x + (c.x-a.x) := by rw[h]
            _= c.x := by ring
      }
      have ac: a = c := by{ext;exact this}
      rw[ac] at aL
      unfold Lies_on at *
      by_contra z
      have : c ∈ L.range ∩ R.range := by{constructor;assumption;assumption}
      rw[z] at this
      contradiction
    }
    have : c = padd a p := by{
      unfold p padd
      ext
      ring
    }
    rw[this]
    unfold padd
    simp
    by_contra h0
    have : a = b := by{
      ext
      calc
        a.x = a.x + c.x - c.x := by ring
          _= a.x + (b.x + (c.x - a.x)) - c.x := by nth_rw 1 [h0]
          _= b.x := by ring
    }
    contradiction
  }
  --following is the last main result, having proved it, rest gets easy
  have hR: R = Line_through cd := by{
    apply line_through_unique
    constructor
    assumption
    obtain ⟨e,f,ef,re,rf⟩ := ex_points_on_line R
    have : c ≠ e ∨ c ≠ f := by{
      by_contra h0
      simp at h0
      have : e = f := by{
        calc
          e = c := by rw[h0.1]
            _= f := by rw[h0.2]
      }
      contradiction
    }
    obtain ce|cf := this
    /-ab hier-/
    have hR : R = Line_through ce := by{
      apply line_through_unique
      constructor
      assumption
      exact re
    }
    rw[hR]
    unfold Lies_on
    unfold Line_through
    simp
    clear f ef rf
    by_contra h0
    let m := ((conj a.x) - (conj b.x))*(c.x-e.x)-(a.x-b.x)*(conj c.x - conj e.x)
    --n IST FALSCH DEFINIERT OJE
    let n := (((conj a.x)*b.x-a.x*(conj b.x))*(c.x-e.x)-(a.x-b.x)*((conj c.x)*e.x-c.x*(conj e.x)))
    have t1: m ≠ 0 := by{
      by_contra h1
      unfold m at h1
      have h2: (conj a.x - conj b.x) * (c.x - e.x) = (a.x - b.x) * (conj c.x - conj e.x) := by{
        calc
          (conj a.x - conj b.x) * (c.x - e.x) = (conj a.x - conj b.x) * (c.x - e.x) - 0 := by ring
            _= (conj a.x - conj b.x) * (c.x - e.x) - ((conj a.x - conj b.x) * (c.x - e.x) - (a.x - b.x) * (conj c.x - conj e.x)) := by rw[h1]
            _= (a.x - b.x) * (conj c.x - conj e.x) := by ring
      }
      clear h1
      have ab_sub: a.x-b.x ≠ 0 := by{
        by_contra ab
        have : a=b := by{
        simp at *
        ext
        calc
          a.x = a.x -0 := by ring
            _= a.x -(a.x-b.x) := by rw[ab]
            _= b.x := by ring
        }
        contradiction
      }
      have ce_conj_sub : conj c.x - conj e.x ≠ 0 := by{
        by_contra h3
        simp at *
        have : conj c.x = conj e.x := by{
          calc
            conj c.x = conj c.x - 0 := by ring
              _= conj c.x - (conj c.x - conj e.x) := by{rw[h3]}
              _= conj e.x := by ring
        }
        have : c=e := by{
          ext
          rw[← conj_twice c.x, ← conj_twice e.x, this]
        }
        contradiction
      }
      have ce_sub : c.x - e.x ≠ 0 := by{
        by_contra ab
        have : c=e := by{
        simp at *
        ext
        calc
          c.x = c.x -0 := by ring
            _= c.x -(c.x-e.x) := by rw[ab]
            _= e.x := by ring
        }
        contradiction
      }
      have abce: conj ((a.x-b.x)/(c.x-e.x)) = (a.x-b.x)/(c.x-e.x) := by{
        simp
        field_simp
        assumption
      }
      --focus on h0
      have imzero: ( (a.x - b.x) / (c.x - e.x)).im = 0 := by{
        exact Complex.conj_eq_iff_im.mp abce
      }
      /-Aus dem könnte man mit colinear_alt folgern:
      ab parallel zu ce
      und dann wird h0 halt zum problem-/
      have LR_parallel: Parallel L R := by{
        rw[this,hR]
        exact (parallel_quot ab ce).mpr imzero
      }
      obtain ⟨q,qh⟩ := LR_parallel
      clear abce ce_sub ce_conj_sub ab_sub h2 m n
      contrapose h0
      simp
      rw[qh] at ch re
      unfold Lies_on shift_line at re ch
      simp at *
      obtain ⟨u,uh1,uh2⟩ := ch
      obtain ⟨v,vh1,vh2⟩ := re
      unfold d p
      rw[uh2,vh2]
      unfold padd
      simp
      unfold colinear
      have : det { x := u.x + q.x } { x := v.x + q.x } { x := b.x + (u.x + q.x - a.x) } = det u v (padd u (Point.mk (b.x-a.x))) := by{
        unfold det padd conj
        simp
        ring
      }
      rw[this]
      clear this
      have goal: colinear u v (padd u (Point.mk (b.x - a.x))) := by{
        rw[this] at vh1 uh1
        unfold Line_through at vh1 uh1
        simp at vh1 uh1
        have abshift: colinear a b (padd u (Point.mk (b.x-a.x))) := by{
          unfold colinear at uh1
          unfold colinear
          calc
            det a b (padd u { x := b.x - a.x }) = det a b u := by{
              unfold det padd
              simp
              ring
            }
              _= 0 := by{assumption}
        }
        have shiftmem: Lies_on (padd u (Point.mk (b.x-a.x))) (Line_through ab) := by{
          unfold Lies_on Line_through
          simp
          assumption
        }
        have uv : u ≠ v := by{
          by_contra ce
          have : c = e := by{
            rw[uh2,vh2]
            ext
            unfold padd
            rw[ce]
          }
          contradiction
        }
        have uvL: Line_through ab = Line_through uv := by{
          apply line_through_unique
          constructor
          repeat
            unfold Lies_on Line_through
            assumption
        }
        rw[uvL] at shiftmem
        unfold Lies_on Line_through at shiftmem
        assumption
      }
      unfold colinear at goal
      assumption
    }
    --I also have to do the reverse...
    unfold conj at t1
    have t2: conj m ≠ 0 := by{
      by_contra h0
      rw[← conj_twice m] at t1
      rw[h0] at t1
      unfold conj at t1
      simp at t1
    }
    let q := Point.mk (n / m)
    have : conj m = -m := by{
      unfold m
      simp
    }
    rw[this] at t2
    have colinear1 : colinear a b q := by{
      unfold colinear
      rw[det_detproper a b q]
      have goal: (detproper a.x (conj a.x) 1 b.x (conj b.x) 1 q.x (conj q.x) 1) = 0 := by{
        unfold q
        simp
        rw[this]
        have : detproper a.x (conj a.x) 1 b.x (conj b.x) 1 (n / m) (conj n / - m) 1 = 1/m * detproper a.x (conj a.x) 1 b.x (conj b.x) 1 (n) (-conj n) (m) := by{
            calc
              detproper a.x (conj a.x) 1 b.x (conj b.x) 1 (n / m) (conj n / - m) 1 = detproper a.x (conj a.x) 1 b.x (conj b.x) 1 ((1/m)*(n)) ((1/m)*(-conj n)) (1/m * m) := by{
                field_simp
                have : conj n / -m = - conj n / m := by{
                  field_simp
                }
                rw[this]
              }
                _= 1/m * detproper a.x (conj a.x) 1 b.x (conj b.x) 1 (n) (-conj n) (m) := by{rw [detproper_row3]}
        }
        rw[this]
        clear this
        field_simp
        unfold n m
        unfold detproper
        simp
        ring
      }
      rw[goal]
      rfl
    }

    have colinear2: colinear c e q := by{
      unfold colinear
      rw[det_detproper c e q]
      have goal: detproper c.x (conj c.x) 1 e.x (conj e.x) 1 q.x (conj q.x) 1 = 0 := by{
        unfold q
        simp
        rw[this]
        have : detproper c.x (conj c.x) 1 e.x (conj e.x) 1 (n / m) (conj n / - m) 1 = 1/m * detproper c.x (conj c.x) 1 e.x (conj e.x) 1 (n) (-conj n) (m) := by{
            calc
              detproper c.x (conj c.x) 1 e.x (conj e.x) 1 (n / m) (conj n / - m) 1 = detproper c.x (conj c.x) 1 e.x (conj e.x) 1 ((1/m)*(n)) ((1/m)*(-conj n)) (1/m * m) := by{
                field_simp
                have : conj n / -m = - conj n / m := by{
                  field_simp
                }
                rw[this]
              }
                _= 1/m * detproper c.x (conj c.x) 1 e.x (conj e.x) 1 (n) (-conj n) (m) := by{rw [detproper_row3]}
        }
        rw[this]
        clear this
        field_simp
        unfold n m
        unfold detproper
        simp
        ring
      }
      rw[goal]
      rfl
    }
    have qbad: q ∈ L.range ∩ R.range := by{
      constructor
      swap
      rw[hR]
      unfold Line_through
      simp
      assumption

      have : L = Line_through ab := by{assumption}
      rw[this]
      unfold Line_through
      simp
      assumption
    }
    rw[h] at qbad
    contradiction

    --letzte 200 zeilen nohcmal bruhhh

    have hR : R = Line_through cf := by{
      apply line_through_unique
      constructor
      assumption
      exact rf
    }
    rw[hR]
    unfold Lies_on
    unfold Line_through
    simp
    clear e ef re
    by_contra h0
    let m := ((conj a.x) - (conj b.x))*(c.x-f.x)-(a.x-b.x)*(conj c.x - conj f.x)
    let n := (((conj a.x)*b.x-a.x*(conj b.x))*(c.x-f.x)-(a.x-b.x)*((conj c.x)*f.x-c.x*(conj f.x)))
    have t1: m ≠ 0 := by{
      by_contra h1
      unfold m at h1
      have h2: (conj a.x - conj b.x) * (c.x - f.x) = (a.x - b.x) * (conj c.x - conj f.x) := by{
        calc
          (conj a.x - conj b.x) * (c.x - f.x) = (conj a.x - conj b.x) * (c.x - f.x) - 0 := by ring
            _= (conj a.x - conj b.x) * (c.x - f.x) - ((conj a.x - conj b.x) * (c.x - f.x) - (a.x - b.x) * (conj c.x - conj f.x)) := by rw[h1]
            _= (a.x - b.x) * (conj c.x - conj f.x) := by ring
      }
      clear h1
      have ab_sub: a.x-b.x ≠ 0 := by{
        by_contra ab
        have : a=b := by{
        simp at *
        ext
        calc
          a.x = a.x -0 := by ring
            _= a.x -(a.x-b.x) := by rw[ab]
            _= b.x := by ring
        }
        contradiction
      }
      have cf_conj_sub : conj c.x - conj f.x ≠ 0 := by{
        by_contra h3
        simp at *
        have : conj c.x = conj f.x := by{
          calc
            conj c.x = conj c.x - 0 := by ring
              _= conj c.x - (conj c.x - conj f.x) := by{rw[h3]}
              _= conj f.x := by ring
        }
        have : c=f := by{
          ext
          rw[← conj_twice c.x, ← conj_twice f.x, this]
        }
        contradiction
      }
      have cf_sub : c.x - f.x ≠ 0 := by{
        by_contra ab
        have : c=f := by{
        simp at *
        ext
        calc
          c.x = c.x -0 := by ring
            _= c.x -(c.x-f.x) := by rw[ab]
            _= f.x := by ring
        }
        contradiction
      }
      have abcf: conj ((a.x-b.x)/(c.x-f.x)) = (a.x-b.x)/(c.x-f.x) := by{
        simp
        field_simp
        assumption
      }
      --focus on h0
      have imzero: ( (a.x - b.x) / (c.x - f.x)).im = 0 := by{
        exact Complex.conj_eq_iff_im.mp abcf
      }
      have LR_parallel: Parallel L R := by{
        rw[this,hR]
        exact (parallel_quot ab cf).mpr imzero
      }
      obtain ⟨q,qh⟩ := LR_parallel
      clear abcf cf_sub cf_conj_sub ab_sub h2 m n
      contrapose h0
      simp
      rw[qh] at ch rf
      unfold Lies_on shift_line at rf ch
      simp at *
      obtain ⟨u,uh1,uh2⟩ := ch
      obtain ⟨v,vh1,vh2⟩ := rf
      unfold d p
      rw[uh2,vh2]
      unfold padd
      simp
      unfold colinear
      have : det { x := u.x + q.x } { x := v.x + q.x } { x := b.x + (u.x + q.x - a.x) } = det u v (padd u (Point.mk (b.x-a.x))) := by{
        unfold det padd conj
        simp
        ring
      }
      rw[this]
      clear this
      have goal: colinear u v (padd u (Point.mk (b.x - a.x))) := by{
        rw[this] at vh1 uh1
        unfold Line_through at vh1 uh1
        simp at vh1 uh1
        have abshift: colinear a b (padd u (Point.mk (b.x-a.x))) := by{
          unfold colinear at uh1
          unfold colinear
          calc
            det a b (padd u { x := b.x - a.x }) = det a b u := by{
              unfold det padd
              simp
              ring
            }
              _= 0 := by{assumption}
        }
        have shiftmem: Lies_on (padd u (Point.mk (b.x-a.x))) (Line_through ab) := by{
          unfold Lies_on Line_through
          simp
          assumption
        }
        have uv : u ≠ v := by{
          by_contra cf
          have : c = f := by{
            rw[uh2,vh2]
            ext
            unfold padd
            rw[cf]
          }
          contradiction
        }
        have uvL: Line_through ab = Line_through uv := by{
          apply line_through_unique
          constructor
          repeat
            unfold Lies_on Line_through
            assumption
        }
        rw[uvL] at shiftmem
        unfold Lies_on Line_through at shiftmem
        assumption
      }
      unfold colinear at goal
      assumption
    }

    unfold conj at t1
    have t2: conj m ≠ 0 := by{
      by_contra h0
      rw[← conj_twice m] at t1
      rw[h0] at t1
      unfold conj at t1
      simp at t1
    }
    let q := Point.mk (n / m)
    have : conj m = -m := by{
      unfold m
      simp
    }
    rw[this] at t2
    have colinear1 : colinear a b q := by{
      unfold colinear
      rw[det_detproper a b q]
      have goal: (detproper a.x (conj a.x) 1 b.x (conj b.x) 1 q.x (conj q.x) 1) = 0 := by{
        unfold q
        simp
        rw[this]
        have : detproper a.x (conj a.x) 1 b.x (conj b.x) 1 (n / m) (conj n / - m) 1 = 1/m * detproper a.x (conj a.x) 1 b.x (conj b.x) 1 (n) (-conj n) (m) := by{
            calc
              detproper a.x (conj a.x) 1 b.x (conj b.x) 1 (n / m) (conj n / - m) 1 = detproper a.x (conj a.x) 1 b.x (conj b.x) 1 ((1/m)*(n)) ((1/m)*(-conj n)) (1/m * m) := by{
                field_simp
                have : conj n / -m = - conj n / m := by{
                  field_simp
                }
                rw[this]
              }
                _= 1/m * detproper a.x (conj a.x) 1 b.x (conj b.x) 1 (n) (-conj n) (m) := by{rw [detproper_row3]}
        }
        rw[this]
        clear this
        field_simp
        unfold n m
        unfold detproper
        simp
        ring
      }
      rw[goal]
      rfl
    }

    have colinear2: colinear c f q := by{
      unfold colinear
      rw[det_detproper c f q]
      have goal: detproper c.x (conj c.x) 1 f.x (conj f.x) 1 q.x (conj q.x) 1 = 0 := by{
        unfold q
        simp
        rw[this]
        have : detproper c.x (conj c.x) 1 f.x (conj f.x) 1 (n / m) (conj n / - m) 1 = 1/m * detproper c.x (conj c.x) 1 f.x (conj f.x) 1 (n) (-conj n) (m) := by{
            calc
              detproper c.x (conj c.x) 1 f.x (conj f.x) 1 (n / m) (conj n / - m) 1 = detproper c.x (conj c.x) 1 f.x (conj f.x) 1 ((1/m)*(n)) ((1/m)*(-conj n)) (1/m * m) := by{
                field_simp
                have : conj n / -m = - conj n / m := by{
                  field_simp
                }
                rw[this]
              }
                _= 1/m * detproper c.x (conj c.x) 1 f.x (conj f.x) 1 (n) (-conj n) (m) := by{rw [detproper_row3]}
        }
        rw[this]
        clear this
        field_simp
        unfold n m
        unfold detproper
        simp
        ring
      }
      rw[goal]
      rfl
    }
    have qbad: q ∈ L.range ∩ R.range := by{
      constructor
      swap
      rw[hR]
      unfold Line_through
      simp
      assumption

      have : L = Line_through ab := by{assumption}
      rw[this]
      unfold Line_through
      simp
      assumption
    }
    rw[h] at qbad
    contradiction
  }
  rw[hR]
  unfold Line_through shift_line
  simp
  ext r
  simp
  unfold d
  constructor
  intro th
  use padd r (pneg p)
  constructor
  swap
  unfold padd pneg
  ext
  ring

  have : c = padd a p := by{
    unfold p padd
    ext
    ring
  }
  rw[this] at th
  have : r = padd (padd r (pneg p)) p := by{
    unfold padd pneg
    ring
  }
  rw[this] at th
  exact colinear_shift_bw a b (padd r (pneg p)) p th

  intro rh
  obtain ⟨u,uh1,uh2⟩ := rh
  have : c = padd a p := by{
    unfold p padd
    ext
    ring
  }
  rw[this]
  rw[uh2]
  exact colinear_shift p uh1
}

lemma parallel_refl (L : Line) : Parallel L L := by{
  apply (parallel_def L L).2
  right
  rfl
}


/-With this we can now talk about Intersections of lines:-/

theorem lines_intersect {L R : Line}(h : ¬Parallel L R) : ∃! s : Point, Lies_on s L ∧ Lies_on s R := by{
  unfold Lies_on

  have : Set.encard (L.range ∩ R.range) = 1 := by{
    by_cases p: Set.encard (L.range ∩ R.range) ≤ 1
    have : Set.encard (L.range ∩ R.range) = 0 ∨ Set.encard (L.range ∩ R.range) = 1 := by{
      apply Set.encard_le_one_iff_eq.1 at p
      obtain p|p := p
      left
      rw[p]
      exact Set.encard_empty
      right
      exact Set.encard_eq_one.2 p
    }
    obtain this|this := this
    have : (L.range ∩ R.range = ∅) := by exact encard_eq_zero.mp this
    have : Parallel L R := by{
      apply (parallel_def L R).2
      left
      assumption
    }
    contradiction
    assumption

    exfalso
    contrapose h
    simp at *
    have : ∃ (a b : Point), a ≠ b ∧ a ∈ (L.range ∩ R.range) ∧ b ∈ (L.range ∩ R.range) := by{
      apply Set.one_lt_encard_iff.1 at p
      tauto
    }
    obtain ⟨a,b,ab,ah,bh⟩ := this

    apply ex_unique_line_mem at ab
    obtain ⟨U,⟨hU1,hU2⟩⟩ := ab
    simp at hU2
    have LU: L = U := by{
      apply hU2
      unfold Lies_on
      exact mem_of_mem_inter_left ah
      unfold Lies_on
      exact mem_of_mem_inter_left bh
    }
    have RU: R = U := by{
      apply hU2
      unfold Lies_on
      exact mem_of_mem_inter_right ah
      unfold Lies_on
      exact mem_of_mem_inter_right bh
    }
    rw[LU,RU]
    exact parallel_refl U
  }
  have : ∃! s : Point, s ∈ (L.range ∩ R.range) := by{
    apply Set.encard_eq_one.1 at this
    obtain ⟨s,hs⟩ := this
    rw[hs]
    exact ExistsUnique.intro s rfl fun y ↦ congrArg fun y ↦ y
  }
  assumption
}

def Intersection {L R : Line}(h : ¬ Parallel L R) : Point :=
  (lines_intersect h).choose

/-This indeed is in the intersection:-/

lemma intersection_mem {L R : Line}(LR : ¬ Parallel L R) : Lies_on (Intersection LR) L ∧ Lies_on (Intersection LR) R := by{
  exact (Classical.choose_spec (lines_intersect LR)).1
}

/-lines_intersect lemma now become nicer:-/

lemma intersect_lines {L R : Line}{a : Point}(LR : ¬ Parallel L R){ah: Lies_on a L ∧ Lies_on a R} : a = Intersection LR := by{
  have : ∃! s, Lies_on s L ∧ Lies_on s R := by{exact lines_intersect LR}
  obtain ⟨s,sh1,sh2⟩ := this
  simp at sh2
  have as: a=s := by{specialize sh2 a ah.1 ah.2; assumption}
  have is: Intersection LR = s := by{specialize sh2 (Intersection LR) (intersection_mem LR).1 (intersection_mem LR).2; assumption}
  rw[as,is]
}

/- With this we now show being parallel is an equivalence relation:-/

lemma parallel_symm (L R : Line)(h : Parallel L R) : Parallel R L := by{
  apply (parallel_def L R).1 at h
  apply (parallel_def R L).2
  obtain h|h := h
  · left
    rw[Set.inter_comm]
    assumption
  · right
    symm
    assumption
}

lemma parallel_trans {L R S : Line}(LR : Parallel L R)(RS : Parallel R S) : Parallel L S := by{
  unfold Parallel at *
  obtain ⟨p,hp⟩ := LR
  obtain ⟨q,hq⟩ := RS
  use padd p q
  rw[hp] at hq
  rw[← shift_line_trans L p q]
  assumption
}

/-Note: I should probably redo this section a bit, define parallel_through first and then use it
for weak_parallel_postulate. Else everyhting is quite redundant-/

lemma weak_parallel_postulate (L : Line)(a : Point) : ∃ Q : Line, Lies_on a Q ∧ Parallel L Q := by{
  obtain ⟨b,bh⟩ := ex_point_on_line L
  use (shift_line L (Point.mk (a.x-b.x)))
  constructor
  unfold Lies_on shift_line
  simp

  use b
  constructor
  assumption
  ext
  unfold padd
  ring
  exact shift_line_parallel L (Point.mk (a.x-b.x))
}

theorem parallel_postulate (L : Line)(a : Point) : ∃! Q : Line, Lies_on a Q ∧ Parallel L Q := by{
  obtain ⟨U,Uh⟩ := weak_parallel_postulate L a
  use U
  constructor
  assumption

  intro R Rh
  by_cases UR: Parallel U R
  unfold Parallel at UR
  obtain h|h := UR
  unfold Lies_on at *
  have : a ∈ U.range ∧ a ∈ R.range := by{
    constructor
    exact Uh.1
    exact Rh.1
  }
  have : a ∈ U.range ∩ R.range := by exact this
  have UR: Parallel U R := by{
    obtain ⟨_,hi⟩ := Uh
    apply parallel_symm at hi
    exact parallel_trans hi Rh.2
  }
  apply (parallel_def U R).1 at UR
  obtain h'|h' := UR
  rw[h'] at this
  contradiction
  ext
  rw[h']

  exfalso
  obtain ⟨_,hU⟩ := Uh
  obtain ⟨_,hR⟩ := Rh
  have : Parallel U R := by{
    apply parallel_symm at hU
    exact parallel_trans hU hR
  }
  contradiction
}

def parallel_through : Line → Point → Line :=
  fun L a ↦ (weak_parallel_postulate L a).choose

/-This really has the properties we want: -/

lemma point_lies_on_parallel_through (L: Line)(a : Point) : Lies_on a (parallel_through L a) := by{
  unfold parallel_through
  exact (Exists.choose_spec (weak_parallel_postulate L a)).1
}

lemma parallel_through_is_parallel (L : Line)(a : Point) : Parallel L (parallel_through L a) := by{
  unfold parallel_through
  exact (Exists.choose_spec (weak_parallel_postulate L a)).2
}

lemma parallel_through_is_parallel_through (L : Line)(a : Point) : Lies_on a (parallel_through L a) ∧ Parallel L (parallel_through L a) := by{
  unfold parallel_through
  exact Exists.choose_spec (weak_parallel_postulate L a)
}

/-Now we can formulate the parallel postualte in a nice way:-/

theorem parallel_through_unique (L R : Line)(a : Point)(h : Lies_on a R ∧ Parallel L R) : R = parallel_through L a := by{
  obtain ⟨S,hS1,hS2⟩ := parallel_postulate L a
  simp at hS2
  have RS: R = S := by{
    exact hS2 R h.1 h.2
  }
  have PTS: parallel_through L a = S := by{
    exact hS2 (parallel_through L a) (point_lies_on_parallel_through L a) (parallel_through_is_parallel L a)
  }
  rw[RS,PTS]
}
