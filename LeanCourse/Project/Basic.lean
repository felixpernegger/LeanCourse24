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
  ring_nf
}

/-And associative:-/

lemma padd_assoc (a b c : Point): padd (padd a b) c = padd a (padd b c) := by{
  unfold padd
  ring_nf
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
  ring_nf
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
      _= Complex.abs (a.x-c.x) := by ring_nf
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
    ring_nf
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
  ring_nf
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
          ring_nf
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
      _=  ({re := (x*z+y*v)/(z^2+v^2), im := (-x*v+y*z)/(z^2+v^2)} : ℂ) := by simp; ring_nf; tauto
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
  ring_nf
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
