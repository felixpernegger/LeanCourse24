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

/-As an "aribitrary point, we use the point zero:"-/

def zero : Point
  := Point.mk 0

def one : Point
  := Point.mk 1

@[simp] lemma one_neq_zero : one ≠ zero := by{
  unfold one zero
  simp
}

/- Natural definition for tangential of sets in a general manner-/
def Tangential (s v : Set Point) : Prop :=
  Set.encard (s ∩ v) = 1

/-A way to prove something is tangential is the following:-/
lemma tangential_simp_ex{s v : Set Point}(h : ∃(p : Point), p ∈ s ∧ p ∈ v ∧ (∀(q : Point), q ∈ s ∧ q ∈ v → q = p)): Tangential s v := by{
  obtain ⟨p,ps,pv,ph⟩ := h
  unfold Tangential
  apply le_antisymm
  · by_contra h0
    simp at h0
    obtain ⟨a,b,ah,bh,ab⟩ := Set.one_lt_encard_iff.1 h0
    simp at ah bh
    rw[ph a ah, ph b bh] at ab
    contradiction
  simp
  use p
  simp
  tauto
}

/-Tangential implies nonempty:-/

lemma tangential_nonempty{s v : Set Point}(h : Tangential s v): (s ∩ v).Nonempty := by{
  contrapose h
  unfold Tangential
  simp at *
  rw[not_nonempty_iff_eq_empty.mp h]
  simp
}

/-So given tangential sets we can choose a point on both of them, which is unique:-/

def Tangential_point{s v : Set Point}(h : Tangential s v) : Point :=
  (tangential_nonempty h).choose

/-This point lies in both sets:-/

lemma tangential_point_in_sets{s v : Set Point}(h : Tangential s v): Tangential_point h ∈ s ∧ Tangential_point h ∈ v := by{
  have : Tangential_point h ∈ s ∩ v := by{
    unfold Tangential_point
    exact Exists.choose_spec (tangential_nonempty h)
  }
  tauto
}

/-And unique-/

lemma tangential_point_unique{s v : Set Point}{p : Point}(h : Tangential s v)(hp: p ∈ s ∧ p ∈ v): p = Tangential_point h := by{
  have hp': p ∈ s ∩ v := by{tauto}
  have tweak: (s ∩ v).encard ≤ 1 := by{
    unfold Tangential at h
    rw[h]
  }
  apply Set.encard_le_one_iff.1 at tweak
  specialize tweak p (Tangential_point h)
  apply tweak
  · assumption
  exact (tangential_point_in_sets h)
}

/-A quick lemma we will use quite often so its nice to have it explicitly, as ring doesnt work on it:-/
lemma sub_neq_zero {a b : Point}(h: a ≠ b): a.x-b.x ≠ 0 := by{
  contrapose h
  simp at *
  ext
  calc
    a.x = a.x - 0 := by{ring}
      _= a.x - (a.x-b.x) := by{rw[h]}
      _= b.x := by{ring}
}


/- It will be convinient to multiply and add Points-/

/-Sometimes we might want to use the negatives of point (for vectors)-/

def pneg : Point → Point :=
  fun a ↦ Point.mk (-a.x)

def pmul : Point → Point → Point :=
  fun a b ↦ Point.mk (a.x * b.x)

def padd : Point → Point → Point :=
  fun a b ↦ Point.mk (a.x+b.x)

def psub : Point → Point → Point :=
  fun a b ↦ padd a (pneg b)

/-Adding zero stays constant-/
lemma padd_zero (a : Point) : padd a (Point.mk 0) = a := by{
  unfold padd
  simp
}

/-So is multipliying one:-/

@[simp] lemma pmul_one (a : Point) : pmul one a = a := by{
  unfold one pmul
  ext
  simp
}

@[simp] lemma one_pmul (a : Point) : pmul a one = a := by{
  unfold pmul one
  ext
  simp
}

@[simp] lemma pmul_zero(a : Point) : pmul a zero = zero := by{
  unfold pmul zero
  simp
}

@[simp] lemma zero_pmul(a : Point) : pmul zero a = zero := by{
  unfold pmul zero
  simp
}



/-Adding is commutative:-/
lemma padd_comm (a b : Point) : padd a b = padd b a := by{
  unfold padd
  ring_nf
}

lemma pmul_comm(a b : Point): pmul a b = pmul b a := by{
  unfold pmul
  simp
  ring
}

lemma pmul_neq_zero{a b : Point}(ah : a ≠ zero)(bh : b ≠ zero): pmul a b ≠ zero := by{
  by_contra h0
  unfold pmul zero at *
  simp at *
  obtain h0|h0 := h0
  · contrapose ah
    simp
    ext
    tauto
  contrapose bh
  simp
  ext
  tauto
}

/-And associative:-/

lemma padd_assoc (a b c : Point): padd (padd a b) c = padd a (padd b c) := by{
  unfold padd
  ring_nf
}

/-So we have an abelian group:-/

@[simp] lemma padd_neg (a : Point): padd a (pneg a) = zero := by{
  unfold zero
  unfold pneg
  unfold padd
  simp
}

def recip : Point → Point :=
  fun p ↦ Point.mk (1/p.x)

@[simp] lemma pmul_recip{a : Point}(ha: a ≠ zero): pmul a (recip a) = one := by{
  unfold pmul recip one zero at *
  have : a.x ≠ 0 := by{
    contrapose ha
    simp at *
    ext
    simp
    assumption
  }
  simp
  field_simp
}

/-Also midpoints are neat-/
def pmidpoint : Point → Point → Point :=
  fun a b ↦ Point.mk ((a.x+b.x)/2)

@[simp] lemma pmidpoint_self (a : Point) : pmidpoint a a = a := by{
  unfold pmidpoint
  ext
  ring
}

lemma pmidpoint_symm(a b : Point) : pmidpoint b a = pmidpoint a b := by{
  unfold pmidpoint
  ext
  simp
  ring
}

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

lemma point_abs_neq{a b : Point}(ab : a ≠ b): 0 < point_abs a b := by{
  by_contra h0
  simp at h0
  have : point_abs a b = 0 := by{
    apply le_antisymm
    assumption
    exact point_abs_pos a b
  }
  have : a = b := by{exact abs_zero_imp_same a b this}
  contradiction
}

lemma point_abs_neq_zero{a b : Point}(ab : a ≠ b): point_abs a b ≠ 0 := by{
  contrapose ab
  simp at *
  exact abs_zero_imp_same a b ab
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

lemma point_abs_same_sq{a b c d : Point}(h: (point_abs a b)^2 = (point_abs c d)^2): point_abs a b = point_abs c d := by{
  calc
    point_abs a b = √((point_abs a b)^2) := by{rw[pow_two, Real.sqrt_mul_self (point_abs_pos a b)]}
      _= √((point_abs c d)^2) := by{rw[h]}
      _= point_abs c d := by{rw[pow_two, Real.sqrt_mul_self (point_abs_pos c d)]}
}

lemma point_abs_pmidpoint(a b : Point): point_abs a (pmidpoint a b) = 1/2 * point_abs a b := by{
  unfold pmidpoint point_abs Complex.abs Complex.normSq
  simp
  have : ((a.x.re - (a.x.re + b.x.re) / 2) * (a.x.re - (a.x.re + b.x.re) / 2) +
      (a.x.im - (a.x.im + b.x.im) / 2) * (a.x.im - (a.x.im + b.x.im) / 2))  = (1/4) * (-2*a.x.re * b.x.re - 2*a.x.im * b.x.im + a.x.re ^ 2 + b.x.re ^ 2 +
        a.x.im ^ 2 +
      b.x.im ^ 2) := by{field_simp; ring_nf}
  rw[this]
  simp
  have :  (√4)⁻¹ = 2⁻¹ := by{
    field_simp
    refine Eq.symm ((fun {x y} ↦ Real.sqrt_eq_cases.mpr) ?_)
    left
    ring_nf
    simp
  }
  rw[this]
  ring_nf
}

lemma point_abs_scal(a b : Point)(s : ℂ): point_abs (p_scal_mul s a) (p_scal_mul s b) = Complex.abs s * point_abs a b := by{
  unfold p_scal_mul
  obtain ⟨s1,s2⟩ := s
  obtain ⟨a1,a2⟩ := a
  obtain ⟨b1,b2⟩ := b
  unfold point_abs Complex.abs Complex.normSq
  simp
  ring_nf
  calc
    √(-(s1 ^ 2 * a1 * b1 * 2) + (s1 ^ 2 * a1 ^ 2 - s1 ^ 2 * a2 * b2 * 2) + s1 ^ 2 * a2 ^ 2 + s1 ^ 2 * b1 ^ 2 +
              (s1 ^ 2 * b2 ^ 2 - a1 * s2 ^ 2 * b1 * 2) +
            (a1 ^ 2 * s2 ^ 2 - s2 ^ 2 * a2 * b2 * 2) +
          s2 ^ 2 * a2 ^ 2 +
        s2 ^ 2 * b1 ^ 2 +
      s2 ^ 2 * b2 ^ 2) = √((s1 ^ 2 + s2 ^ 2) *(-(a1 * b1 * 2) + (a1 ^ 2 - a2 * b2 * 2) + a2 ^ 2 + b1 ^ 2 + b2 ^ 2)) := by{ring_nf}
        _= √(s1^2+s2^2) * √(-(a1 * b1 * 2) + (a1 ^ 2 - a2 * b2 * 2) + a2 ^ 2 + b1 ^ 2 + b2 ^ 2) := by{
          rw[Real.sqrt_mul]
          nlinarith
        }
}

/-The absolute value of a point is the obvious thing:-/
def pabs : Point → ℝ :=
  fun a ↦ Complex.abs a.x

/-This is zero iff a is zero:-/
lemma pabs_zero (a : Point) : pabs a = 0 ↔ a = Point.mk 0 := by{
  unfold pabs
  simp
  constructor
  intro h
  ext
  simp
  assumption

  intro h
  rw[h]
}

/-The "direction" two point is the normed vector between them:-/
def dir: Point → Point → Point :=
  fun a b ↦ Point.mk ((b.x-a.x)/ (point_abs a b))

@[simp] lemma dir_self(a : Point): dir a a = zero := by{
  unfold dir zero
  simp
}

/-The direction is zero iff a = b:-/
lemma dir_zero (a b : Point): pabs (dir a b) = 0 ↔ a = b := by{
  constructor
  intro h
  apply (pabs_zero (dir a b)).1 at h
  unfold dir at h
  simp at *
  obtain h|h := h
  ext
  calc
    a.x = a.x + 0 := by{ring}
      _=a.x + (b.x - a.x) := by{rw[h]}
      _= b.x := by{ring}

  apply abs_zero_imp_same a b at h
  assumption

  intro h
  rw[h]
  clear h
  unfold dir
  simp
  unfold pabs
  simp
}

/-Otherwise the direction has abosulte value 1:-/
lemma dir_one {a b : Point}(h : a ≠ b): pabs (dir a b) = 1 := by{
  unfold dir pabs
  rw[point_abs_symm  a b]
  unfold point_abs
  simp
  have : Complex.abs (b.x - a.x) ≠ 0 := by{
    contrapose h
    simp at *
    symm
    ext
    assumption
  }
  field_simp
}

/-dir is antisymmetric:-/
lemma dir_antisymm(a b : Point): dir b a = pneg (dir a b) := by{
  unfold dir pneg
  simp
  rw[point_abs_symm b a]
  field_simp
}

def pconj : Point → Point :=
  fun a ↦ Point.mk (conj a.x)

/-Mirroring twice gives original:-/

@[simp] lemma pconj_twice (a : Point) : pconj (pconj a) = a := by{
  unfold pconj
  simp
}

@[simp] lemma pconj_zero: pconj zero = zero := by{
  unfold zero pconj conj
  simp
}

lemma pconj_point_abs(a b : Point): point_abs (pconj a) (pconj b) = point_abs a b := by{
  unfold pconj conj point_abs Complex.abs Complex.normSq
  simp
  ring_nf
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

lemma det_zero_detproper{a b c : ℂ}(h: det (Point.mk a) (Point.mk b) (Point.mk c) = 0): detproper a (conj a) 1 b (conj b) 1 c (conj c) 1 = 0:= by{
  rw[det_detproper] at h
  simp at h
  have : (detproper a (conj a) 1 b (conj b) 1 c (conj c) 1).re = 0 := by{
    unfold detproper conj
    simp
    ring
  }
  calc
    (detproper a (conj a) 1 b (conj b) 1 c (conj c) 1) =({re := (detproper a (conj a) 1 b (conj b) 1 c (conj c) 1).re , im := (detproper a (conj a) 1 b (conj b) 1 c (conj c) 1).im}:ℂ) := by{exact rfl}
      _= ({re := 0, im := 0}:ℂ) := by{rw[h,this]}
      _= 0 := rfl
}

def colinear (a b c : Point) : Prop :=
  det a b c = 0

def noncolinear (a b c : Point) : Prop :=
  ¬colinear a b c

/-An alternative very useful notion will be given shortly -/

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

lemma noncolinear_self(a b c : Point)(h: noncolinear a b c): a ≠ b ∧ b ≠ c ∧ c ≠ a := by{
  contrapose h
  unfold noncolinear
  simp at *
  apply colinear_self a b
  tauto
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

@[simp] lemma wtf5(x y : ℝ): -({re := x, im := y}:ℂ) = ({re := -x, im := -y}:ℂ) := by{
  have : (-1 : ℂ) = ({re := -1, im := 0}:ℂ) := by{
    refine Complex.ext_iff.mpr ?_
    simp
  }
  calc
    -({re := x, im := y}:ℂ)= -1 * ({re := x, im := y}:ℂ) := by{ring}
      _= ({re := -1, im := 0}:ℂ)*({re := x, im := y}:ℂ) := by{rw[this]}
      _= ({re := -x, im := -y}:ℂ) := by{simp}
}

@[simp] lemma wtf6(x y: ℝ): 2*({re := x, im := y}:ℂ)={re := 2*x, im := 2*y} := by{
  have : 2 = ({re := 2, im := 0}:ℂ) := by{exact rfl}
  rw[this]
  simp
}

@[simp] lemma wtf7(x y : ℝ): ({re := x, im := y}:ℂ)/2 = ({re := x/2, im := y/2}:ℂ) := by{
  have : ({re := x, im := y}:ℂ)/2 = 1/2 * ({re := x, im := y}:ℂ) := by{ring}
  rw[this]
  norm_cast
  have : 1/2 = ({re := 1/2, im := 0}:ℂ) := by{
    refine Eq.symm (eq_one_div_of_mul_eq_one_right ?h)
    rw[wtf6]
    ring_nf
    rfl
  }
  rw[this]
  simp
  ring_nf
  tauto
}

lemma pmidpoint_same_imp_same_left{a b : Point}(h : pmidpoint a b = a): a = b := by{
  obtain ⟨a1,a2⟩ := a
  obtain ⟨b1,b2⟩ := b
  unfold pmidpoint at h
  simp at *
  obtain ⟨h1,h2⟩ := h
  constructor
  linarith
  linarith
}

lemma pmidpoint_same_imp_same_right{a b : Point}(h : pmidpoint a b = b): a = b := by{
  symm
  rw[pmidpoint_symm] at h
  exact pmidpoint_same_imp_same_left h
}

lemma pmidpoint_diff_left{a b : Point}(ab : a ≠ b): pmidpoint a b ≠ a := by{
  contrapose ab
  simp at *
  exact (pmidpoint_same_imp_same_left ab)
}

lemma pmidpoint_diff_right{a b : Point}(ab : a ≠ b): pmidpoint a b ≠ b := by{
  contrapose ab
  simp at *
  exact (pmidpoint_same_imp_same_right ab)
}

/-As a preview to similar triangles, note the following:-/
lemma point_abs_pmidpoint_pmidpoint(a b p): point_abs (pmidpoint p a) (pmidpoint p b) = 1/2 * point_abs a b := by{
  have g: point_abs (pmidpoint p a) (pmidpoint p b) = point_abs (p_scal_mul (1/2) a) (p_scal_mul (1/2) b) := by{
    unfold pmidpoint p_scal_mul point_abs
    simp
    ring_nf
  }
  rw[g, point_abs_scal a b (1/2)]
  simp
}


/-The alternative (nonsymmetric) notion of colinear is now the following:-/
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

/-Fun fact: I originally did this prove without colinear_alt (so with determinants).
That took me about 300 lines of awful calculations and a week of work.
Luckily I saw the light!-/
