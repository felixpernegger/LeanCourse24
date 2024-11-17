/- It is fine to import all of Mathlib in your project.
This might make the loading time of a file a bit longer. If you want a good chunk of Mathlib, but not everything, you can `import Mathlib.Tactic` and then add more imports as necessary. -/
import Mathlib

/- open namespaces that you use to shorten names and enable notation. -/
open Function Set Classical

/- recommended whenever you define anything new. -/
noncomputable section

/- Now write definitions and theorems. -/


@[ext] structure Point where
  x : ℂ

def pmul : Point → Point → Point :=
  fun a b ↦ Point.mk (a.x * b.x)

def padd : Point → Point → Point :=
  fun a b ↦ Point.mk (a.x+b.x)

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


def pconj : Point → Point :=
  fun a ↦ Point.mk (conj a.x)

def det : Point → Point → Point → ℂ :=
  fun a b c ↦ a.x * (conj b.x) + c.x * (conj a.x) + b.x * (conj c.x) - a.x * (conj c.x) - c.x * (conj b.x) - b.x * (conj a.x)

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

def nonlinear (a b c : Point) : Prop :=
  ¬linear a b c

--lemma linear_alt (a:Point)(b: Point)(c:Point)(h: a≠ b ∧ b≠ c ∧ c≠ a): linear a b c ⇔ (a.x-b.x)/()

lemma linear_trans (a b c d : Point)(h: linear a b c) (h': linear a b d)(nab: a ≠ b):  linear b c d := by{
  unfold linear at *
  unfold det at *
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

lemma same_line_imp_colinear(a b c : Point)(h : Line a b = Line b c) : linear a b c := by{
  have : c ∈ Line a b := by{
    rw[h]
    exact (self_in_line b c).2
  }
  exact mem_line_colinear a b c this
}

def Circle1 : Point → ℝ → Set Point :=
  fun z R ↦ {a : Point | point_abs z a = R}

lemma circle_of_neg_rad (z : Point)(R : ℝ)(h : R < 0): Circle1 z R = ∅ := by{
  unfold Circle1
  sorry
}

lemma circle_of_pos_rad_nonempty (z : Point)(R : ℝ)(h : 0≤ R): Set.Nonempty (Circle1 z R) := by{
  use Point.mk (z.x + R)
  unfold Circle1
  simp
  unfold point_abs
  simp
  assumption
}

lemma circle_unique (z z' : Point)(R R' : ℝ)(h : Circle1 z R = Circle1 z' R')(h' : R≥ 0): z = z' ∧  R = R' := by{
  by_cases p: R'<0
  have : Circle1 z' R' = ∅ := by{
    exact circle_of_neg_rad z' R' p
  }
  rw[this] at h
  have : Set.Nonempty (Circle1 z R) := by{exact circle_of_pos_rad_nonempty z R h'}
  apply Set.nonempty_iff_ne_empty.1 at this
  tauto

  simp at p




}

lemma ex_circumcircle (a b c : Point) (h : nonlinear a b c) :
  ∃! z : (Point × ℝ), {a,b,c} ⊆ Circle1 z.1 z.2 := by{
    sorry
  }


def Circumcircle (a b c : Point) : Set Point :=
  if h : linear a b c then
    if a = b ∨ b = c ∨ c = a then ∅
    else Line a b
  else by
    {let z := ex_circumcircle a b c (by { unfold nonlinear; assumption }) sorry --???? Circle1 z.1 z.2

@[ext] structure Triangle where
  a : Point
  b : Point
  c : Point
  notline : nonlinear a b c
