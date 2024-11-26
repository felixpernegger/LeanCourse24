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

/-So we have an abelina group:-/

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

lemma conj_add (x:ℂ) (y:ℂ) : conj (x+y) = conj x + conj y := by{
  unfold conj
  exact RingHom.map_add (starRingEnd ℂ) x y
}

lemma conj_mul' (x:ℂ) (y:ℂ) : conj (x*y) = (conj x) * (conj y) := by{
  unfold conj
  exact RingHom.map_mul (starRingEnd ℂ) x y
}

/-conjugating twice is self:-/

lemma conj_twice (x : ℂ) : conj (conj x) = x := by{
  unfold conj
  simp
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

lemma pconj_twice (a : Point) : pconj (pconj a) = a := by{
  unfold pconj
  simp
  rw[conj_twice]
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
  repeat
    rw[conj_twice]
  ring
}

def colinear (a b c : Point) : Prop :=
  det a b c = 0

def noncolinear (a b c : Point) : Prop :=
  ¬colinear a b c

/- This notion of colinearity is the same as the usual one:-/

/-I know this is a bit assymetric and could probably could use better notation, but we won't ever
use this, so it really doesnt matter all that much-/

theorem colinear_def {a b c : Point}: (noncolinear a b c) ↔ (∀ u v : ℝ, (↑u * (a.x-b.x) + ↑v * (a.x-c.x)  = 0) → (u=0 ∧ v=0)) := by{
  obtain ⟨a1,a2⟩ := a
  obtain ⟨b1,b2⟩ := b
  obtain ⟨c1,c2⟩ := c
  unfold noncolinear
  unfold colinear
  unfold det
  unfold conj
  simp at *
  constructor
  intro h u v uv
  simp at *
  --obtain ⟨uv1,uv2⟩ := uv
  sorry
  intro uv h
  contrapose uv
  simp at *
  clear uv
  sorry
}

lemma colinear_ex {a b c : Point}(h: colinear a b c) : ∃ u v : ℝ, ¬(u=0 ∧ v=0) ∧ (↑u * (a.x-b.x) + ↑v * (a.x-c.x)  = 0) :=by{
  by_contra p
  push_neg at p
  have : noncolinear a b c := by{
    apply colinear_def.2
    intro u v h
    specialize p u v
    tauto
  }
  tauto
}

/-Above is wrong lol maybe-/

--lemma colinear_alt (a:Point)(b: Point)(c:Point)(h: a≠ b ∧ b≠ c ∧ c≠ a): colinear a b c ⇔ (a.x-b.x)/()


/-The following took me over a week (!) to formalise. It is extremely gruesome and mostly brute force calculations with determinants
However it is central for everything else. Maybe one can simplify the proof significantly, i do not know -/

lemma colinear_trans (a b c d : Point)(h: colinear a b c) (h': colinear a b d)(nab: a ≠ b):  colinear b c d := by{
  unfold colinear at *
  unfold det at *
  unfold conj at *
  obtain ⟨x,y⟩ := a
  obtain ⟨z,v⟩ := b
  obtain ⟨n,m⟩ := c
  obtain ⟨k,r⟩ := d
  simp at *
  ring
  have hs: x * (m - v) + y * (z - n) + (v*n -z*m) = 0 := by{linarith}
  clear h
  have h's: x * (r - v) + y * (z - k) + (v*k - z*r) = 0 := by{linarith}
  clear h'
  have goal: z* (r - m) + v * (n -  k) + m * k - n * r = 0 := by{
    by_cases p : x = z
    specialize nab p
    rw[p] at hs
    rw[p] at h's
    have hsn : z * (y-v) + v*n + y * - n = 0 := by{linarith}
    have h'sn : z * (y-v) + v * k + y * -k = 0 := by{linarith}
    clear p
    clear hs
    clear h's
    have yz : y-v≠ 0 := by{exact sub_ne_zero_of_ne nab}
    clear nab
    have eg: v * n + y* -n = v * k + y * -k := by{linarith}
    have: v * (n-k) = y * (n-k) := by{linarith}
    by_cases nk: n = k
    clear hsn
    rw[nk]
    simp
    clear this nk eg
    have : z * (y-v) - k * (y-v) = 0 := by{linarith}
    have : (z-k)*(y-v)=0 := by{linarith}
    have : z-k = 0 := by{exact eq_zero_of_ne_zero_of_mul_right_eq_zero yz this}
    have : z = k := by{linarith}
    rw[this]
    linarith

    have nnk : n -k ≠ 0 := by{
      by_contra nk
      have : n=k := by{linarith}
      contradiction
      }
    have vy : v = y := by{
      calc
        v = v * 1 := by linarith
          _= v * ((n-k)/(n-k)) := by field_simp
          _= (v* (n-k))/ (n-k) := by field_simp
          _= (y * (n-k)) / (n-k) := by rw[this]
          _= y := by field_simp
    }
    have : y - v = 0 := by {linarith}
    contradiction

    clear nab
    have t: x * (m - r) + y * (k-n) + (v * n - z * m) - (v * k - z * r) = 0 := by{
      calc
        x * (m - r) + y * (k-n) + (v * n - z * m) - (v * k - z * r) = x * (m - v) + y * (z - n) + (v * n - z * m) - (x * (r - v) + y * (z - k) + (v * k - z * r)) := by ring
          _= 0 - 0 := by{rw[hs,h's]}
          _= 0 := by ring
    }
    have : x * (m - r) + y * (k - n) + (v * n - z * m) - (v * k - z * r) = (x -z)*(m-r) + (y - v)* (k-n) := by ring
    rw[this] at t
    clear this
    have : x*(r-m) + y * (n -k) = z*(r-m) + v *(n-k) := by{linarith}
    rw[← this]
    by_cases rm: r=m
    rw[rm] at h's
    rw[rm] at this
    rw[rm] at t
    rw[rm]
    simp at *
    clear rm
    clear t
    obtain h|h := this
    symm at h
    rw[h] at hs
    rw[h] at h's
    clear h
    clear h's
    have : (x-z)*(m-y)= 0 := by{linarith}
    simp at this
    obtain h|h := this
    have : x = z := by{linarith}
    contradiction

    have : m = y := by{linarith}
    rw[this]
    linarith

    have : k = n := by{linarith}
    rw[this]
    linarith



    by_cases mv: m=v
    symm at mv
    rw[mv] at hs
    rw[mv] at h's
    rw[mv] at this
    clear mv
    simp at *
    have tt: (y-m)*(z-n)=0 := by{linarith}
    clear hs
    simp at tt
    obtain h|h := tt
    have ff: y = m := by{linarith}
    rw[ff] at h's
    rw[ff] at t
    clear h
    clear ff
    have xf: (x-z)*(r-m)=0 := by{linarith}
    simp at xf
    obtain u|u := xf
    have : x=z := by{linarith}
    contradiction
    have : r=m := by{linarith}
    contradiction

    have pf: z = n := by{linarith}
    rw[pf] at h's
    rw[pf] at p
    rw[pf] at t
    rw[pf] at this
    clear h
    clear pf
    have oje: n * (r - m) + m * (n - k) = n*r-m*k := by ring
    rw[oje] at this
    rw[this]
    ring
    clear this
    have : (x-z)*(r-m) = (y-v)*(k-n) := by{
      calc
        (x-z)*(r-m) = (x-z)*(r-m) + 0 := by ring
          _= (x-z)*(r-m) + ((x - z) * (m - r) + (y - v) * (k - n)) := by rw[t]
          _= ((x-z)*(r-m) + (x - z) * (m - r)) + (y - v) * (k - n) := by ring
          _= (y-v)*(k-n) := by ring
    }
    have rms : r-m ≠ 0 := by{
      by_contra helpme
      have : r = m := by{linarith}
      contradiction
    }
    have : x-z = (y-v)*(k-n)/(r-m) := by{field_simp; assumption}
    have xx: x = z + (y - v) * (k - n) / (r - m) := by linarith
    rw[xx] at t
    rw[xx] at hs
    rw[xx] at h's
    rw[xx]
    rw[xx] at p
    clear xx
    clear this
    clear this
    simp at *
    have : (z + (y - v) * (k - n) / (r - m)) * (r - m) = z*(r-m) + (y-v)*(k-n) := by{field_simp}
    rw[this]
    clear this
    have :  z * (r - m) + (y - v) * (k - n) + y * (n - k) + m * k - n * r = z*(r-m)+v*n-v*k+m*k-n*r := by ring
    rw[this]
    clear this
    have mvs : m-v≠ 0 := by{
      by_contra mvs
      have : m=v := by{linarith}
      contradiction
    }
    clear t
    have : (z + (y - v) * (k - n) / (r - m)) * (m - v) + y * (z - n) + (v * n - z * m) = z*(y-v)+((y-v)*(k-n)*(m-v))/(r-m)-y*n+v*n := by{field_simp;ring}
    rw[this] at hs
    clear this
    have yvs : y-v≠ 0 := by exact p.1.1
    have : z*(y-v) = -((y - v) * (k - n) * (m - v) / (r - m) - y * n + v * n) := by linarith
    have zz: z = -((y - v) * (k - n) * (m - v) / (r - m) - y * n + v * n) / (y-v) := by{
      calc
        z = z * (y-v) / (y-v) := by field_simp
          _= -((y - v) * (k - n) * (m - v) / (r - m) - y * n + v * n) / (y-v) := by rw[this]
    }
    clear this
    clear hs
    rw[zz] at h's
    rw[zz]
    clear zz
    simp at *
    field_simp
    ring
    }
  linarith
  }

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

/- Lets define parallel lines. We say a line is parallel to itself, so we can get a nice equivalence relation-/
def Parallel(L R : Line) : Prop :=
  L.range ∩ R.range = ∅ ∨ L.range = R.range

lemma parallel_refl (L : Line) : Parallel L L := by{
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
      tauto
      right
      exact Set.encard_eq_one.2 p
    }
    obtain this|this := this
    have : (L.range ∩ R.range = ∅) := by exact encard_eq_zero.mp this
    have : Parallel L R := by{
      unfold Parallel
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

/-do this with Exists.choose_spec somehow-/
lemma intersection_mem {L R : Line}(LR : ¬ Parallel L R) : Lies_on (Intersection LR) L ∧ Lies_on (Intersection LR) R := by{
  sorry
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
  unfold Parallel at *
  obtain h|h := h
  · left
    rw[Set.inter_comm]
    assumption
  · right
    symm
    assumption
}

lemma parallel_trans {L R S : Line}(LR : Parallel L R)(RS : Parallel R S) : Parallel L S := by{
  by_contra p
  unfold Parallel at *
  push_neg at p
  obtain LR|LR := LR
  swap
  have : L = R := by{
    ext x
    rw[LR]
  }
  rw[this] at p
  clear LR
  clear this
  obtain ⟨p1,p2⟩ := p
  obtain RS|RS := RS
  rw[RS] at p1
  obtain ⟨a,ah⟩ := p1
  contradiction
  contradiction

  obtain RS|RS := RS
  obtain ⟨p1,p2⟩ := p


  swap
  have : R=S := by{
    ext
    rw[RS]
  }
  rw[this] at LR
  obtain ⟨p1,p2⟩ := p
  rw[LR] at p1
  obtain ⟨a,ah⟩ := p1
  contradiction

  obtain ⟨s,sh⟩ := p1
  sorry


}

/-Note: I should probably redo this section a bit, define parallel_through first and then use it
for weak_parallel_postulate. Else everyhting is quite redundant-/

lemma weak_parallel_postulate (L : Line)(a : Point) : ∃ Q : Line, Lies_on a Q ∧ Parallel L Q := by{
  by_cases h0: Lies_on a L
  use L
  constructor
  assumption
  exact parallel_refl L

  obtain ⟨S,u,v,uv,h⟩ := L
  let p := Point.mk (a.x+u.x-v.x)
  unfold Lies_on at h0
  simp at h0
  have ap: a ≠ p := by{
    contrapose uv
    simp at *
    have : a.x = a.x + u.x - v.x := by{
      exact congrArg Point.x uv
    }
    have : u.x-v.x = 0 := by
      calc
        u.x-v.x = -a.x +(a.x + u.x - v.x) := by ring
          _= -a.x + a.x := by rw[← this]
          _= 0 := by ring
    ext
    calc
      u.x = u.x - 0 := by ring
        _= u.x - (u.x - v.x) := by rw[this]
        _= v.x := by ring
  }
  use Line_through ap
  constructor
  exact line_through_mem_left ap
  unfold Parallel
  left
  simp
  unfold Line_through
  rw[h]
  simp
  ext o
  constructor
  swap
  intro cc
  contradiction
  intro oh
  simp at *
  contrapose h0
  rw[h]
  simp at *
  clear h0
  clear h
  clear S
  obtain ⟨h1,h2⟩ := oh
  apply colinear_perm13 at h1
  apply colinear_perm13 at h2
  have goal: colinear o v a := by{
    unfold p at h2
    unfold p at ap
    clear p
    unfold colinear at *
    unfold det at *
    unfold conj at *
    obtain ⟨x,y⟩ := a
    obtain ⟨g,b⟩ := u
    obtain ⟨c,d⟩ := o
    obtain ⟨e,f⟩ := v
    simp at *
    ring_nf
    have : - (c * f) + (c * y) + (f * x) + (d * e) - (d * x) - (e * y) = 0 := by{
      have ha: - (c * f) + (d * e) - (g * d) + (b * c) - (e * b) + (f * g) = 0 := by{linarith}
      clear h1
      have hb: -(c*y) -(b*c)+(c*f)+(d*x)+(d*g)-(d*e)-(x*d)+(y*c)-(x*y)-(g*y)+(e*y)+(y*x)+(b*x)-(f*x) = 0 := by{linarith}
      clear h2
      sorry
      }
    linarith
    }
  apply colinear_perm12
  by_cases ov : o=v
  swap
  apply colinear_trans o v u a h1 goal
  assumption

  rw[ov] at h1
  rw[ov] at h2
  rw[ov] at goal
  clear h1
  clear goal
  clear ov
  clear o
  unfold p at h2
  apply colinear_perm23
  apply colinear_perm23 at h2
  apply colinear_perm12
  apply (colinear_add a v u).2
  apply colinear_perm12
  have : u.x + a.x - v.x = a.x + u.x - v.x := by ring
  rw[this]
  assumption
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
  exfalso
  unfold Lies_on at *
  have : a ∈ U.range ∧ a ∈ R.range := by{
    constructor
    exact Uh.1
    exact Rh.1
  }
  have : a ∈ U.range ∩ R.range := by exact this
  rw[h] at this
  contradiction

  exact Line.ext_iff.mpr (id (Eq.symm h))

  exfalso
  obtain ⟨_,hU⟩ := Uh
  obtain ⟨_,hR⟩ := Rh
  have : Parallel U R := by{
    apply parallel_symm at hU
    exact parallel_trans hU hR
  }
  contradiction
}

/-This is NOT THE WAY-/

def parallel_through : Line → Point → Line :=
  fun L a ↦ (parallel_postulate L a).choose

/-This indeed is a parallel to the original Line:-/

lemma parallel_through_is_parallel (L : Line)(a : Point) : Parallel L (parallel_through L a) := by{
  unfold parallel_through
  sorry
}

/- And the point lies on the Line:-/

lemma parallel_through_on_line (L : Line)(a : Point) : Lies_on a (parallel_through L a) := by{
  unfold parallel_through
  sorry
}
/-Old Section about sLine (Line as a function ew)
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
    apply colinear_perm13 at bcd
    apply colinear_perm12 at bcd
    have bdx: colinear d b x := by exact colinear_trans c d b x bcd u h'
    apply colinear_perm13 at hd
    by_cases p: d=b
    rw[p] at u
    rw[p] at h'
    clear bdx bcd hd
    apply colinear_perm13 at hc
    apply colinear_perm12
    exact colinear_trans c b a x hc u h'

    apply colinear_perm12
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

-/


/- Natural definition for tangential-/
def Tangential (s v : Set Point) : Prop :=
  Set.encard (s ∩ v) = 1

/-Now we feel confident enough to finally define Triangles-/

@[ext] structure Triangle where
  a : Point
  b : Point
  c : Point
  notline : noncolinear a b c

/- We will use the lenghts of sides of triangles often-/

def tri_ab: Triangle → ℝ :=
  fun T ↦ (point_abs T.a T.b)

def tri_bc: Triangle → ℝ :=
  fun T ↦ (point_abs T.b T.c)

def tri_ca: Triangle → ℝ :=
  fun T ↦ (point_abs T.c T.a)

/-We can shift and scale Triangles:-/
lemma tri_shift_lemma (T : Triangle)(p : Point): noncolinear (padd T.a p) (padd T.b p) (padd T.c p) := by{
  exact noncolinear_shift p T.notline
}

def tri_shift : Triangle → Point → Triangle :=
  fun T p ↦ Triangle.mk (padd T.a p) (padd T.b p) (padd T.c p) (tri_shift_lemma T p)

/-shifting by zero stays constant:-/

lemma tri_shift_zero (T : Triangle) : tri_shift T (Point.mk 0) = T := by{
  unfold tri_shift
  simp [padd_zero]
}

lemma tri_shift_padd (T : Triangle) (p q : Point) : tri_shift T (padd p q) = tri_shift (tri_shift T p) q := by{
  unfold tri_shift
  simp [padd_assoc]
}

--to do : scale

/-Similarly we can mirror/conjugate Triangles:-/
lemma tri_conj_lemma (T : Triangle) : noncolinear (pconj T.a) (pconj T.b) (pconj T.c) := by{
  exact noncolinear_conj T.notline
}

def tri_conj : Triangle → Triangle :=
  fun T ↦ Triangle.mk (pconj T.a) (pconj T.b) (pconj T.c) (tri_conj_lemma T)

/-Mirroring twice gives the same-/

lemma tri_conj_twice (T : Triangle) : tri_conj (tri_conj T) = T := by{
  unfold tri_conj
  simp [pconj_twice]
}

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

def centroid : Triangle → Point :=
  fun T ↦ Point.mk ((T.a.x+T.b.x+T.c.x)/3)

lemma midtriangle_noncolinear (T : Triangle): noncolinear (Point.mk ((T.b.x+T.c.x)/2)) (Point.mk ((T.c.x+T.a.x)/2)) (Point.mk ((T.a.x + T.b.x)/2)) := by{
  obtain ⟨a,b,c,h⟩ := T
  obtain ⟨a1,a2⟩ := a
  obtain ⟨b1,b2⟩ := b
  obtain ⟨c1,c2⟩ := c
  simp at *
  unfold noncolinear at *
  unfold colinear at *
  unfold det at *
  unfold conj at *
  unfold starRingEnd at *
  simp at *
  contrapose h
  push_neg at *
  linarith
}

def midtriangle : Triangle → Triangle :=
  fun T ↦ Triangle.mk (Point.mk ((T.b.x+T.c.x)/2)) (Point.mk ((T.c.x+T.a.x)/2)) (Point.mk ((T.a.x + T.b.x)/2)) (midtriangle_noncolinear T)

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
    apply colinear_perm13
    apply colinear_perm12
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
  --if noncolinear a b c ∨ noncolinear a

  /-def Circumcircle (a b c : Point) : Set Point :=
  if h : colinear a b c then
    if a = b ∨ b = c ∨ c = a then ∅
    else sLine a b
  sorry
  --else by
    --{let z := ex_circumcircle a b c (by { unfold noncolinear; assumption }) sorry --???? Circle1 z.1 z.2
-/

/- A crucial definition in planar geometry are similar triangles:-/
/- Similar means same rotation as here well! This helps us deal better with area. "Antisimilarity" will be introduced after-/

/- I want to redo oldSimilar with scaling-/

def oldSimilar (T Q : Triangle) : Prop :=
  ∃z : ℂ, (z* T.a.x = Q.a.x) ∧ (z* T.b.x = Q.b.x) ∧ (z* T.c.x = Q.c.x)

/-For more general cases, see Similar and direct Similar.-/
/-Note that the scaling factor cant be 0:-/
lemma oldsimilar_neq_zero {T Q : Triangle}(z : ℂ)(zh : (z* T.a.x = Q.a.x) ∧ (z* T.b.x = Q.b.x) ∧ (z* T.c.x = Q.c.x)) : z≠ 0 := by{
  by_contra p
  rw[p] at zh
  simp at zh
  obtain ⟨a,b,c, q⟩ := Q
  simp at zh
  unfold noncolinear at q
  unfold colinear at q
  unfold det at q
  unfold conj at q
  push_neg at q
  obtain ⟨zh1,zh2,zh3⟩ := zh
  rw[← zh1 ,← zh2,← zh3] at q
  simp at q
}

/-Lets show being oldsimilar is an equivalence relation:-/

lemma oldsimilar_refl (T : Triangle) : oldSimilar T T := by{
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
  sorry
}

/-The version of Similar triangles actually useable are the following:-/

/-direct similar means, we cannont mirror (this preserves directed area and angles)-/

def directSimilar (T Q : Triangle) : Prop :=
  ∃p : Point, oldSimilar (tri_shift T p) (tri_shift Q p)

/-directSimilar is weaker than oldSimilar:-/

lemma oldsimilar_imp_directsimilar {T Q : Triangle} (h: oldSimilar T Q) : directSimilar T Q := by{
  use Point.mk 0
  rw[tri_shift_zero,tri_shift_zero]
  assumption
}

/-This again is a equivalence relation:-/

lemma directsimilar_refl (T : Triangle) : directSimilar T T :=  by{
  use Point.mk 0
  rw[tri_shift_zero]
  exact oldsimilar_refl T
}

lemma directsimilar_symm {T Q : Triangle} (h: directSimilar T Q) : directSimilar Q T := by{
  sorry
}

lemma directsimilar_trans{T Q R : Triangle}(TQ : directSimilar T Q)(QR: directSimilar Q R) : directSimilar T R := by{
  sorry
}
/-Mirrorring is cool:-/
lemma directsimilar_conj (T Q : Triangle) : directSimilar T Q ↔ directSimilar (tri_conj T) (tri_conj Q) := by{
  sorry
}

/-Antisimilar is now define as being similar to the mirrored:-/

def antiSimilar (T Q : Triangle) : Prop :=
  directSimilar T (tri_conj Q)

/-AntiSimilar is a bit more awkward:-/
lemma antisimilar_pseudo_refl (T: Triangle) : antiSimilar T (tri_conj T) := by{
  unfold antiSimilar
  rw[tri_conj_twice]
  exact directsimilar_refl T
}

lemma antisimilar_symm {T Q : Triangle}(h : antiSimilar T Q) : antiSimilar Q T := by{
  unfold antiSimilar at *
  apply directsimilar_symm
  apply (directsimilar_conj (tri_conj T) Q).2
  rw[tri_conj_twice]
  assumption
}

lemma antisimilar_pseudo_trans {T Q R : Triangle}(TQ: antiSimilar T Q)(QR : antiSimilar Q R) : directSimilar T R := by{
  unfold antiSimilar at *
  have : directSimilar (tri_conj Q) R := by{
    rw[← tri_conj_twice R]
    exact (directsimilar_conj Q (tri_conj R)).1 QR
  }
  exact directsimilar_trans TQ this
}

/-the usual definition of Similar is the following:-/

def Similar (T Q : Triangle) : Prop :=
  directSimilar T Q ∨ antiSimilar T Q

/- Similar is weaker than antiSimilar, directSimilar and oldSimilar:-/

lemma antisimilar_imp_similar {T Q : Triangle}(h: antiSimilar T Q) : Similar T Q := by{
  right
  assumption
}

lemma directsimilar_imp_similar {T Q : Triangle}(h: directSimilar T Q) : Similar T Q := by{
  left
  assumption
}

lemma oldsimilar_imp_similar {T Q : Triangle}(h: oldSimilar T Q) : Similar T Q := by{
  apply directsimilar_imp_similar
  exact oldsimilar_imp_directsimilar h
}

/-once again being Similar is an equivalence relation:-/

/-first following may be useful:-/
lemma similar_conj {T Q : Triangle} (h: Similar T Q) : Similar T (tri_conj Q) := by{
  unfold Similar at *
  obtain h|h := h
  right
  unfold antiSimilar
  rw[tri_conj_twice]
  assumption
  unfold antiSimilar at h
  left
  assumption
}

lemma similar_refl (T : Triangle) : Similar T T := by{
  unfold Similar
  left
  exact directsimilar_refl T
}

lemma similar_symm {T Q : Triangle}(h : Similar T Q) : Similar Q T := by{
  sorry
}

lemma similar_trans {T Q R : Triangle}(TQ : Similar T Q)(QR : Similar Q R) : Similar T R := by{
  sorry
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

lemma ex_circumcircle {a b c : Point} (h : noncolinear a b c) :
  ∃! z : (Point × ℝ), {a,b,c} ⊆ Circle1 z.1 z.2 := by{
    sorry
  }


/-def Circumcircle (a b c : Point) : Set Point :=
  if h : colinear a b c then
    if a = b ∨ b = c ∨ c = a then ∅
    else sLine a b
  sorry
  --else by
    --{let z := ex_circumcircle a b c (by { unfold noncolinear; assumption }) sorry --???? Circle1 z.1 z.2
-/-/
