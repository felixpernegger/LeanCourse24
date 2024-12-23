import LeanCourse.Project.qObject
import Mathlib

open Function Set Classical

noncomputable section


/-Now we feel confident enough to finally define Triangles-/

@[ext] structure Triangle where
  a : Point
  b : Point
  c : Point
  noncolinear : noncolinear a b c

/- We will use the lenghts of sides of triangles often-/

def abs_tri_ab: Triangle → ℝ :=
  fun T ↦ (point_abs T.a T.b)

def abs_tri_bc: Triangle → ℝ :=
  fun T ↦ (point_abs T.b T.c)

def abs_tri_ca: Triangle → ℝ :=
  fun T ↦ (point_abs T.c T.a)

/-The points of the Triangle are disjoint.-/
lemma tri_disj (T : Triangle): T.a ≠ T.b ∧ T.b ≠ T.c ∧ T.c ≠ T.a := by{
  obtain ⟨a,b,c,h⟩ := T
  simp
  contrapose h
  unfold noncolinear
  simp
  push_neg at h
  have h' : a = b ∨ b = c ∨ c = a :=by{tauto}
  obtain h'|h'|h' := h'
  repeat
    unfold colinear
    apply det_self
    tauto
}

/-using this we can quickly acces the sides of a triangle:-/
def tri_ab : Triangle → Line :=
  fun T ↦ Line_through (tri_disj T).1

def tri_bc : Triangle → Line :=
  fun T ↦ Line_through (tri_disj T).2.1

def tri_ca : Triangle → Line :=
  fun T ↦ Line_through (tri_disj T).2.2

/-As usual, the points indeed lie on the lines...-/
lemma tri_a_on_ab (T : Triangle): Lies_on T.a (tri_ab T) := by{
  unfold tri_ab
  exact line_through_mem_left (tri_disj T).1
}

lemma tri_b_on_ab (T : Triangle): Lies_on T.b (tri_ab T) := by{
  unfold tri_ab
  exact line_through_mem_right (tri_disj T).1
}

lemma tri_b_on_bc (T : Triangle): Lies_on T.b (tri_bc T) := by{
  unfold tri_bc
  exact line_through_mem_left (tri_disj T).2.1
}

lemma tri_c_on_bc (T : Triangle): Lies_on T.c (tri_bc T) := by{
  unfold tri_bc
  exact line_through_mem_right (tri_disj T).2.1
}

lemma tri_c_on_ca (T : Triangle): Lies_on T.c (tri_ca T) := by{
  unfold tri_ca
  exact line_through_mem_left (tri_disj T).2.2
}

lemma tri_a_on_ca (T : Triangle): Lies_on T.a (tri_ca T) := by{
  unfold tri_ca
  exact line_through_mem_right (tri_disj T).2.2
}

/-Annnnd also from definition c doesnt lie on a b etc-/
lemma tri_c_not_on_ab(T : Triangle): ¬(Lies_on T.c (tri_ab T)) := by{
  unfold tri_ab Lies_on Line_through
  simp
  have : noncolinear T.a T.b T.c :=by{exact T.noncolinear}
  unfold noncolinear at this
  assumption
}

lemma tri_a_not_on_bc(T : Triangle): ¬(Lies_on T.a (tri_bc T)) := by{
  unfold tri_bc Lies_on Line_through
  simp
  have : noncolinear T.a T.b T.c :=by{exact T.noncolinear}
  unfold noncolinear at this
  contrapose this
  simp at *
  apply colinear_perm12
  apply colinear_perm23
  assumption
}

lemma tri_b_not_on_ca(T : Triangle): ¬(Lies_on T.b (tri_ca T)) := by{
  unfold tri_ca Lies_on Line_through
  simp
  have : noncolinear T.a T.b T.c :=by{exact T.noncolinear}
  unfold noncolinear at this
  contrapose this
  simp at *
  apply colinear_perm12
  apply colinear_perm13
  assumption
}

/-We can shift and scale Triangles:-/
lemma tri_shift_lemma (T : Triangle)(p : Point): noncolinear (padd T.a p) (padd T.b p) (padd T.c p) := by{
  exact noncolinear_shift p T.noncolinear
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
  exact noncolinear_conj T.noncolinear
}

def tri_conj : Triangle → Triangle :=
  fun T ↦ Triangle.mk (pconj T.a) (pconj T.b) (pconj T.c) (tri_conj_lemma T)

/-Mirroring twice gives the same-/

@[simp] lemma tri_conj_twice (T : Triangle) : tri_conj (tri_conj T) = T := by{
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

lemma midtriangle_noncolinear (T : Triangle): noncolinear (pmidpoint T.b T.c) (pmidpoint T.c T.a) (pmidpoint T.a T.b) := by{
  unfold pmidpoint at *
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

lemma midtriangle_noncolinear_point{a b c : Point}(h : noncolinear a b c): noncolinear (pmidpoint b c) (pmidpoint c a) (pmidpoint a b) := by{
  unfold pmidpoint at *
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

def Midtriangle : Triangle → Triangle :=
  fun T ↦ Triangle.mk (pmidpoint T.b T.c) (pmidpoint T.c T.a) (pmidpoint T.a T.b) (midtriangle_noncolinear T)

/- For reasons of compactness we introduce an unnecessary variable here-/
/-This has very low priority, so i leave it here
theorem heron{a b c : Point}{s : ℝ}(h: s = 1/2 * (perimiter_points a b c)) : |(area_points a b c)| = Real.sqrt (s*(s - (point_abs a b))*(s - (point_abs b c))*(s - point_abs c a)) := by{
  sorry
}
-/
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

lemma area_add_side (a b c x : Point)(bc : b≠c)(h : Lies_on x (Line_through bc)): area_points a b c = area_points a b x + area_points a x c := by{
  rw[area_add a b c x]
  have : area_points x b c = 0 := by{
    refine (area_zero_iff x b c).mpr ?_
    unfold Lies_on at h
    unfold Line_through at h
    simp at h
    apply colinear_perm13
    apply colinear_perm12
    assumption
  }
  linarith
}



/- A short notion for a point being in between other:-/

def in_between (a b x : Point) : Prop :=
  point_abs  a x + point_abs x b = point_abs a b

lemma in_between_self_left(a b : Point): in_between a b a := by{
  unfold in_between
  rw[point_abs_self, zero_add]
}

lemma in_between_self_right(a b : Point): in_between a b b := by{
  unfold in_between
  rw[point_abs_self, point_abs_symm, add_zero]
}

/-The wording of this is of course a bit unfortunate, but putting x in the middle wouldnt be
mich better in my opinion-/

lemma in_between_imp_scal (a b x : Point): (∃(t : ℝ), (0 ≤ t) ∧ (t ≤ 1) ∧ x = padd (p_scal_mul t a) (p_scal_mul (1-t) b)) → in_between a b x := by{

  intro h
  by_cases ab : a = b
  rw[ab]
  rw[ab] at h
  obtain ⟨t,t0,t1,ht⟩ := h
  have xb: x = b := by{
    rw[ht]
    ext
    unfold padd p_scal_mul
    simp
    ring
  }
  rw[xb]
  unfold in_between
  rw[point_abs_self]
  ring

  obtain ⟨t,t0,t1,ht⟩ := h
  have xgo: x = go_along a b ((1-t)*(point_abs a b)) := by{
    rw[ht]
    unfold go_along p_scal_mul dir padd
    simp
    have : (↑(point_abs a b) : ℂ) ≠ 0 := by{
      contrapose ab
      simp at *
      exact abs_zero_imp_same a b ab
    }
    field_simp
    ring
  }
  have abd: 0 < point_abs a b := by{
    have nonneg: 0 ≤ point_abs a b := by{exact point_abs_pos a b}
    have neqzero: point_abs a b ≠ 0 := by{
      contrapose ab
      simp at *
      exact abs_zero_imp_same a b ab
    }
    exact lt_of_le_of_ne nonneg (id (Ne.symm neqzero))
  }
  have ax: point_abs a x = (1-t)*(point_abs a b) := by{
    rw[xgo]
    rw [go_along_abs1 ab ((1 - t) * point_abs a b)]
    simp
    have : 0 ≤ 1-t := by{linarith}
    exact (mul_nonneg_iff_of_pos_right abd).mpr this
  }
  have bx : point_abs b x = t*(point_abs a b) := by{
    rw[xgo]
    rw [go_along_abs2 ab ((1 - t) * point_abs a b)]
    have :|point_abs a b - (1 - t) * point_abs a b| = point_abs a b - (1 - t) * point_abs a b := by{
      simp
      field_simp
      assumption
    }
    rw[this]
    ring
  }
  unfold in_between
  rw[point_abs_symm x b, ax, bx]
  ring
}

/-We will later show the reverse of this with pythagorean theorem. Proving it directly is very tricky.-/

/-This is symmetric in the first two arguments:-/

lemma in_between_symm {a b x : Point}(h : in_between a b x) : in_between b a x := by{
  unfold in_between at *
  rw[point_abs_symm b a, ← h, add_comm, point_abs_symm x a, point_abs_symm b x]
}

/-
/-A sweet consequence is that this can only happen when x already lies on the line between a b-/
--Proving this directly is horrible.
--However prove in between is equivalent to saying there is a t ∈ [0,1] s.t. x = t*a + (1-t)*b.
--This is sort of equivalent to colinear_alt2, which should be able to do the rest!
lemma in_between_imp_colinear {a b z : Point} (h: in_between a b z) : colinear a b z := by{
  apply (in_between_alt a b z) at h
  obtain ⟨t,t0,t1,ht⟩ := h
  rw[ht]
  unfold colinear det conj padd p_scal_mul
  simp
  ring_nf
}
--BIG TODO: Also do the reverse here: if a b c are colinear, one of them is between the other two
-/
/-The reverse (kind of) holds as well:-/
lemma colinear_imp_in_between1 {a b z : Point} (h : colinear a b z)(ha: point_abs a z ≤ point_abs a b)(hb: point_abs z b ≤ point_abs a b): in_between a b z := by{
  apply colinear_perm23 at h
  apply (colinear_alt2 a z b).1 at h
  by_cases h' : a = b
  rw[h'] at ha
  rw[point_abs_self b] at ha
  have : 0 = point_abs b z := by{
    apply le_antisymm
    exact point_abs_pos b z
    assumption
  }
  have : b = z := by{exact abs_zero_imp_same b z (id (Eq.symm this))}
  rw[h',this]
  unfold in_between
  simp
  exact point_abs_self z

  simp [*] at *
  obtain ⟨t,ht⟩ := h
  have zz: z = go_along a b (t*(point_abs a b)) := by{
    unfold go_along p_scal_mul dir padd
    ext
    rw[ht]
    simp
    have : (↑(point_abs a b) : ℂ) ≠ 0 := by{
      contrapose h'
      simp at *
      exact abs_zero_imp_same a b h'
    }
    field_simp
    ring
  }
  have hht: 0 ≤ t ∧ t ≤ 1 := by{
    have abb: 0 < point_abs a b := by{
      contrapose h'
      simp at *
      apply abs_zero_imp_same
      apply le_antisymm
      assumption
      exact point_abs_pos a b
    }
    constructor
    contrapose hb
    simp at *
    have : point_abs b z = (1-t)*(point_abs a b) := by{
      rw[zz]
      rw [go_along_abs2 h' (t * point_abs a b)]
      have : |point_abs a b - t * point_abs a b| = point_abs a b - t * point_abs a b := by{
        simp
        field_simp
        linarith
      }
      rw[this]
      ring
    }
    rw[point_abs_symm z b, this]
    field_simp
    linarith


    contrapose ha
    simp at *
    have : point_abs a z = t*(point_abs a b) := by{
      rw[zz]
      rw [go_along_abs1 h' (t * point_abs a b)]
      have : |t * point_abs a b| = t * point_abs a b := by{
        simp
        field_simp
        linarith
      }
      rw[this]
    }
    rw[this]
    field_simp
    assumption
  }
  have ad: point_abs a z = t*(point_abs a b) := by{
    have : abs (t * (point_abs a b)) = t * (point_abs a b) := by{
      simp
      have u: 0 ≤ point_abs a b := by{exact point_abs_pos a b}
      exact Left.mul_nonneg hht.1 u
    }
    rw[← this]
    rw[zz]
    exact go_along_abs1 h' (t * point_abs a b)
  }
  have bd: point_abs b z = (1-t)*(point_abs a b) := by{
    rw[zz]
    rw [go_along_abs2 h' (t * point_abs a b)]
    have : |point_abs a b - t * point_abs a b| = point_abs a b - t * point_abs a b := by{
      simp
      have : 0<(point_abs a b) := by{
        have g0: 0 ≤ point_abs a b := by{exact point_abs_pos a b}
        have n0: 0 ≠ point_abs a b := by{
          contrapose h'
          simp at *
          exact abs_zero_imp_same a b (id (Eq.symm h'))
        }
        exact lt_of_le_of_ne g0 n0
      }
      field_simp
      exact hht.2
    }
    rw[this]
    ring
  }
  unfold in_between
  rw[point_abs_symm z b]
  rw[ad,bd]
  ring
  }

/-This immediately implies given 3 points, 1 is in between the other two:-/
lemma colinear_imp_in_between2 (a b c : Point)(h : colinear a b c): in_between a b c ∨ in_between b c a ∨ in_between c a b := by{
  have p1: colinear b c a := by{
    apply colinear_perm13
    apply colinear_perm23
    assumption
  }
  have p2: colinear c a b := by{
    apply colinear_perm12
    apply colinear_perm13
    assumption
  }
  by_cases h0 : point_abs a b ≤ point_abs b c
  by_cases h1 : point_abs b c ≤ point_abs c a
  by_cases h2 : point_abs c a ≤ point_abs a b

  have : point_abs b c ≤ point_abs a b := by{linarith}
  left
  apply colinear_imp_in_between1 h
  repeat
    rw[point_abs_symm]
    assumption

  simp at h2
  have h3: point_abs a b ≤ point_abs c a := by{exact LT.lt.le h2}
  right
  right
  apply colinear_imp_in_between1 p2
  repeat
    rw[point_abs_symm]
    assumption

  simp at h1
  have h3: point_abs c a ≤ point_abs b c := by{exact LT.lt.le h1}
  right
  left
  apply colinear_imp_in_between1 p1
  repeat
    rw[point_abs_symm]
    assumption

  simp at h0
  have h3: point_abs b c ≤ point_abs a b := by{exact LT.lt.le h0}
  by_cases h1 : point_abs b c ≤ point_abs c a
  by_cases h2 : point_abs c a ≤ point_abs a b

  left
  apply colinear_imp_in_between1 h
  repeat
    rw[point_abs_symm]
    assumption

  simp at h2
  have h4: point_abs a b ≤ point_abs c a := by{exact LT.lt.le h2}
  right
  right
  apply colinear_imp_in_between1 p2
  repeat
    rw[point_abs_symm]
    assumption

  simp at h1
  have h4: point_abs c a ≤ point_abs b c := by{exact LT.lt.le h1}
  by_cases h2 : point_abs c a ≤ point_abs a b

  left
  apply colinear_imp_in_between1 h
  repeat
    rw[point_abs_symm]
    assumption

  simp at h2
  clear h3 h4 p1 p2 h
  exfalso
  have : point_abs b c < point_abs b c := by{
    calc
      point_abs b c < point_abs a b := by{exact h0}
        _< point_abs c a := by{exact h2}
        _< point_abs b c := by{exact h1}
  }
  simp at this
}

/-first small lemma (better suited elsewhere, but whatever)-/

lemma in_between_go_along{a b : Point}{r : ℝ}(ab : a ≠ b)(h : in_between a b (go_along a b r)) : 0 ≤ r ∧ r ≤ point_abs a b := by{
  unfold in_between at h
  have absub : 0 < point_abs a b := by{exact point_abs_neq ab}
  rw[← point_abs_symm b, go_along_abs1 ab, go_along_abs2 ab] at h
  have g1: 0 ≤ r := by{
    by_contra h0
    simp at h0
    have : point_abs a b < point_abs a b := by{
      calc
        point_abs a b < point_abs a b - r := by{linarith}
          _= abs (point_abs a b - r) := by{
            symm
            simp
            linarith
          }
          _≤ abs r + abs (point_abs a b - r) := by{simp}
          _= point_abs a b := by{rw[h]}
    }
    linarith
  }
  have g2: r ≤ point_abs a b := by{
    by_contra h0
    simp [*] at *
    have : abs r = r := by{simp [*]}
    rw[this] at h
    have : abs (point_abs a b - r) < 0 := by{
      calc
        abs (point_abs a b - r) = -r + (r+ abs (point_abs a b - r)) := by{ring}
          _= -r + point_abs a b := by{rw[h]}
          _< - point_abs a b + point_abs a b := by{linarith}
          _= 0 := by{ring}
    }
    contrapose this
    simp
  }
  tauto
}

lemma in_between_go_along'{a b : Point}{r : ℝ}(ab : a ≠ b)(h : in_between b (go_along a b r) a) : r ≤ 0 := by{
  unfold in_between at h
  rw[go_along_abs1 ab, go_along_abs2 ab, point_abs_symm b a] at h
  have z: 0 < point_abs a b := by{exact point_abs_neq ab}
  by_contra h0
  simp [*] at *
  have : abs r = r := by{simp [*]; linarith}
  rw[this] at h
  clear this

  by_cases h1: 0 < point_abs a b - r
  have : |point_abs a b - r| = point_abs a b - r := by{simp; linarith}
  linarith

  simp at h1
  have : abs (point_abs a b - r) = -(point_abs a b - r) := by{
    refine abs_of_nonpos ?h
    linarith
  }
  linarith
}
