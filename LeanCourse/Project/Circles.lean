import LeanCourse.Project.Triangles
import Mathlib

open Function Set Classical

noncomputable section

abbrev PosReal : Type := {x : ℝ // 0 ≤ x}

/-In this section we will define circles and prove some stuff about them.
One of the main goals is to prove that every Triangle has a unique circumcircle.-/

/-Because Circle is taken in mathlib...........
We use CCircle "Complex Circle"-/

/- Now introduce circles:-/
@[ext] structure CCircle where
  range : Set Point
  span : ∃ (z : Point) (R : PosReal), range = {p : Point | point_abs z p = R}

/-It is a matter of debate how you want to define circles exactly
One could allow negative radii, however then:
-Circles dont have unique centers
-Circles dont have unique radii

So the question is rather if we allow radius zero.
This has one major upside and one major downside:

-The power of point/circle technique uses circles with radius zero occassionally and effectivefely.

-On the other hand, basically everything with tangents only works for positive radii

I ultimately decided for radius 0. Where this wont work, we will use an extension of CCircle.
-/


/-And tangents to circles-/

def LineCircleTangent (C: CCircle) (L : Line) : Prop :=
  Tangential C.range L.range

/-Obviously Circles are mostly seen as tuple of a Point and a nonnegative real number:-/
def Circle_through (z : Point)(R : PosReal) : CCircle where
  range := {p : Point | point_abs z p = R}
  span := by{
    use z
    use R
  }

/-Every circle can be seen this way:-/
lemma circle_gen (C : CCircle): ∃(z:Point)(R: PosReal), C = Circle_through z R := by{
  obtain ⟨h,p,r,gen⟩ := C
  use p
  use r
  ext x
  unfold Circle_through
  simp
  rw[gen]
  simp
}

/-So we obtain center and radius:-/

lemma circle_has_center (C : CCircle): ∃(z: Point), ∃(R : PosReal), C = Circle_through z R := by{
  exact circle_gen C
}

def Center : CCircle → Point :=
  fun C ↦ (circle_has_center C).choose

def Lies_on_circle (a : Point)(C : CCircle) : Prop :=
  a ∈ C.range

lemma circle_has_radius (C : CCircle): ∃(R : PosReal), ∃(z : Point), C = Circle_through z R := by{
  obtain ⟨z,R,h⟩ := circle_gen C
  use R
  use z
}

def Radius : CCircle → PosReal :=
  fun C ↦ (circle_has_radius C).choose

/-These really do what we want:-/

lemma center_is_center (C : CCircle): ∃(R : PosReal), C = Circle_through (Center C) R := by{
  unfold Center
  exact (Exists.choose_spec (circle_has_center C))
}

lemma radius_is_radius (C : CCircle): ∃(z : Point), C = Circle_through z (Radius C) := by{
  unfold Radius
  exact (Exists.choose_spec (circle_has_radius C))
}

/-The two are unique! This is a bit painful to show.
We first show the uniqueness of the radius, for this we use the diameter.-/

lemma diameter_max {z a b : Point}{R : PosReal}(ah: Lies_on_circle a (Circle_through z R))(bh : Lies_on_circle b (Circle_through z R)) : point_abs a b ≤ 2*R := by{
  unfold Circle_through Lies_on_circle at *
  simp at *
  calc
    point_abs a b ≤ point_abs a z + point_abs z b := by{exact point_abs_triangle a z b}
      _= point_abs z a + point_abs z b := by{rw [point_abs_symm z a]}
      _ ≤ (↑R : ℝ) + ↑R := by{rw[ah,bh];rfl}
      _= 2*R := by ring
}

/-There exists points satistifying the diameter:-/
lemma diameter_ex (z : Point)(R : PosReal) : ∃(a b : Point), (Lies_on_circle a (Circle_through z R)) ∧ (Lies_on_circle b (Circle_through z R)) ∧ (point_abs a b = 2*R) := by{
  use (Point.mk (z.x + (↑R : ℂ)))
  use (Point.mk (z.x - (↑R : ℂ)))
  unfold Lies_on_circle
  unfold Circle_through
  simp
  unfold point_abs
  simp
  ring_nf
  unfold Complex.abs
  simp
}

/-We can state the uniqueness of the radius (and later center) in a very nice way, as we've already
shown that every Circle has the form Circle_through z R-/

theorem radius_unique (z : Point)(R : PosReal) : R = Radius (Circle_through z R) := by{
  obtain ⟨p,ph⟩ := radius_is_radius (Circle_through z R)
  obtain ⟨a,b,ah,bh,ab⟩ := diameter_ex z R
  obtain ⟨c,d,ch,dh,cd⟩ := diameter_ex p (Radius (Circle_through z R))
  have le1: point_abs a b ≤ 2*(Radius (Circle_through z R)) := by{
    clear c d ch dh cd
    rw[ph] at ah bh
    exact diameter_max ah bh
  }
  rw[ab] at le1
  clear a b ab ah bh
  have le2: point_abs c d ≤ 2*R := by{
    rw[← ph] at ch dh
    exact diameter_max ch dh
  }
  rw[cd] at le2
  clear c d cd ch dh
  simp at *
  apply le_antisymm
  assumption
  assumption
}

/-A sometimes maybe faster way to use this is the following:-/
lemma radius_unique_spec {z z' : Point}{R R' : PosReal}(h: Circle_through z R = Circle_through z' R') : R = R' := by{
  have R1: R = Radius (Circle_through z R) := by{
    exact radius_unique z R
  }
  have R2: R' = Radius (Circle_through z' R') := by{
    exact radius_unique z' R'
  }
  rw[h] at R1
  nth_rw 1 [R1]
  symm
  assumption
}

/-With this we can show that the center is unique as well. This will be a bit painful.
For simplicities sake we first show this without (Center C). (so first the spec way)-/

lemma center_unique_spec {p q : Point}{R S : PosReal}(h: Circle_through p R = Circle_through q S): p = q := by{
  have RS: R = S := by{
    exact radius_unique_spec h
  }
  rw[← RS] at h
  clear S RS
  by_contra h0
  have lo: Lies_on_circle (go_along p q (-R)) (Circle_through p R) := by{
    unfold Lies_on_circle Circle_through
    simp
    rw[go_along_abs1]
    simp
    assumption
  }
  rw[h] at lo
  unfold Lies_on_circle Circle_through at lo
  simp at lo
  have : point_abs q (go_along p q (-(↑R : ℝ))) = point_abs p q + ((↑R : ℂ)) := by{
    rw[go_along_abs2]
    simp
    norm_cast
    have : 0 ≤ point_abs p q + ↑R := by{
      apply add_nonneg
      exact point_abs_pos p q
      exact R.2
    }
    exact abs_of_nonneg this

    assumption
  }
  norm_cast at this
  simp at this
  rw[this] at lo
  simp at lo
  apply abs_zero_imp_same at lo
  contradiction
}

theorem center_unique (z : Point)(R : PosReal) : z = Center (Circle_through z R) := by{
  obtain ⟨r,rh⟩  := center_is_center (Circle_through z R)
  exact center_unique_spec rh
}
