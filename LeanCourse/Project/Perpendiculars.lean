import LeanCourse.Project.Circles
import Mathlib

open Function Set Classical

noncomputable section

/-This section is for introducing perpendiculars. Goals are to highilght how Parallel and Perpenduclar
are connected, show every point and line has a unique perpendicular line and finishing off with the orthocenter.-/


/-Firstt we define perpedicular "points"-/
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
  sorry
}

lemma perp_points_perm_back{a b c d}(h: perp_points a b c d): perp_points a b d c := by{
  apply perp_points_perm_switch
  apply perp_points_perm_front
  exact perp_points_perm_switch h
}
