import LeanCourse.Project.Similar
import Mathlib

open Function Set Classical

noncomputable section

set_option linter.unusedTactic false
set_option maxHeartbeats 1000000

/-In this section we actually prove something interesting for once:
Ceva's theorem. The main lemma behind it will be proven by computation, the main result however
geomtrically!-/

/-First we need signed quotients:-/
def sQuot : Point → Point → Point → ℝ :=
  fun a b c ↦ (if h: in_between a c b then (point_abs a b) /(point_abs b c) else - (point_abs a b) / point_abs b c)

/-Note: We will only ever use this in the case of a b c being colinear, to simplify the definitioon however,
we techincally dont require that.-/

/-The central lemma (bc of its importance called theorem tho haha) is now, that the sQuot corresponds to the quotient of areas:-/
/-We define it very carefully to be as exact and general as possible:-/
theorem squot_areas{a b c p : Point}{L : Line}(ah: Lies_on a L)(bh: Lies_on b L)(ch: Lies_on c L)(ph: ¬Lies_on p L): sQuot a b c = (area_points a b p) / (area_points b c p) := by{
  by_cases cb: c = b
  · rw[cb]
    unfold area_points det
    simp
    unfold sQuot in_between
    rw[point_abs_self]
    have u : point_abs a c + 0 = point_abs a c := by{ring}
    simp [u]
  by_cases ab: a = b
  · rw[ab]
    unfold sQuot area_points det
    simp [in_between_self_left, point_abs_self]
  unfold sQuot
  have col: colinear a b c := by{
    have hL: L = Line_through ab := by{
      apply line_through_unique
      tauto
    }
    rw[hL] at ch
    unfold Line_through Lies_on at ch
    simp at ch
    assumption
  }
  have bc_abs: point_abs b c ≠ 0 := by{
    contrapose cb
    simp at *
    symm
    exact abs_zero_imp_same b c cb
  }
  have area_z: area_points b c p ≠ 0 := by{
    contrapose ph
    simp at *
    have hL: L = Line_through cb := by{
      apply line_through_unique
      tauto
    }
    rw[hL]
    unfold Lies_on Line_through
    simp
    apply colinear_perm12
    exact (area_zero_iff b c p).1 ph
  }
  by_cases ac : a = c
  · rw[ac]
    rw[point_abs_symm b c]
    rw[point_abs_symm] at bc_abs
    field_simp
    have : ¬in_between c c b := by{
      contrapose bc_abs
      simp at *
      unfold in_between at bc_abs
      rw[point_abs_symm b c, point_abs_self] at bc_abs
      simp [*] at *
      assumption
    }
    simp [*]
    unfold area_points det
    simp
    ring
  obtain h|h|h := colinear_imp_in_between2 a b c col
  · have nh: ¬in_between a c b := by{
      by_contra h0
      unfold in_between at *
      rw[← h0, point_abs_symm c b] at h
      have : b = c := by{
        apply abs_zero_imp_same b c
        linarith
      }
      tauto
    }
    simp [nh]
    field_simp
    apply colinear_perm23 at col
    obtain ⟨R,hR⟩ := colinear_go_along ac col
    rw[hR]
    rw[hR] at h
    have ca: c ≠ a := by{tauto}
    rw[go_along_symm] at h
    have h1: abs R = R := by{
      suffices: 0 ≤ R
      · exact (abs_of_nonneg this)
      suffices: point_abs c a - R ≤ 0
      · have : 0 ≤ point_abs c a := by{exact point_abs_pos c a}
        linarith
      exact in_between_go_along' ca h
    }
    have h2: abs (point_abs a c - R) = - (point_abs a c - R) := by{
      suffices: point_abs a c - R ≤ 0
      · exact abs_of_nonpos this
      rw[point_abs_symm]
      exact in_between_go_along' ca h
    }
    rw[go_along_abs1, point_abs_symm, go_along_abs2, h1, h2]
    unfold go_along dir
    have ac_abs: (point_abs a c) ≠ 0 := by{
      exact point_abs_neq_zero ac
    }
    unfold area_points det padd p_scal_mul
    field_simp
    obtain ⟨a1,a2⟩ := a
    obtain ⟨c1,c2⟩ := c
    obtain ⟨p1,p2⟩ := p
    unfold point_abs conj
    field_simp at *
    have : Complex.abs { re := a1 - c1, im := a2 - c2 } ≠ 0 := by{
      by_contra h0
      simp at h0
      have s1: a1 - c1 = 0 := by{
        calc
          a1-c1 = ({ re := a1 - c1, im := a2 - c2 } : ℂ).re := by{simp}
            _= (0 : ℂ).re := by{rw[h0]}
            _= 0 := by{simp}
      }
      have s2: a2-c2 = 0 := by{
        calc
          a2-c2 = ({ re := a1 - c1, im := a2 - c2 } : ℂ).im := by{simp}
            _= (0 : ℂ).im := by{rw[h0]}
            _= 0 := by{simp}
      }
      have t1: a1 = c1 := by{linarith}
      have t2: a2 = c2 := by{linarith}
      tauto
    }
    field_simp
    ring
    repeat
      assumption

  have hh: ¬in_between a c b := by{
    by_contra h0
    unfold in_between at *
    rw[← h0] at h
    rw[point_abs_symm b a] at h
    have : a=b := by{
      apply abs_zero_imp_same
      linarith
    }
    tauto
  }
  simp [hh]
  field_simp
  apply colinear_perm23 at col
  obtain ⟨R,hR⟩ := colinear_go_along ac col
  rw[hR] at h
  apply in_between_symm at h
  obtain u := in_between_go_along' ac h
  rw[point_abs_symm b c, hR, go_along_abs1 ac, go_along_abs2 ac]
  have s1: abs R = -R := by{
    simp
    assumption
  }
  have s2: |point_abs a c - R| = point_abs a c - R := by{
    obtain o := point_abs_pos a c
    simp
    linarith
  }
  rw[s1,s2]
  obtain ⟨a1,a2⟩ := a
  obtain ⟨c1,c2⟩ := c
  obtain ⟨p1,p2⟩ := p
  unfold go_along dir padd p_scal_mul area_points det conj point_abs
  field_simp at *
  have : Complex.abs { re := a1 - c1, im := a2 - c2 } ≠ 0 := by{
      by_contra h0
      simp at h0
      have s1: a1 - c1 = 0 := by{
        calc
          a1-c1 = ({ re := a1 - c1, im := a2 - c2 } : ℂ).re := by{simp}
            _= (0 : ℂ).re := by{rw[h0]}
            _= 0 := by{simp}
      }
      have s2: a2-c2 = 0 := by{
        calc
          a2-c2 = ({ re := a1 - c1, im := a2 - c2 } : ℂ).im := by{simp}
            _= (0 : ℂ).im := by{rw[h0]}
            _= 0 := by{simp}
      }
      have t1: a1 = c1 := by{linarith}
      have t2: a2 = c2 := by{linarith}
      tauto
  }
  field_simp
  ring



  apply in_between_symm at h
  simp [h]
  field_simp
  apply colinear_perm23 at col
  obtain ⟨R,hR⟩ := colinear_go_along ac col
  rw[point_abs_symm b c, hR, go_along_abs1, go_along_abs2]
  rw[hR] at h
  obtain ⟨u1,u2⟩ := in_between_go_along ac h
  have s1: abs R = R := by{simp [*]}
  have s2: abs (point_abs a c - R) = point_abs a c - R := by{
    simp
    linarith
  }
  rw[s1,s2]
  obtain ⟨a1,a2⟩ := a
  obtain ⟨c1,c2⟩ := c
  obtain ⟨p1,p2⟩ := p
  unfold go_along dir padd p_scal_mul area_points det conj point_abs
  field_simp at *
  have : Complex.abs { re := a1 - c1, im := a2 - c2 } ≠ 0 := by{
      by_contra h0
      simp at h0
      have s1: a1 - c1 = 0 := by{
        calc
          a1-c1 = ({ re := a1 - c1, im := a2 - c2 } : ℂ).re := by{simp}
            _= (0 : ℂ).re := by{rw[h0]}
            _= 0 := by{simp}
      }
      have s2: a2-c2 = 0 := by{
        calc
          a2-c2 = ({ re := a1 - c1, im := a2 - c2 } : ℂ).im := by{simp}
            _= (0 : ℂ).im := by{rw[h0]}
            _= 0 := by{simp}
      }
      have t1: a1 = c1 := by{linarith}
      have t2: a2 = c2 := by{linarith}
      tauto
  }
  field_simp
  ring
  repeat
    tauto
}

/-With that lemma we can now prove ceva's theorem in a nice way
Unfortunaately our version is a bit ugly, as ceva's theorem is best stated in terms of projective geometry,
which is not possible with the foundation of geometry being used here :(-/

def not_on_perimiter(p : Point)(T : Triangle): Prop :=
  ¬Lies_on p (tri_ab T) ∧ ¬Lies_on p (tri_bc T) ∧ ¬Lies_on p (tri_ca T)

  theorem Ceva(T : Triangle)(p : Point)(hp: not_on_perimiter p T): 0 = 0 := by{
    sorry
  }

--ich muss noch eine sQuotL version einführen, die 1 ist wenn parallel!
