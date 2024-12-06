import LeanCourse.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Convolution
import Mathlib.Data.Real.Irrational
import Mathlib.MeasureTheory.Function.Jacobian
open BigOperators Function Set Real Topology Filter
open MeasureTheory Interval Convolution ENNReal
noncomputable section

noncomputable section
open BigOperators Function Set Real Filter Classical Topology TopologicalSpace


/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 11 & 12.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 10.12.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/


example (x : ℝ) :
    deriv (fun x ↦ Real.exp (x ^ 2)) x = 2 * x * Real.exp (x ^ 2) := by {
  #check deriv.comp
  have h1: DifferentiableAt ℝ (fun y ↦ y^2) x := by{
    fun_prop
  }
  have h2: DifferentiableAt ℝ (fun y ↦ Real.exp y) ((fun y ↦ y^2) x) := by{
    fun_prop
  }
  have : (fun x ↦ rexp (x ^ 2)) =  (fun x ↦ Real.exp x)∘(fun x ↦ x^2) := by{
    rfl
  }
  rw[this]
  let u := (fun (y:ℝ) ↦ y^2)
  have udef : u = (fun (y:ℝ) ↦ y^2) := rfl
  rw[← udef]
  rw[← udef] at h1
  rw[← udef] at h2
  let v := (fun y ↦ Real.exp y)
  have vdef : v = (fun y ↦ Real.exp y) := rfl
  rw[← vdef]
  rw[← vdef] at h2
  rw[deriv.comp x h2 h1]
  have : deriv v (u x) = rexp (x^2) := by{
    unfold v u
    apply HasDerivAt.deriv
    exact Real.hasDerivAt_exp (x ^ 2)
  }
  rw[this]
  have : deriv u x = 2*x := by{
    unfold u
    apply HasDerivAt.deriv
    have hc: HasDerivAt (fun (z:ℝ) ↦ z ) 1 x := by{exact hasDerivAt_id' x}
    have : 2 * x = (↑(2:ℕ):ℝ) * ((fun (z:ℝ) ↦ z) x) ^ (2 - 1)* 1 := by{simp}
    rw[this]
    exact HasDerivAt.pow 2 hc
  }
  rw[this]
  ring
  }

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : ℕ∞} in
/- In this exercise you should combine the right lemmas from the library,
in particular `IsBoundedBilinearMap.contDiff`. -/
example (L : E →L[𝕜] E →L[𝕜] E) (f g : E → E) (hf : ContDiff 𝕜 n f)
    (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (fun z : E × E ↦ L (f z.1) (g z.2)) := by {
  #check IsBoundedBilinearMap.contDiff
  apply IsBoundedBilinearMap.contDiff
  sorry
  }


section

variable (α : Type*)
 [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]

/-
In the next three exercises we will show that every continuous injective function `ℝ → ℝ` is
either strictly monotone or strictly antitone.

We start by proving a slightly harder version of the exercise in class.
We generalize the real numbers to an arbitrary type `α`
that satisfies all the conditions required for the intermediate value theorem.
If you want to prove this by using the intermediate value theorem only once,
then use `intermediate_value_uIcc`.
`uIcc a b` is the unordered interval `[min a b, max a b]`.
Useful lemmas: `uIcc_of_le` and `mem_uIcc`. -/
lemma mono_exercise_part1 {f : α → α} (hf : Continuous f) (h2f : Injective f) {a b x : α}
    (hab : a ≤ b) (h2ab : f a < f b) (hx : a ≤ x) : f a ≤ f x := by {
  have ab: [[f a, f b]] ⊆ f '' [[a, b]] := by{
    apply intermediate_value_uIcc
    exact Continuous.continuousOn hf
  }
  have ax: [[f a, f x]] ⊆ f '' [[a, x]] := by{
    apply intermediate_value_uIcc
    exact Continuous.continuousOn hf
  }
  have bx: [[f x, f b]] ⊆ f '' [[x, b]] := by{
    apply intermediate_value_uIcc
    exact Continuous.continuousOn hf
  }
  by_contra h0
  simp at h0
  by_cases h1: f x ≤ f b
  have: f a ∈ [[f x, f b]] := by{
    refine mem_uIcc.mpr ?_
    left
    constructor
    exact le_of_lt h0
    exact le_of_lt h2ab
  }
  have s1: f a ∈ f '' [[x,b]] := by{
    exact bx this
  }
  simp at s1
  obtain ⟨u,uh1,uh2⟩ := s1
  have ua: u = a := by{
    apply h2f
    assumption
  }
  rw[ua] at uh1
  clear uh2 ua this
  by_cases xb: x ≤ b
  simp [*] at uh1
  have xa: a = x := by{exact le_antisymm hx uh1}
  rw[xa] at h0
  exact (lt_self_iff_false (f x)).mp h0

  simp at xb
  have: b ≤ x := by{exact le_of_lt xb}
  simp [*] at uh1
  have ba: b = a := by{exact le_antisymm uh1 hab}
  rw[ba] at h2ab
  exact (lt_self_iff_false (f a)).mp h2ab

  simp at h1
  have : f b < f b := by{
    calc
      f b < f x := by{exact h1}
        _< f a := by{exact h0}
        _< f b := by{exact h2ab}
  }
  exact (lt_self_iff_false (f b)).mp this
  }


/- Now use this and the intermediate value theorem again
to prove that `f` is at least monotone on `[a, ∞)`. -/
lemma mono_exercise_part2 {f : α → α} (hf : Continuous f) (h2f : Injective f)
    {a b : α} (hab : a ≤ b) (h2ab : f a < f b) : StrictMonoOn f (Ici a) := by {
  unfold StrictMonoOn
  intro x xh
  intro y yh xy
  simp at yh xh
  have ay: f a ≤ f y := by{exact mono_exercise_part1 α hf h2f hab h2ab yh}
  have ax: f a ≤ f x := by{exact mono_exercise_part1 α hf h2f hab h2ab xh}
  have hxy: x ≤ y := by{exact le_of_lt xy}
  #check mono_exercise_part1
  have t: f a < f y :=by{
    have : a ≠ y := by{
      refine ne_of_lt ?h
      exact lt_of_le_of_lt xh xy
    }
    have : f a ≠ f y := by{
      exact fun a_1 ↦ this (h2f a_1)
    }
    exact lt_of_le_of_ne ay this
  }
  have : f x ≤ f y := by{
    clear hab h2ab b
    sorry
  }
  have uu: f x ≠ f y := by{
    by_contra p
    apply h2f at p
    rw[p] at xy
    exact (lt_self_iff_false y).mp xy
  }
  exact lt_of_le_of_ne this uu
  }

/-
Now we can finish just by using the previous exercise multiple times.
In this proof we take advantage that we did the previous exercise for an arbitrary order,
because that allows us to apply it to `ℝ` with the reversed order `≥`.
This is called `OrderDual ℝ`. This allows us to get that `f` is also strictly monotone on
`(-∞, b]`.
Now finish the proof yourself.
You do not need to apply the intermediate value theorem in this exercise.
-/
lemma mono_exercise_part3 (f : ℝ → ℝ) (hf : Continuous f) (h2f : Injective f) :
    StrictMono f ∨ StrictAnti f := by {
  have : ∀ {a b : ℝ} (hab : a ≤ b) (h2ab : f a < f b), StrictMonoOn f (Iic b)
  · intro a b hab h2ab
    have := mono_exercise_part2 (OrderDual ℝ) hf h2f hab h2ab
    rw [strictMonoOn_dual_iff.symm] at this
    exact this
  sorry
  }

end

/-
Let's prove that the absolute value function is not differentiable at 0.
You can do this by showing that the left derivative and the right derivative do exist,
but are not equal. We can state this with `HasDerivWithinAt`
To make the proof go through, we need to show that the intervals have unique derivatives.
An example of a set that doesn't have unique derivatives is the set `ℝ × {0}`
as a subset of `ℝ × ℝ`, since that set doesn't contains only points in the `x`-axis,
so within that set there is no way to know what the derivative of a function should be
in the direction of the `y`-axis.

The following lemmas will be useful
* `HasDerivWithinAt.congr`
* `uniqueDiffWithinAt_convex`
* `HasDerivWithinAt.derivWithin`
* `DifferentiableAt.derivWithin`.
-/

example : ¬ DifferentiableAt ℝ (fun x : ℝ ↦ |x|) 0 := by {
  intro h
  have h1 : HasDerivWithinAt (fun x : ℝ ↦ |x|) 1 (Ici 0) 0 := by {
    sorry
    }
  have h2 : HasDerivWithinAt (fun x : ℝ ↦ |x|) (-1) (Iic 0) 0 := by {
    sorry
    }
  have h3 : UniqueDiffWithinAt ℝ (Ici (0 : ℝ)) 0 := by {
  sorry
  }
  have h4 : UniqueDiffWithinAt ℝ (Iic (0 : ℝ)) 0 := by {
  sorry
  }
  -- sorry
  sorry
  }



/- There are special cases of the change of variables theorems for affine transformations
(but you can also use the change of variable theorem from the lecture) -/
example (a b : ℝ) :
    ∫ x in a..b, sin (x / 2 + 3) =
    2 * cos (a / 2 + 3) - 2 * cos (b / 2  + 3) := by {
  sorry
  }

/- Use the change of variables theorem for this exercise. -/
example (f : ℝ → ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    ∫ x in s, exp x * f (exp x) = ∫ y in exp '' s, f y := by {
  sorry
  }

example (x : ℝ) : ∫ t in (0)..x, t * exp t = (x - 1) * exp x + 1 := by {
  sorry
  }

example (a b : ℝ) : ∫ x in a..b, 2 * x * exp (x ^ 2) =
    exp (b ^ 2) - exp (a ^ 2) := by {
  sorry
  }


/-! # Exercises to hand-in. -/

/- This is a copy of `mono_exercise_part1` above. See the comments there for more info. -/
variable (α : Type*) [ConditionallyCompleteLinearOrder α]
  [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] in
lemma mono_exercise_part1_copy {f : α → α} (hf : Continuous f) (h2f : Injective f) {a b x : α}
    (hab : a ≤ b) (h2ab : f a < f b) (hx : a ≤ x) : f a ≤ f x := by {
  have ab: [[f a, f b]] ⊆ f '' [[a, b]] := by{
    apply intermediate_value_uIcc
    exact Continuous.continuousOn hf
  }
  have ax: [[f a, f x]] ⊆ f '' [[a, x]] := by{
    apply intermediate_value_uIcc
    exact Continuous.continuousOn hf
  }
  have bx: [[f x, f b]] ⊆ f '' [[x, b]] := by{
    apply intermediate_value_uIcc
    exact Continuous.continuousOn hf
  }
  by_contra h0
  simp at h0
  by_cases h1: f x ≤ f b
  have: f a ∈ [[f x, f b]] := by{
    refine mem_uIcc.mpr ?_
    left
    constructor
    exact le_of_lt h0
    exact le_of_lt h2ab
  }
  have s1: f a ∈ f '' [[x,b]] := by{
    exact bx this
  }
  simp at s1
  obtain ⟨u,uh1,uh2⟩ := s1
  have ua: u = a := by{
    apply h2f
    assumption
  }
  rw[ua] at uh1
  clear uh2 ua this
  by_cases xb: x ≤ b
  simp [*] at uh1
  have xa: a = x := by{exact le_antisymm hx uh1}
  rw[xa] at h0
  exact (lt_self_iff_false (f x)).mp h0

  simp at xb
  have: b ≤ x := by{exact le_of_lt xb}
  simp [*] at uh1
  have ba: b = a := by{exact le_antisymm uh1 hab}
  rw[ba] at h2ab
  exact (lt_self_iff_false (f a)).mp h2ab

  simp at h1
  have : f b < f b := by{
    calc
      f b < f x := by{exact h1}
        _< f a := by{exact h0}
        _< f b := by{exact h2ab}
  }
  exact (lt_self_iff_false (f b)).mp this
  }

/- Prove the following using the change of variables theorem. -/
lemma change_of_variables_exercise (f : ℝ → ℝ) :
    ∫ x in (0)..π, sin x * f (cos x) = ∫ y in (-1)..1, f y := by {
  rw[intervalIntegral.integral_of_le]
  rw[intervalIntegral.integral_of_le]
  swap
  linarith
  swap
  exact pi_nonneg
  let g := f
  let ff := fun y ↦ cos y
  let a := (0:ℝ)
  let b := (π : ℝ)
  have adef : a = 0 := rfl
  have bdef : b = π := rfl
  have gdef: g = f := rfl
  rw[← gdef,← adef, ← bdef]

  have ffdef: ff = fun y ↦ cos y := rfl
  --rw[← ffdef]
  let f' := fun x ↦ - sin x
  have f'_def : f' = fun x ↦ - sin x := rfl
  --rw[← f'_def]
  have h : ∀ x ∈ [[a, b]], HasDerivAt ff (f' x) x := by{
    unfold ff f'
    intro x xh
    exact hasDerivAt_cos x
  }
  --#check integral_image_eq_integral_abs_deriv_smul
  have : ∫ (x : ℝ) in Ioc a b, sin x * g (cos x) ∂volume = ∫ (x : ℝ) in Ioc a b, sin x * g (cos x) := rfl
  rw[this]
  clear this
  have : ∫ (x : ℝ) in Ioc (-1) 1, g x ∂volume = ∫ (x : ℝ) in Ioc (-1) 1, g x := rfl
  rw[this]
  clear this

  have : ∫ (x : ℝ) in Ioc a b, sin x * g (cos x) = ∫ (x : ℝ) in Ioc a b, -f' x * g (ff x) := by{
    unfold f' ff
    simp
  }
  rw[this]
  clear this

  --#check integral_image_eq_integral_abs_deriv_smul
  unfold a b at *
  clear adef bdef a b
  let s := Ioc 0 π
  have sdef: s = Ioc 0 π := rfl
  rw[← sdef]
  have hs : MeasurableSet s := by{
    unfold s
    simp
  }
  have hf' : ∀ x ∈ s, HasDerivWithinAt ff (f' x) s x := by{
    unfold ff f'
    intro x xh
    unfold s
    refine HasDerivAt.hasDerivWithinAt ?h
    exact hasDerivAt_cos x
  }
  have hf : InjOn ff s := by{
    unfold ff s
    intro x xh y yh yx
    simp at *
    clear gdef ffdef f'_def hf' s hs h f' ff g f
    have z: 0 ≤ x := by{
      exact le_of_lt xh.1
    }
    have r: 0 ≤ y := by{
      exact le_of_lt yh.1
    }
    obtain ⟨xh1,xh2⟩ := xh
    obtain ⟨yh1,yh2⟩ := yh
    have ax: arccos (cos x) = x := by{
      exact arccos_cos z xh2
    }
    have ay: arccos (cos y) = y := by{
      exact arccos_cos r yh2
    }
    rw[← ax,← ay,yx]
  }
  have : ∫ (x : ℝ) in s, -f' x * g (ff x) = ∫ (x : ℝ) in s, |f' x| • g (ff x) := by{
    simp
    apply setIntegral_congr
    exact hs
    intro x xs
    simp
    ring
    simp
    have : sin x = |sin x| := by{
      have : 0 ≤ sin x := by{
        unfold s at xs
        simp at xs
        refine sin_nonneg_of_mem_Icc ?hx
        simp
        obtain ⟨xs1,xs2⟩ := xs
        constructor
        exact le_of_lt xs1
        assumption
      }
      exact Eq.symm (abs_of_nonneg this)
    }
    rw[this]
    simp
    ring
  }
  rw[this]
  rw[← integral_image_eq_integral_abs_deriv_smul hs hf' hf g]
  have : ff '' s = Ico (-1) 1 := by{
    ext x
    unfold ff s
    simp
    constructor
    intro h
    obtain ⟨y,yh1,yh2⟩ := h
    rw[← yh2]
    constructor
    exact neg_one_le_cos y
    by_contra p
    simp at p
    have t: cos y = 1 := by{
      apply le_antisymm
      exact cos_le_one y
      assumption
    }
    obtain ⟨yh11,yh12⟩ := yh1
    clear this gdef ffdef h s sdef hs hf hf' f'_def f' f g ff p x yh2
    have : 0 ≤ y := by{
      exact le_of_lt yh11
    }
    have : arccos (cos y) = y := by{
      exact arccos_cos this yh12
    }
    rw[← this,t] at yh11
    simp at yh11

    intro h
    use arccos x
    constructor
    constructor
    refine arccos_pos.mpr ?h.left.left.a
    exact h.2
    exact arccos_le_pi x
    refine cos_arccos ?h.right.hx₁ ?h.right.hx₂
    exact h.1
    obtain ⟨h1,h2⟩ := h
    exact le_of_lt h2
  }
  rw[this]
  simp at *
  unfold g
  clear this gdef ffdef f'_def sdef hf hf' hs h f'
  clear this s ff g
  rw [@integral_Ico_eq_integral_Ioo]
  rw [@integral_Ioc_eq_integral_Ioo]
  }
