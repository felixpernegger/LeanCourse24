import LeanCourse.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow

noncomputable section
open BigOperators Function Set Real Filter Classical Topology TopologicalSpace


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 10.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 3.12.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

/- You can use `filter_upwards` to conveniently conclude `Eventually` statements from `Eventually`
in one or more hypotheses using the same filter. -/
example {ι : Type*} {L : Filter ι} {f g : ι → ℝ} (h1 : ∀ᶠ i in L, f i ≤ g i)
    (h2 : ∀ᶠ i in L, g i ≤ f i) : ∀ᶠ i in L, f i = g i := by
  filter_upwards [h1, h2] with i h1 h2
  exact le_antisymm h1 h2

example {ι : Type*} {L : Filter ι} {a b : ι → ℤ} (h1 : ∀ᶠ i in L, a i ≤ b i + 1)
    (h2 : ∀ᶠ i in L, b i ≤ a i + 1) (h3 : ∀ᶠ i in L, b i ≠ a i) : ∀ᶠ i in L, |a i - b i| = 1 := by {
  filter_upwards [h1,h2,h3]
  intro u uh1 uh2 uh3
  by_cases h0: 2 ≤ abs (a u - b u)
  apply le_abs.1 at h0
  exfalso
  obtain h0|h0 := h0
  linarith
  linarith
  have : abs (a u - b u) < 2 := by linarith
  clear h0
  have g: 0 ≤ abs (a u - b u) := by exact abs_nonneg (a u - b u)
  have h: abs (a u - b u) = 1 ∨ abs (a u - b u) = 0 := by{
    by_cases p: 1 ≤ abs (a u - b u)
    left
    linarith
    right
    linarith
  }
  obtain h|h := h
  assumption
  exfalso
  have : a u - b u = 0 := by exact abs_eq_zero.mp h
  have : b u = a u := by linarith
  contradiction
  }

/- The goal of the following exercise is to prove that
the regular open sets in a topological space form a complete boolean algebra.
`U ⊔ V` is given by `interior (closure (U ∪ V))`.
`U ⊓ V` is given by `U ∩ V`. -/


variable {X : Type*} [TopologicalSpace X]

variable (X) in
structure RegularOpens where
  carrier : Set X
  isOpen : IsOpen carrier
  regular' : interior (closure carrier) = carrier

namespace RegularOpens

/- We write some lemmas so that we can easily reason about regular open sets. -/
variable {U V : RegularOpens X}

instance : SetLike (RegularOpens X) X where
  coe := RegularOpens.carrier
  coe_injective' := fun ⟨_, _, _⟩ ⟨_, _, _⟩ _ => by congr

theorem le_def {U V : RegularOpens X} : U ≤ V ↔ (U : Set X) ⊆ (V : Set X) := by simp
@[simp] theorem regular {U : RegularOpens X} : interior (closure (U : Set X)) = U := U.regular'

@[simp] theorem carrier_eq_coe (U : RegularOpens X) : U.1 = ↑U := rfl

@[ext] theorem ext (h : (U : Set X) = V) : U = V :=
  SetLike.coe_injective h


/- First we want a complete lattice structure on the regular open sets.
We can obtain this from a so-called `GaloisCoinsertion` with the closed sets.
This is a pair of maps
* `l : RegularOpens X → Closeds X`
* `r : Closeds X → RegularOpens X`
with the properties that
* for any `U : RegularOpens X` and `C : Closeds X` we have `l U ≤ C ↔ U ≤ r U`
* `r ∘ l = id`
If you know category theory, this is an *adjunction* between orders
(or more precisely, a coreflection).
-/

/- The closure of a regular open set. Of course mathlib knows that the closure of a set is closed.
(the `simps` attribute will automatically generate the simp-lemma for you that
`(U.cl : Set X) = closure (U : Set X)`
-/
@[simps]
def cl (U : RegularOpens X) : Closeds X :=
  ⟨closure U, by{ exact isClosed_closure}⟩

/- The interior of a closed set. You will have to prove yourself that it is regular open. -/
@[simps]
def _root_.TopologicalSpace.Closeds.int (C : Closeds X) : RegularOpens X :=
  ⟨interior C, by{
    exact isOpen_interior
  }, by{
    ext x
    constructor
    intro xh
    rw[mem_interior] at *
    obtain ⟨t,th1,th2,th3⟩ := xh
    use t
    constructor
    swap
    constructor
    assumption
    assumption

    have : closure (interior ↑C) ⊆ (↑C : Set X) := by{
      intro x xh
      clear th1 U V t th2 th3
      unfold closure at xh
      simp at xh
      exact xh C C.2 interior_subset
    }
    exact fun ⦃a⦄ a_1 ↦ this (th1 a_1)
    intro h
    rw[mem_interior]
    use interior ↑C
    constructor
    exact subset_closure
    constructor
    simp
    assumption
  }⟩

/- Now let's show the relation between these two operations. -/
lemma cl_le_iff {U : RegularOpens X} {C : Closeds X} :
    U.cl ≤ C ↔ U ≤ C.int := by{
      have uwu: interior (closure (↑U : Set X)) = (↑U : Set X) := by simp
      have s1: (↑C.int : Set X) = interior ↑C := rfl
      have s2: (↑U.cl : Set X) = closure ↑U := rfl
      constructor
      intro h
      rw[le_def]
      have t1: (↑U.cl : Set X) ⊆ ↑C := by{
        rw[s2]
        assumption
      }
      rw[s1]
      rw[s2] at t1
      have go: interior (closure (↑U : Set X)) ⊆ interior (↑C : Set X) := by exact interior_mono h
      rw[uwu] at go
      assumption

      intro h
      have : ↑U.cl ⊆ (↑C : Set X) := by{
        rw[le_def] at h
        rw[s1] at h
        rw[s2]
        have my: closure ↑U ⊆ closure (interior (↑C : Set X)) := by exact closure_mono h
        have yay: closure (interior ↑C) ⊆ (↑C : Set X) := by{
          intro x xh
          unfold closure at xh
          have : IsClosed (↑C : Set X) ∧ interior (↑C : Set X) ⊆ ↑C := by{
            constructor
            exact Closeds.closed C
            exact interior_subset
          }
          exact xh C this
        }
        exact fun ⦃a⦄ a_1 ↦ yay (my a_1)
      }
      exact this
    }

@[simp] lemma cl_int : U.cl.int = U := by{
  have s1: interior U.cl = (↑U.cl.int : Set X):= rfl
  have s2: U.cl = closure (↑U : Set X) := rfl
  ext x
  constructor
  intro h
  rw[←  s1] at h
  rw[s2] at h
  simp at h
  assumption
  intro h
  rw[← s1,s2]
  simp
  assumption
  }

/- This gives us a GaloisCoinsertion. -/

def gi : GaloisCoinsertion cl (fun C : Closeds X ↦ C.int) where
  gc U C := cl_le_iff
  u_l_le U := by simp
  choice C hC := C.int
  choice_eq C hC := rfl

/- It is now a general theorem that we can lift the complete lattice structure from `Closeds X`
to `RegularOpens X`. The lemmas below give the definitions of the lattice operations. -/

instance completeLattice : CompleteLattice (RegularOpens X) :=
  GaloisCoinsertion.liftCompleteLattice gi

@[simp] lemma coe_inf {U V : RegularOpens X} : ↑(U ⊓ V) = (U : Set X) ∩ V := by
  have : U ⊓ V = (U.cl ⊓ V.cl).int := rfl
  simp [this]

@[simp] lemma coe_sup {U V : RegularOpens X} : ↑(U ⊔ V) = interior (closure ((U : Set X) ∪ V)) := by
  have : U ⊔ V = (U.cl ⊔ V.cl).int := rfl
  simp [this]

@[simp] lemma coe_top : ((⊤ : RegularOpens X) : Set X) = univ := by
  have : (⊤ : RegularOpens X) = (⊤ : Closeds X).int := rfl
  simp [this]

@[simp] lemma coe_bot : ((⊥ : RegularOpens X) : Set X) = ∅ := by
  have : (⊥ : RegularOpens X) = (⊥ : Closeds X).int := rfl
  simp [this]

@[simp] lemma coe_sInf {U : Set (RegularOpens X)} :
    ((sInf U : RegularOpens X) : Set X) =
    interior (⋂₀ ((fun u : RegularOpens X ↦ closure u) '' U)) := by
  have : sInf U = (sInf (cl '' U)).int := rfl
  simp [this]

@[simp] lemma Closeds.coe_sSup {C : Set (Closeds X)} : ((sSup C : Closeds X) : Set X) =
    closure (⋃₀ ((↑) '' C)) := by
  have : sSup C = Closeds.closure (sSup ((↑) '' C)) := rfl
  simp [this]

@[simp] lemma coe_sSup {U : Set (RegularOpens X)} :
    ((sSup U : RegularOpens X) : Set X) =
    interior (closure (⋃₀ ((fun u : RegularOpens X ↦ closure u) '' U))) := by
  have : sSup U = (sSup (cl '' U)).int := rfl
  simp [this]

/- We still have to prove that this gives a distributive lattice.
Warning: these are hard. -/
instance completeDistribLattice : CompleteDistribLattice (RegularOpens X) :=
  CompleteDistribLattice.ofMinimalAxioms
  { completeLattice with
    inf_sSup_le_iSup_inf := by sorry
    iInf_sup_le_sup_sInf := by sorry
    }

/- Finally, we can show that the regular open subsets form a complete Boolean algebra.
Define `compl` and`coe_compl` holds and complete the instance below. -/

structure CompleteBooleanAlgebra.MinimalAxioms (α : Type*) extends
    CompleteDistribLattice.MinimalAxioms α, HasCompl α where
  inf_compl_le_bot : ∀ (x : α), x ⊓ xᶜ ≤ ⊥
  top_le_sup_compl : ∀ (x : α), ⊤ ≤ x ⊔ xᶜ

abbrev CompleteBooleanAlgebra.ofMinimalAxioms {α : Type*}
    (h : CompleteBooleanAlgebra.MinimalAxioms α) : CompleteBooleanAlgebra α where
      __ := h
      le_sup_inf x y z :=
        let z := CompleteDistribLattice.ofMinimalAxioms h.toMinimalAxioms
        le_sup_inf


instance : HasCompl (RegularOpens X) where
  compl U := sorry

@[simp] lemma coe_compl (U : RegularOpens X) : ↑Uᶜ = interior (U : Set X)ᶜ := by{
  ext x
  constructor
  intro xh
  rw[mem_interior]
  sorry
  intro xh
  contrapose xh
  simp at *
  have : x ∈ U := by{
    contrapose xh
    simp at *
    sorry
    }
  apply subset_closure
  assumption
}

instance : CompleteBooleanAlgebra (RegularOpens X) :=
  { inferInstanceAs (CompleteDistribLattice (RegularOpens X)) with
    inf_compl_le_bot := by simp
    top_le_sup_compl := by{
      simp
      intro U
      ext x
      rw[coe_sup]
      rw[coe_top]
      constructor
      intro
      trivial
      intro xh
      --somehow i cannot type complement correctly
      have : (↑U ∪ (↑(@compl (RegularOpens X) Order.Frame.toHasCompl U : RegularOpens X) : Set X)) = univ := by{
        ext x
        constructor
        intro
        trivial
        intro xh
        simp
        by_cases p: x ∈ (↑U : Set X)
        left
        assumption

        right
        #check mem_compl_iff
        apply (mem_compl_iff (↑U : Set X) x).2 at p
        sorry
      }
      rw[this]
      rw[mem_interior]
      use univ
      constructor
      swap
      constructor
      simp
      trivial
      intro y yh
      unfold closure
      simp
      intro C cC Cuniv
      rw[Cuniv]
      trivial
    }
    le_sup_inf := by{
      clear U V
      intro U V R
      rw[le_def]
      simp
      intro x xh
      sorry
    }
    sdiff_eq := by{
      clear U V
      intro U V
      ext x
      simp
      constructor
      intro xh
      obtain ⟨T,⟨Th1,Th2⟩,Th3⟩ := xh
      simp at *
      have ll: ∀ (i : RegularOpens X), U ≤ V ⊔ i → x ∈ closure ↑i := by exact fun i a ↦ Th2 i a Th3
      clear T Th3 Th1 Th2
      simp at ll
      sorry

      intro xh
      sorry
    }
    himp_eq := by{
      clear U V
      intro U V
      ext x
      simp
      constructor
      intro xh
      obtain ⟨A,hA⟩ := xh
      simp at hA
      sorry
      sorry
    }
  }

instance completeBooleanAlgebra : CompleteBooleanAlgebra (RegularOpens X) :=
  CompleteBooleanAlgebra.ofMinimalAxioms {
    inf_sSup_le_iSup_inf := completeDistribLattice.inf_sSup_le_iSup_inf
    iInf_sup_le_sup_sInf := completeDistribLattice.iInf_sup_le_sup_sInf
    inf_compl_le_bot := by
      sorry
    top_le_sup_compl := by
      sorry
  }

/-! # Exercises to hand-in. -/

/- Here is a technical property using filters, characterizing when a 2-valued function converges to
a filter of the form `if q then F else G`. The next exercise is a more concrete application.
Useful lemmas here are
* `Filter.Eventually.filter_mono`
* `Filter.Eventually.mono` -/
lemma technical_filter_exercise {ι α : Type*} {p : ι → Prop} {q : Prop} {a b : α}
    {L : Filter ι} {F G : Filter α}
    (hbF : ∀ᶠ x in F, x ≠ b) (haG : ∀ᶠ x in G, x ≠ a) (haF : pure a ≤ F) (hbG : pure b ≤ G) :
    (∀ᶠ i in L, p i ↔ q) ↔
    Tendsto (fun i ↦ if p i then a else b) L (if q then F else G) := by {
  have hab : a ≠ b
  · have ah : ∀ᶠ (x : α) in (pure a), x ≠ b := by{
    exact haF hbF
    }
    have bh : ∀ᶠ (x : α) in (pure b), x ≠ a := by{
    exact hbG haG
    }
    by_contra ab
    rw[ab] at ah bh haF haG
    clear a ab
    have : b ≠ b := by{
      exact ah
    }
    tauto
  rw [tendsto_iff_eventually]
  constructor
  intro r t h
  filter_upwards [r] with u uh
  rw[uh]
  clear u uh
  clear r
  clear p L ι
  by_cases h0: q
  simp [h0] at *
  exact haF h
  simp [h0] at *
  exact hbG h

  intro u
  by_cases h0: q
  simp [h0] at u
  simp [h0]
  let r := fun x ↦ x ≠ b
  have : ∀ᶠ (x : α) in F, r x := by{
    unfold r
    assumption
  }
  specialize u this
  filter_upwards [u] with i j
  by_cases h0: p i
  assumption
  exfalso
  simp [h0] at *
  unfold r at j
  tauto


  simp [h0] at u
  simp [h0]
  let r := fun x ↦ x ≠ a
  have : ∀ᶠ (x : α) in G, r x := by{
    unfold r
    assumption
  }
  specialize u this
  filter_upwards [u] with i j
  by_cases h0: p i
  exfalso
  simp [h0] at *
  unfold r at j
  tauto
  assumption
  }

/- To be more concrete, we can use the previous lemma to prove the following.
if we denote the characteristic function of `A` by `1_A`, and `f : ℝ → ℝ` is a function,
then  `f * 1_{s i}` tends to `f * 1_t` iff `x ∈ s i` is eventually equivalent to
`x ∈ t` for all `x`. (note that this does *not* necessarily mean that `s i = t` eventually).
`f * 1_t` is written `indicator t f` in Lean.
Useful lemmas for this exercise are `indicator_apply`, `apply_ite` and `tendsto_pi_nhds`. -/
lemma tendsto_indicator_iff {ι : Type*} {L : Filter ι} {s : ι → Set ℝ} {t : Set ℝ} {f : ℝ → ℝ}
    (ha : ∀ x, f x ≠ 0) :
    (∀ x, ∀ᶠ i in L, x ∈ s i ↔ x ∈ t) ↔
    Tendsto (fun i ↦ indicator (s i) f) L (𝓝 (indicator t f)) := by {

  have : ∀(x : ℝ), ∀ᶠ (i : ι) in L, x ∈ s i ↔ x ∈ t ↔ Tendsto (fun i ↦ (s i).indicator f x) L (𝓝 (t.indicator f x)) := by{
    --(∀ᶠ (i : ι) in L, p i ↔ q) ↔ Tendsto (fun i ↦ if p i then a else b) L (if q then F else G)
    intro x
    rw[indicator_apply]
    specialize ha x
    have : (∀ᶠ (i : ι) in L, x ∈ s i ↔ x ∈ t) ↔ Tendsto (fun i ↦ if x ∈ (s i) then f x else 0) L (𝓝 (if x ∈ t then f x else 0)) := by{
      have : 𝓝 (if x ∈ t then f x else 0) = if x ∈ t then 𝓝 (f x) else 𝓝 (0) := by{
        exact apply_ite 𝓝 (x ∈ t) (f x) 0
      }
      rw[this]
      clear this
      have t1: pure (f x) ≤ 𝓝 (f x) := by{
        exact intervalIntegral.FTCFilter.pure_le
      }
      have t2: pure (@OfNat.ofNat ℝ 0 Zero.toOfNat0) ≤ 𝓝 (0) := by{
        exact Specializes.pure_le_nhds fun ⦃U⦄ a ↦ a
      }
      have s1 : ∀ᶠ y in 𝓝 (f x), y ≠ 0 := by{
        exact ContinuousAt.eventually_ne (fun ⦃U⦄ a ↦ a) ha
      }
      have s2 : ∀ᶠ y in 𝓝 (0), y ≠ f x := by{
        exact ContinuousAt.eventually_ne (fun ⦃U⦄ a ↦ a) (id (Ne.symm ha))
      }
      exact technical_filter_exercise s1 s2 t1 t2
    }
    exact this
  }
  constructor
  intro h
  refine tendsto_pi_nhds.mpr ?mp.a
  intro x
  specialize this x
  specialize h x
  apply this.1
  assumption

  intro h
  intro x
  specialize this x
  apply this.2
  exact Tendsto.apply_nhds h x
  }
