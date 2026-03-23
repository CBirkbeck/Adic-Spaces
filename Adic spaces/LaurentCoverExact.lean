/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Localization.Away.Basic
import «Adic spaces».TateAlgebra

/-!
# Laurent Cover Exactness (Wedhorn Lemma 8.33)

For any element `f ∈ A` (in a strongly noetherian Tate ring), the 2-element
Laurent cover yields an exact sequence:

  `0 → A → B₁ × B₂ → B₁₂ → 0`

where:
- `B₁ = A⟨ζ⟩/(f-ζ)` (presheaf at `R(f/1)`)
- `B₂ = A⟨η⟩/(1-fη)` (presheaf at `R(1/f)`)
- `B₁₂ = A⟨ζ,ζ⁻¹⟩/(f-ζ)` (presheaf at `R(f/1) ∩ R(1/f)`)

## Discrete case

For `[DiscreteTopology A]`:
- `B₁ ≅ A` (via `quotientFSubXEquiv`)
- `B₂ ≅ Localization.Away f` (via `quotientOneSubfXEquiv`)
- `B₁₂ ≅ Localization.Away f`
- The exact sequence becomes: `0 → A → A × A[1/f] → A[1/f] → 0`

This is the standard Čech complex for the cover `Spec A = D(f) ∪ Spec A`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 8.33
-/

open TateAlgebra LaurentTateAlgebra

namespace LaurentCover

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-! ### The Laurent cover maps (Row 2 of the 3×3 diagram) -/

/-- The diagonal embedding `ι : A → A⟨ζ⟩ × A⟨η⟩` sending `a ↦ (a, a)`. -/
noncomputable def iotaHom :
    A →+* ↥(TateAlgebra A) × ↥(TateAlgebra A) :=
  RingHom.prod (algebraMap A ↥(TateAlgebra A)) (algebraMap A ↥(TateAlgebra A))

/-- The difference map `λ : A⟨ζ⟩ × A⟨η⟩ → A⟨ζ, ζ⁻¹⟩` sending
`(g, h) ↦ posEmb(g) - negEmb(h)`. This is an additive group homomorphism. -/
noncomputable def lambdaMap :
    ↥(TateAlgebra A) × ↥(TateAlgebra A) →+ LaurentTateAlgebra A where
  toFun p := posEmbHom p.1 - negEmbHom p.2
  map_zero' := by simp
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring

/-! ### Discrete case: direct exactness via ring isomorphisms -/

section Discrete

variable [DiscreteTopology A] [IsNoetherianRing A]

/-- `B₁ = A⟨X⟩/(f-X)` for the discrete case. -/
noncomputable abbrev B₁ (f : A) :=
  ↥(TateAlgebra A) ⧸ Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X}

/-- `B₂ = A⟨Y⟩/(1-fY)` for the discrete case. -/
noncomputable abbrev B₂ (f : A) :=
  ↥(TateAlgebra A) ⧸ Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X}

/-- The diagonal map `ε : A → B₁ × B₂` from Row 3. -/
noncomputable def epsilonHom (f : A) : A →+* B₁ f × B₂ f :=
  RingHom.prod
    ((Ideal.Quotient.mk _).comp (algebraMap A ↥(TateAlgebra A)))
    ((Ideal.Quotient.mk _).comp (algebraMap A ↥(TateAlgebra A)))

omit [IsNoetherianRing A] in
/-- `ε` is injective: the diagonal embedding into B₁ × B₂ is injective.
For discrete A, B₁ ≅ A via `quotientFSubXEquiv`, and the first projection
composed with this equivalence is the identity. -/
theorem epsilonHom_injective (f : A) : Function.Injective (epsilonHom f) := by
  intro a b hab
  have h1 := (Prod.mk.inj hab).1
  have hcomp : (TateAlgebra.quotientFSubXToA f).comp
      (TateAlgebra.AToQuotientFSubX f) = RingHom.id A :=
    TateAlgebra.quotientFSubXToA_comp_AToQuotientFSubX f
  have ha := RingHom.congr_fun hcomp a
  have hb := RingHom.congr_fun hcomp b
  simp only [RingHom.comp_apply, RingHom.id_apply] at ha hb
  rw [← ha, ← hb]
  exact congr_arg (TateAlgebra.quotientFSubXToA f) h1

/-- The δ map: `B₁ f × B₂ f →+ Localization.Away f` defined as the difference
of the two natural maps to `Localization.Away f`:
- First component: `B₁ f ≅ A → Localization.Away f` (algebraMap composed with equiv)
- Second component: `B₂ f ≅ Localization.Away f` (just the equiv)

This is the second map in the Cech complex for the Laurent cover. -/
noncomputable def deltaMap (f : A) : B₁ f × B₂ f →+ Localization.Away f where
  toFun p :=
    algebraMap A (Localization.Away f) (TateAlgebra.quotientFSubXToA f p.1) -
      TateAlgebra.quotientOneSubfXToLoc f p.2
  map_zero' := by simp [map_zero]
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    ring

omit [IsNoetherianRing A] in
/-- The composition `delta circ epsilon = 0`: the image of `epsilon` lands in the
kernel of `delta`. -/
theorem deltaMap_comp_epsilonHom (f : A) :
    ∀ a : A, deltaMap f (epsilonHom f a) = 0 := by
  intro a
  simp only [deltaMap, epsilonHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    RingHom.prod_apply, RingHom.comp_apply]
  have h1 : TateAlgebra.quotientFSubXToA f
      ((Ideal.Quotient.mk _) (algebraMap A ↥(TateAlgebra A) a)) = a := by
    have := RingHom.congr_fun (TateAlgebra.quotientFSubXToA_comp_AToQuotientFSubX f) a
    simp only [RingHom.comp_apply, RingHom.id_apply, TateAlgebra.AToQuotientFSubX] at this
    exact this
  have h2 : TateAlgebra.quotientOneSubfXToLoc f
      ((Ideal.Quotient.mk _) (algebraMap A ↥(TateAlgebra A) a)) =
      algebraMap A (Localization.Away f) a := by
    simp only [TateAlgebra.quotientOneSubfXToLoc, Ideal.Quotient.lift_mk,
      TateAlgebra.evalInvFHom_algebraMap]
  rw [h1, h2, sub_self]

omit [IsNoetherianRing A] in
/-- The delta map is surjective: given any element of `Localization.Away f`,
we can find a preimage in `B_1 f x B_2 f`. -/
theorem deltaMap_surjective (f : A) : Function.Surjective (deltaMap f) := by
  intro y
  refine ⟨(0, (TateAlgebra.quotientOneSubfXEquiv f).symm (-y)), ?_⟩
  simp only [deltaMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_zero]
  have h : TateAlgebra.quotientOneSubfXToLoc f
      ((TateAlgebra.quotientOneSubfXEquiv f).symm (-y)) = -y :=
    (TateAlgebra.quotientOneSubfXEquiv f).right_inv (-y)
  rw [h]
  ring

omit [IsNoetherianRing A] in
/-- Helper: `quotientOneSubfXToLoc` is injective (it's one direction of an equiv). -/
theorem quotientOneSubfXToLoc_injective (f : A) :
    Function.Injective (TateAlgebra.quotientOneSubfXToLoc f) :=
  (TateAlgebra.quotientOneSubfXEquiv f).injective

omit [IsNoetherianRing A] in
/-- Reverse inclusion: if `delta(b_1, b_2) = 0` then `(b_1, b_2)` is in the range
of `epsilon`. This uses that both equivalences allow us to recover the element
`a` in `A`. -/
theorem ker_deltaMap_le_range_epsilonHom (f : A) :
    ∀ p : B₁ f × B₂ f, deltaMap f p = 0 → ∃ a : A, epsilonHom f a = p := by
  intro ⟨b₁, b₂⟩ h
  simp only [deltaMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
  -- From h: algebraMap(quotientFSubXToA(b₁)) - quotientOneSubfXToLoc(b₂) = 0
  have heq : algebraMap A (Localization.Away f) (TateAlgebra.quotientFSubXToA f b₁) =
      TateAlgebra.quotientOneSubfXToLoc f b₂ := sub_eq_zero.mp h
  set a := TateAlgebra.quotientFSubXToA f b₁
  -- b₁ = AToQuotientFSubX(a) since the equiv round-trips
  have hb₁ : TateAlgebra.AToQuotientFSubX f a = b₁ := by
    change (TateAlgebra.quotientFSubXEquiv f).symm (TateAlgebra.quotientFSubXEquiv f b₁) = b₁
    exact (TateAlgebra.quotientFSubXEquiv f).symm_apply_apply b₁
  -- quotientOneSubfXToLoc(mk(algebraMap a)) = algebraMap(a)
  have himg : TateAlgebra.quotientOneSubfXToLoc f
      ((Ideal.Quotient.mk _) (algebraMap A ↥(TateAlgebra A) a)) =
      algebraMap A (Localization.Away f) a := by
    simp only [TateAlgebra.quotientOneSubfXToLoc, Ideal.Quotient.lift_mk,
      TateAlgebra.evalInvFHom_algebraMap]
  have hb₂ : (Ideal.Quotient.mk _) (algebraMap A ↥(TateAlgebra A) a) = b₂ := by
    apply quotientOneSubfXToLoc_injective f
    rw [himg, heq]
  exact ⟨a, Prod.ext hb₁ hb₂⟩

omit [IsNoetherianRing A] in
/-- **Laurent cover exactness (Wedhorn Lemma 8.33, discrete case).**
The sequence `0 -> A ->[epsilon] B_1 f x B_2 f ->[delta] Localization.Away f -> 0`
is exact:
1. `epsilon` is injective
2. `delta` is surjective
3. `delta circ epsilon = 0` (image of epsilon is contained in kernel of delta)
4. `ker delta` is a subset of `im epsilon` -/
theorem laurentCover_exact (f : A) :
    Function.Injective (epsilonHom f) ∧
    Function.Surjective (deltaMap f) ∧
    (∀ x, deltaMap f (epsilonHom f x) = 0) ∧
    (∀ p, deltaMap f p = 0 → ∃ a, epsilonHom f a = p) :=
  ⟨epsilonHom_injective f,
   deltaMap_surjective f,
   deltaMap_comp_epsilonHom f,
   ker_deltaMap_le_range_epsilonHom f⟩

end Discrete

end LaurentCover
