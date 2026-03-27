/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».RationalRefinement
import «Adic spaces».RationalSubsets
import Mathlib.RingTheory.Flat.Basic

/-!
# Laurent Covers as Rational Coverings

For an element `f : A` and a base rational datum `D₀`, we construct the
2-element Laurent covering and prove it covers `rationalOpen D₀`.

Also proves Lemma 7.54: `R(T/s) = ⋂_{t ∈ T} R({t}/s)`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 7.54, Lemma 8.33, Lemma 8.34
-/

open Classical
open scoped Pointwise

noncomputable section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-! ### Lemma 7.54: rational decomposition into singletons -/

/-- **Lemma 7.54 of Wedhorn**: `R({t₁,...,tₙ}/s) = ⋂ᵢ R({tᵢ}/s)` for nonempty T.
A rational subset is the intersection of its singleton components. -/
theorem rationalOpen_eq_iInter_singleton (T : Finset A) (hT : T.Nonempty) (s : A) :
    rationalOpen T s = ⋂ t ∈ T, rationalOpen {t} s := by
  ext v
  simp only [Set.mem_iInter, rationalOpen, Set.mem_setOf_eq,
    Finset.mem_singleton, forall_eq, Set.mem_sep_iff]
  constructor
  · rintro ⟨hv, hvT, hvs⟩ t ht
    exact ⟨hv, hvT t ht, hvs⟩
  · intro h
    obtain ⟨t₀, ht₀⟩ := hT
    exact ⟨(h t₀ ht₀).1, fun t ht => (h t ht).2.1, (h t₀ ht₀).2.2⟩

/-! ### Laurent cover construction -/

variable [HasRestrictionMaps A]

/-- The "plus half" of the Laurent cover at `f` within base `D₀`:
represents `{v ∈ R(D₀) : v(f) ≤ v(s₀)}`. -/
noncomputable def laurentPlusDatum (D₀ : RationalLocData A) (f : A) :
    RationalLocData A where
  P := D₀.P
  T := insert f D₀.T
  s := D₀.s
  hopen := by
    obtain ⟨N, hN⟩ := D₀.hopen
    exact ⟨N, fun b hb => Subring.closure_mono (Set.union_subset_union_right _
      (Set.range_comp_subset_range (fun t : D₀.T => (⟨t, Finset.mem_insert_of_mem t.2⟩ :
        (insert f D₀.T : Finset A))) (fun t => divByS (t : A) D₀.s))) (hN b hb)⟩

/-- The "minus half" of the Laurent cover at `f` within base `D₀`:
represents `{v ∈ R(D₀) : v(s₀) ≤ v(f), v(f) ≠ 0}`. -/
noncomputable def laurentMinusDatum (D₀ : RationalLocData A) (f : A) :
    RationalLocData A where
  P := D₀.P
  T := (insert D₀.s D₀.T).product ({D₀.s, f} : Finset A) |>.image (fun p => p.1 * p.2)
  s := D₀.s * f
  hopen := by
    -- Goal: ∃ N, ∀ b ∈ I^N, divByS (↑b) (s₀ * f) ∈ locSubring P T' (s₀ * f)
    -- where P = D₀.P, T' = (insert s₀ T₀) * {s₀, f}, s₀ = D₀.s, T₀ = D₀.T.
    --
    -- From D₀.hopen we get N₀ with: ∀ b ∈ I^N₀, divByS (↑b) s₀ ∈ locSubring P T₀ s₀.
    -- Using the localization ring hom φ : Away s₀ →+* Away (s₀*f) (since algebraMap s₀
    -- is a unit in Away (s₀*f)), one shows φ maps locSubring P T₀ s₀ into
    -- locSubring P T' (s₀*f) by checking generators: φ(divByS t s₀) = divByS (t*f) (s₀*f)
    -- and t*f ∈ T' for t ∈ T₀. This gives divByS (↑b*f) (s₀*f) ∈ D' for b ∈ I^N₀.
    -- The factorization divByS (↑b) (s₀*f) = divByS (↑b*f) (s₀*f) * divByS s₀ (s₀*f)
    -- then requires divByS s₀ (s₀*f) = 1/f ∈ D', which needs a locSubring closure
    -- argument for the change-of-denominator from s₀ to s₀*f.
    -- Full proof requires a helper lemma (locSubring_invF_mem or similar).
    sorry

/-- The plus half is contained in the base. -/
theorem laurentPlus_subset (D₀ : RationalLocData A) (f : A) :
    rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s := by
  intro v ⟨hv, hvT, hvs⟩
  refine ⟨hv, fun t ht => hvT t (Finset.mem_insert_of_mem ht), hvs⟩

/-- The minus half is contained in the base. -/
theorem laurentMinus_subset (D₀ : RationalLocData A) (f : A) :
    rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s := by
  have hT : (laurentMinusDatum D₀ f).T = insert D₀.s D₀.T * ({D₀.s, f} : Finset A) :=
    Finset.image_mul_product.symm
  rw [show (laurentMinusDatum D₀ f).s = D₀.s * f from rfl, hT,
    ← rationalOpen_inter (insert D₀.s D₀.T) ({D₀.s, f} : Finset A) D₀.s f
      (Finset.mem_insert_self D₀.s D₀.T) (Finset.mem_insert_of_mem (Finset.mem_singleton_self f)),
    rationalOpen_insert_s]
  exact Set.inter_subset_left

/-- The Laurent halves cover the base (valuation trichotomy). -/
theorem laurentCover_covers (D₀ : RationalLocData A) (f : A)
    (v : Spv A) (hv : v ∈ rationalOpen D₀.T D₀.s) :
    v ∈ rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ∨
    v ∈ rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s := by
  obtain ⟨hvspa, hvT, hvs⟩ := hv
  rcases v.vle_total f D₀.s with h | h
  · -- Plus half: v(f) ≤ v(s₀)
    left
    exact ⟨hvspa, fun t ht => by
      rcases Finset.mem_insert.mp ht with rfl | ht'
      · exact h
      · exact hvT t ht', hvs⟩
  · -- Minus half: v(s₀) ≤ v(f)
    right
    have hT : (laurentMinusDatum D₀ f).T = insert D₀.s D₀.T * ({D₀.s, f} : Finset A) :=
      Finset.image_mul_product.symm
    rw [show (laurentMinusDatum D₀ f).s = D₀.s * f from rfl, hT,
      ← rationalOpen_inter (insert D₀.s D₀.T) ({D₀.s, f} : Finset A) D₀.s f
        (Finset.mem_insert_self D₀.s D₀.T)
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self f)),
      rationalOpen_insert_s]
    refine ⟨⟨hvspa, hvT, hvs⟩, hvspa, fun t ht => ?_, fun hf0 => hvs (v.vle_trans h hf0)⟩
    rcases Finset.mem_insert.mp ht with rfl | ht'
    · exact h
    · rw [Finset.mem_singleton.mp ht']; exact v.vle_refl f

/-- The 2-element Laurent covering of `D₀` at element `f`. -/
noncomputable def laurentCovering (D₀ : RationalLocData A) (f : A) :
    RationalCovering A where
  base := D₀
  covers := {laurentPlusDatum D₀ f, laurentMinusDatum D₀ f}
  hsubset D hD := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hD
    exact hD.elim (· ▸ laurentPlus_subset D₀ f) (· ▸ laurentMinus_subset D₀ f)
  hcover v hv := by
    rcases laurentCover_covers D₀ f v hv with h | h
    · exact ⟨_, Finset.mem_insert_self _ _, h⟩
    · exact ⟨_, Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)), h⟩

/-! ### Assembly: Separation via the localization-of-completion bridge

The proof of IsSheafy uses the localization-of-completion theorem:

  `Completion(R⁺[1/s]) ≃+* Completion(R⁺)[1/s']`

where R⁺ = locSubring with I-adic topology, s = denominator element.

From this bridge:
1. Each `presheafValue D ≅ R̂⁺[1/s]` (localization of I-adic completion)
2. `R̂⁺` is flat over `R⁺` (AdicCompletion bridge, 0 sorry)
3. `R̂⁺[1/s]` is flat over `R⁺` (localization preserves flatness)
4. Restriction maps between presheaf values are flat (localization of flat)
5. Product of restrictions is faithfully flat (covering → surjective on Spec)
6. Faithfully flat ⟹ injective ⟹ IsSheafy

The key missing piece is (4): restriction maps are flat over the base
presheaf value. This requires the localization-of-completion isomorphism
(CompletionLocalization.lean). -/

/-- **Product restriction is zero-kernel**: the product of restriction maps
from `presheafValue C.base` to `∏ presheafValue D` is faithfully flat.

Uses: each restriction is flat (restrictionMap_flat) + covering condition
gives surjectivity on Spec. -/
theorem productRestriction_zero_kernel
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [FirstCountableTopology A] [IsDomain A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) (x : presheafValue C.base)
    (hx : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
      restrictionMap C.base D (C.hsubset D hD) x = 0) :
    x = 0 := by
  sorry -- Key: localization-of-completion bridge + density + algebraic injectivity

/-- **Theorem 8.28(b) of Wedhorn**: Every rational covering of a strongly
noetherian Tate ring has the separation property.

Proof: the product restriction is faithfully flat (by `restrictionMap_flat`
+ covering condition), and faithfully flat maps are injective. -/
theorem rationalCovering_hasSeparation
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [FirstCountableTopology A] [IsDomain A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) :
    ∀ x y : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x =
        restrictionMap C.base D (C.hsubset D hD) y) → x = y := by
  intro x y hxy
  have hzero := productRestriction_zero_kernel P C (x - y) (fun D hD => by
    change restrictionMapHom C.base D (C.hsubset D hD) (x - y) = 0
    rw [map_sub, sub_eq_zero]
    exact hxy D hD)
  exact sub_eq_zero.mp hzero

end ValuationSpectrum

end
