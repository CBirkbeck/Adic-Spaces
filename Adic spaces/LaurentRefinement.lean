/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».RationalRefinement
import «Adic spaces».RationalSubsets
import «Adic spaces».TopologyComparison
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-!
# Laurent Covers and Tate Acyclicity Infrastructure

Infrastructure for proving IsSheafy (Wedhorn Theorem 8.28) via the
faithful flatness route (Corollary 8.31).

## Key facts (from reviewer):
- `1-sX` is NOT prime in `A⟨X⟩` in general (it can be a unit when s is
  topologically nilpotent). So `presheafValue D₀` is NOT a domain in general.
- The correct route: `1-sX` is a NON-ZERO-DIVISOR (regular) on `M⟨X⟩`
  for any module M. This gives flatness of `A⟨X⟩/(1-sX)` over A
  (Wedhorn Lemma 8.30, proved in `flat_quotient_oneSubfX_general`).
- IsSheafy follows from: Prop 8.15 (localization principle) + Cor 8.31
  (product restriction is faithfully flat) + Laurent cover exactness.

## Main results

* `rationalOpen_eq_iInter_singleton` : Lemma 7.54 (rational decomposition)
* `laurentCovering` : 2-element Laurent cover construction
* `rationalCovering_hasSeparation` : separation via faithful flatness
* `rationalCovering_hasGluing` : gluing via Laurent exactness

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 7.54, 8.30, 8.31,
  Corollary 8.31, Proposition 8.15, Theorem 8.28
-/

open Classical

noncomputable section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-! ### Lemma 7.54: rational decomposition into singletons -/

/-- **Lemma 7.54 of Wedhorn**: `R({t₁,...,tₙ}/s) = ⋂ᵢ R({tᵢ}/s)` for nonempty T. -/
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

/-- The "plus half" of the Laurent cover at `f` within base `D₀`. -/
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

/-- The "minus half" of the Laurent cover at `f` within base `D₀`. -/
noncomputable def laurentMinusDatum (D₀ : RationalLocData A) (f : A) :
    RationalLocData A where
  P := D₀.P
  T := (insert D₀.s D₀.T).product ({D₀.s, f} : Finset A) |>.image (fun p => p.1 * p.2)
  s := D₀.s * f
  hopen := by sorry -- locSubring closure for product denominator

/-- The plus half is contained in the base. -/
theorem laurentPlus_subset (D₀ : RationalLocData A) (f : A) :
    rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s := by
  intro v ⟨hv, hvT, hvs⟩
  refine ⟨hv, fun t ht => hvT t (Finset.mem_insert_of_mem ht), hvs⟩

open scoped Pointwise in
/-- The minus half is contained in the base. -/
theorem laurentMinus_subset (D₀ : RationalLocData A) (f : A) :
    rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s := by
  have hT : (laurentMinusDatum D₀ f).T = insert D₀.s D₀.T * ({D₀.s, f} : Finset A) := by
    simp only [laurentMinusDatum, Finset.mul_def]; rfl
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
  · left
    exact ⟨hvspa, fun t ht => by
      rcases Finset.mem_insert.mp ht with rfl | ht'
      · exact h
      · exact hvT t ht', hvs⟩
  · right
    open scoped Pointwise in
    rw [show rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s =
      rationalOpen (insert D₀.s D₀.T) D₀.s ∩ rationalOpen {D₀.s, f} f from by
        simp only [laurentMinusDatum]
        rw [show Finset.image (fun p => p.1 * p.2) (Finset.product (insert D₀.s D₀.T) {D₀.s, f})
          = insert D₀.s D₀.T * ({D₀.s, f} : Finset A) from by simp [Finset.mul_def]]
        rw [← rationalOpen_inter (insert D₀.s D₀.T) {D₀.s, f} D₀.s f
          (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))]]
    rw [rationalOpen_insert_s]
    exact ⟨⟨hvspa, hvT, hvs⟩, ⟨hvspa, fun t ht => by
      rcases Finset.mem_insert.mp ht with rfl | ht'
      · exact h
      · rw [Finset.mem_singleton.mp ht']; exact v.vle_refl f,
      fun hf0 => hvs (v.vle_trans h hf0)⟩⟩

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

/-! ### IsSheafy via faithful flatness (Wedhorn Corollary 8.31)

The correct proof route (per reviewer):
1. `1-sX` is regular on `M⟨X⟩` (Wedhorn Lemma 8.30) — gives flatness
2. Prop 8.15: presheafValue D = rational localization of presheafValue D₀
3. Cor 8.31: product restriction is faithfully flat for finite rational covers
4. Faithfully flat → injective → embedding (field 1 of IsSheafy)
5. Laurent cover Čech exactness → gluing (field 2 of IsSheafy)

Key existing results:
- `flat_quotient_oneSubfX_general` : A⟨X⟩/(1-sX) flat over A (0 sorry)
- `presheafValue_flat_of_tateQuotient` : presheafValue D flat over A (0 sorry)
- `epsilonHom_gen_injective` : Laurent separation (0 sorry)
- `laurentCover_exact` : full Laurent exactness (discrete, 0 sorry)

NOTE: `1-sX` is NOT prime in general (can be a unit when s is top. nilpotent).
So presheafValue D₀ is NOT necessarily a domain. The proof uses flatness
and faithful flatness, NOT the domain/localization argument. -/

/-- **Separation via faithful flatness** (Wedhorn Cor. 8.31).

For a strongly noetherian Tate ring, every rational covering has the
separation property: the product restriction is injective.

The proof uses:
1. Each presheafValue D is flat over A (`presheafValue_flat_of_tateQuotient`)
2. The product of presheafValues for a covering is faithfully flat over A
   (the covering condition gives surjectivity on Spec)
3. Faithfully flat → the algebra map A → ∏ presheafValue D is injective
4. The product restriction from presheafValue C.base factors through this
5. Prop 8.15 identifies presheafValue D with rational localization of
   presheafValue C.base, making the restriction faithfully flat over the base

Step 5 requires the localization principle (Prop 8.15). -/
theorem rationalCovering_hasSeparation
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [FirstCountableTopology A] [IsDomain A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) :
    ∀ x y : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x =
        restrictionMap C.base D (C.hsubset D hD) y) → x = y := by
  sorry -- Wedhorn Cor 8.31: faithful flatness of product restriction
        -- Needs: Prop 8.15 (localization principle) + covering → faithfully flat

/-- **Gluing for rational coverings** (Wedhorn Theorem 8.28).

Given compatible sections on cover pieces, produce a global section.
Uses Laurent cover exactness + refinement + Prop 8.15. -/
theorem rationalCovering_hasGluing
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [FirstCountableTopology A] [IsDomain A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A)
    (f : ∀ (D : ↥C.covers), presheafValue D.1)
    (hcompat : ∀ (D₁ D₂ : ↥C.covers)
       (D₃ : RationalLocData A)
       (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
       (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
       restrictionMap D₁.1 D₃ h₃₁ (f D₁) =
         restrictionMap D₂.1 D₃ h₃₂ (f D₂)) :
    ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D := by
  sorry -- Čech gluing: Laurent exactness + localization principle + refinement

-- The embedding theorem (Topology.IsEmbedding) is stated in StructureSheaf.lean
-- since it uses `productRestrictionSub` defined there.

end ValuationSpectrum

end
