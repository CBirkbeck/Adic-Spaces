/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».Presheaf
import «Adic spaces».PresheafIdentification
import «Adic spaces».AdicCompletionBridge

/-!
# Tate Ring Structure on Presheaf Values (Wedhorn Proposition 8.15)

For a strongly noetherian Tate ring `(A, A⁺)` with pair of definition `(A₀, I)`,
and a rational localization datum `D₀`, the presheaf value `presheafValue D₀`
carries a natural Tate ring structure:

- **Ring of definition**: The closure of `locSubring` in the completion
- **Ideal of definition**: The closure of `locIdeal` in the completion
- **Topologically nilpotent unit**: The image of the pseudo-uniformizer from A

This enables the "localization principle": the structure presheaf on a rational
subset `R(T/s)` is the structure presheaf of the Tate ring `presheafValue D₀`.

## Main results

* `presheafValue_isTateRing` : `IsTateRing (presheafValue D₀)` (TODO)
* `presheafValue_pairOfDefinition` : The natural pair of definition (TODO)
* `presheafValue_topNilUnit` : Topologically nilpotent unit in presheafValue

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Proposition 8.15, Example 6.38
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A] [HasRestrictionMaps A]

/-! ### Topologically nilpotent unit in presheafValue

If A has a topologically nilpotent unit π (i.e., A is a Tate ring), then
the image of π under canonicalMap is a topologically nilpotent unit in
presheafValue D₀. This is because:
- canonicalMap is a ring hom, so it preserves units
- canonicalMap is continuous, so it preserves topological nilpotency -/

/-- A topologically nilpotent unit in A maps to a topologically nilpotent
unit in `presheafValue D₀` via `canonicalMap`. -/
theorem presheafValue_topNilUnit [IsTateRing A]
    (D₀ : RationalLocData A) :
    ∃ u : (presheafValue D₀)ˣ, IsTopologicallyNilpotent (u : presheafValue D₀) := by
  -- Get the topologically nilpotent unit from A
  obtain ⟨π, hπ⟩ := IsTateRing.exists_topologicallyNilpotent_unit (A := A)
  -- Map π to presheafValue D₀ via canonicalMap
  have hunit : IsUnit (D₀.canonicalMap (π : A)) := (π.isUnit).map D₀.canonicalMap
  -- The image is topologically nilpotent (continuous image of top-nil sequence)
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec]
  -- canonicalMap preserves topological nilpotency (continuous MonoidWithZero hom)
  -- canonicalMap = coeRingHom ∘ algebraMap
  -- Both are continuous, so the composition is continuous
  -- IsTopologicallyNilpotent.map gives the result
  exact hπ.map (canonicalMap_continuous D₀)

/-! ### Pair of definition in presheafValue

The natural pair of definition for `presheafValue D₀`:
- **Ring of definition**: The image of `locSubring` under `coeRingHom`
  (the completion of locSubring sits inside presheafValue as a subring)
- **Ideal of definition**: The image of `locIdeal` under the lifted map

For a Noetherian locSubring with locIdeal-adic topology:
- The completion of locSubring = AdicCompletion(locIdeal, locSubring) (bridge)
- This is a complete open subring of presheafValue
- The image of locIdeal generates the topology

TODO: Construct and verify this pair of definition. -/

/-- The ring of definition inside `presheafValue D₀`: the closure of
`locSubring` in the completion. This is the image of the AdicCompletion
of `locSubring` (via the bridge) embedded into the completion of the
ambient localization.

For Noetherian locSubring with locIdeal-adic topology: the closure
= Completion(locSubring) = AdicCompletion(locIdeal, locSubring). -/
noncomputable def presheafValue_ringOfDef (D₀ : RationalLocData A) :
    Subring (presheafValue D₀) := by
  letI := D₀.uniformSpace
  exact (D₀.coeRingHom.comp (locSubring D₀.P D₀.T D₀.s).subtype).range.topologicalClosure

/-- The ring of definition is open in `presheafValue D₀`.

This follows from locSubring being open in the localization topology:
its image under coeRingHom is open in the completion topology (open
subsets are preserved by dense embeddings for additive subgroups). -/
theorem presheafValue_ringOfDef_isOpen (D₀ : RationalLocData A) :
    IsOpen ((presheafValue_ringOfDef D₀ : Subring (presheafValue D₀)) : Set (presheafValue D₀)) := by
  -- Strategy: show the topological closure of the image of locSubring contains
  -- a 0-neighborhood in the completion, then use AddSubgroup.isOpen_of_mem_nhds.
  letI := D₀.uniformSpace
  letI := D₀.isUniformAddGroup
  letI := D₀.isTopologicalRing
  open Filter Topology in
  -- The localization topology has a 0-neighborhood basis: locNhd n
  have hbasis := (locBasis D₀.P D₀.T D₀.s D₀.hopen).hasBasis_nhds_zero
  -- coe : Localization.Away D₀.s → Completion is a dense inducing
  have hdi : IsDenseInducing
      (D₀.coeRingHom : Localization.Away D₀.s → presheafValue D₀) :=
    UniformSpace.Completion.isDenseInducing_coe
  -- In the completion, nhds 0 has basis: closure(coe '' locNhd n)
  -- (by Bourbaki GT III §3 no.4 Prop 7, using RegularSpace)
  set f := (D₀.coeRingHom : Localization.Away D₀.s → presheafValue D₀) with hf_def
  have hf_zero : f 0 = 0 := map_zero D₀.coeRingHom
  have hbasis_compl : (nhds (0 : presheafValue D₀)).HasBasis (fun _ : ℕ => True)
      (fun n => closure (f '' (locNhd D₀.P D₀.T D₀.s n :
        Set (Localization.Away D₀.s)))) := by
    rw [← hf_zero]
    exact hbasis.hasBasis_of_isDenseInducing hdi
  -- f '' locNhd n ⊆ (coeRingHom ∘ subtype).range (as set)
  have himage_sub : ∀ n,
      f '' (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s)) ⊆
      ((D₀.coeRingHom.comp (locSubring D₀.P D₀.T D₀.s).subtype).range :
        Set (presheafValue D₀)) := by
    intro n x hx
    -- x = f y for some y ∈ locNhd n
    obtain ⟨y, hy, hyx⟩ := hx
    -- y ∈ locNhd n means y = (d : Localization.Away D₀.s) for some d ∈ (locIdeal)^n
    obtain ⟨d, _, hdy⟩ := hy
    -- x = f y = f (subtype d) = (coeRingHom ∘ subtype) d
    refine ⟨d, ?_⟩
    show D₀.coeRingHom ((locSubring D₀.P D₀.T D₀.s).subtype d) = x
    -- hdy : subtype.toAddMonoidHom d = y, which definitionally = subtype d = y
    -- hyx : coeRingHom y = x
    exact show D₀.coeRingHom ((locSubring D₀.P D₀.T D₀.s).subtype d) = x from
      hdy ▸ hyx
  -- closure(f '' locNhd n) ⊆ topologicalClosure(range) = presheafValue_ringOfDef
  have hclosure_sub : ∀ n,
      closure (f '' (locNhd D₀.P D₀.T D₀.s n :
        Set (Localization.Away D₀.s))) ⊆
      (presheafValue_ringOfDef D₀ : Set (presheafValue D₀)) := by
    intro n; exact closure_mono (himage_sub n)
  -- presheafValue_ringOfDef contains a 0-neighborhood
  have hmem_nhds : (presheafValue_ringOfDef D₀ : Set (presheafValue D₀)) ∈
      nhds (0 : presheafValue D₀) :=
    Filter.mem_of_superset (hbasis_compl.mem_of_mem (i := 0) trivial) (hclosure_sub 0)
  -- An additive subgroup containing a 0-neighborhood is open
  change IsOpen ((presheafValue_ringOfDef D₀).toAddSubgroup : Set (presheafValue D₀))
  exact AddSubgroup.isOpen_of_mem_nhds _ hmem_nhds

/-- The ideal of definition inside the ring of definition: the closure
of the image of `locIdeal` in the completion. -/
noncomputable def presheafValue_idealOfDef (D₀ : RationalLocData A) :
    Ideal (presheafValue_ringOfDef D₀) := by
  sorry -- Lift locIdeal to an ideal of the closure

/-- The ideal of definition is finitely generated (locIdeal is f.g. and
Noetherian completion preserves finite generation). -/
theorem presheafValue_idealOfDef_fg (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)] :
    (presheafValue_idealOfDef D₀).FG := by
  sorry -- locIdeal is f.g. → its image in the completion is f.g.

/-- The subspace topology on the ring of definition equals the
ideal-of-definition-adic topology. -/
theorem presheafValue_isAdic (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)] :
    @IsAdic (presheafValue_ringOfDef D₀) _ sorry (presheafValue_idealOfDef D₀) := by
  sorry -- The I-adic topology on the completion of locSubring = subspace topology

/-- **Proposition 8.15 (partial)**: `presheafValue D₀` has a natural
pair of definition, making it a Huber ring. Combined with
`presheafValue_topNilUnit`, this gives `IsTateRing`. -/
theorem presheafValue_pairOfDefinition [IsTateRing A] [IsNoetherianRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)] :
    Nonempty (PairOfDefinition (presheafValue D₀)) := by
  sorry -- Assembly: presheafValue_ringOfDef + presheafValue_idealOfDef
        -- + openness + f.g. + IsAdic

end ValuationSpectrum
