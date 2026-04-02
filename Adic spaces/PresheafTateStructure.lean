/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».Presheaf
import «Adic spaces».PresheafIdentification
import «Adic spaces».AdicCompletionBridge
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

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
  [IsHuberRing A]

/-! ### Topologically nilpotent unit in presheafValue

If A has a topologically nilpotent unit π (i.e., A is a Tate ring), then
the image of π under canonicalMap is a topologically nilpotent unit in
presheafValue D₀. This is because:
- canonicalMap is a ring hom, so it preserves units
- canonicalMap is continuous, so it preserves topological nilpotency -/

/-- A topologically nilpotent unit in `A` maps to a topologically nilpotent
unit in `presheafValue D₀` via `canonicalMap`. -/
theorem presheafValue_topNilUnit [IsTateRing A] (D₀ : RationalLocData A) :
    ∃ u : (presheafValue D₀)ˣ, IsTopologicallyNilpotent (u : presheafValue D₀) := by
  obtain ⟨π, hπ⟩ := IsTateRing.exists_topologicallyNilpotent_unit (A := A)
  have hunit : IsUnit (D₀.canonicalMap (π : A)) := π.isUnit.map D₀.canonicalMap
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec]
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

/-- The ring of definition inside `presheafValue D₀`: the topological closure of
the image of `locSubring` under `coeRingHom` in the completion. -/
noncomputable def presheafValue_ringOfDef (D₀ : RationalLocData A) :
    Subring (presheafValue D₀) :=
  letI := D₀.uniformSpace
  (D₀.coeRingHom.comp (locSubring D₀.P D₀.T D₀.s).subtype).range.topologicalClosure

/-- The ring of definition is open in `presheafValue D₀`. -/
theorem presheafValue_ringOfDef_isOpen (D₀ : RationalLocData A) :
    IsOpen ((presheafValue_ringOfDef D₀ : Subring (presheafValue D₀)) :
      Set (presheafValue D₀)) := by
  letI := D₀.uniformSpace; letI := D₀.isUniformAddGroup; letI := D₀.isTopologicalRing
  open Filter Topology in
  have hbasis := (locBasis D₀.P D₀.T D₀.s D₀.hopen).hasBasis_nhds_zero
  set f := (D₀.coeRingHom : Localization.Away D₀.s → presheafValue D₀) with hf_def
  have hbasis_compl : (nhds (0 : presheafValue D₀)).HasBasis (fun _ : ℕ => True)
      (fun n => closure (f '' (locNhd D₀.P D₀.T D₀.s n :
        Set (Localization.Away D₀.s)))) :=
    (map_zero D₀.coeRingHom : f 0 = 0) ▸
      hbasis.hasBasis_of_isDenseInducing UniformSpace.Completion.isDenseInducing_coe
  have himage_sub : ∀ n, f '' (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s)) ⊆
      ((D₀.coeRingHom.comp (locSubring D₀.P D₀.T D₀.s).subtype).range :
        Set (presheafValue D₀)) := by
    intro n x ⟨y, hy, hyx⟩
    obtain ⟨d, _, hdy⟩ := hy
    exact ⟨d, by
      have hdy' : (locSubring D₀.P D₀.T D₀.s).subtype d = y := hdy
      rw [RingHom.comp_apply, hdy']; exact hyx⟩
  have hclosure_sub : ∀ n, closure (f '' (locNhd D₀.P D₀.T D₀.s n :
      Set (Localization.Away D₀.s))) ⊆
      (presheafValue_ringOfDef D₀ : Set (presheafValue D₀)) :=
    fun n => closure_mono (himage_sub n)
  change IsOpen ((presheafValue_ringOfDef D₀).toAddSubgroup : Set (presheafValue D₀))
  exact AddSubgroup.isOpen_of_mem_nhds _
    (Filter.mem_of_superset (hbasis_compl.mem_of_mem (i := 0) trivial) (hclosure_sub 0))

omit [PlusSubring A] in
/-- The subspace uniformity on `locSubring` equals the `locIdeal`-adic uniformity. -/
theorem locSubring_subspace_eq_adic (D₀ : RationalLocData A) :
    UniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype D₀.uniformSpace =
    @IsTopologicalAddGroup.rightUniformSpace _ _
      (locIdeal D₀.P D₀.T D₀.s).adicTopology
      (inferInstance) := by
  letI : TopologicalSpace (Localization.Away D₀.s) := D₀.topology
  letI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  have key : TopologicalSpace.induced (locSubring D₀.P D₀.T D₀.s).subtype D₀.topology =
      (locIdeal D₀.P D₀.T D₀.s).adicTopology := by
    have htag_ind : @IsTopologicalAddGroup (locSubring D₀.P D₀.T D₀.s)
        (TopologicalSpace.induced (locSubring D₀.P D₀.T D₀.s).subtype D₀.topology) _ :=
      @IsTopologicalRing.to_topologicalAddGroup _ _
        (TopologicalSpace.induced (locSubring D₀.P D₀.T D₀.s).subtype D₀.topology)
        (Subring.instIsTopologicalRing (locSubring D₀.P D₀.T D₀.s))
    have htag_adic : @IsTopologicalAddGroup (locSubring D₀.P D₀.T D₀.s)
        (locIdeal D₀.P D₀.T D₀.s).adicTopology _ :=
      @IsTopologicalRing.to_topologicalAddGroup _ _ (locIdeal D₀.P D₀.T D₀.s).adicTopology
        (RingFilterBasis.isTopologicalRing
          (locIdeal D₀.P D₀.T D₀.s).adic_basis.toRing_subgroups_basis.toRingFilterBasis)
    apply @IsTopologicalAddGroup.ext (locSubring D₀.P D₀.T D₀.s) _ _ _ htag_ind htag_adic
    have hbasis_loc := (locBasis D₀.P D₀.T D₀.s D₀.hopen).hasBasis_nhds_zero
    have hpreimage_eq : ∀ n : ℕ,
        (locSubring D₀.P D₀.T D₀.s).subtype ⁻¹'
          (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s)) =
        ((locIdeal D₀.P D₀.T D₀.s ^ n : Ideal (locSubring D₀.P D₀.T D₀.s)) :
          Set (locSubring D₀.P D₀.T D₀.s)) := by
      intro n; ext ⟨x, hx_mem⟩; constructor
      · rintro ⟨d, hd, hd_eq⟩
        have : d = ⟨x, hx_mem⟩ := Subtype.val_injective (by
          change d.val = x; change d.val = _ at hd_eq; exact hd_eq)
        exact this ▸ hd
      · intro hx; exact ⟨⟨x, hx_mem⟩, hx, rfl⟩
    have hbasis_ind :
        (@nhds (locSubring D₀.P D₀.T D₀.s)
          (TopologicalSpace.induced (locSubring D₀.P D₀.T D₀.s).subtype D₀.topology) 0).HasBasis
        (fun _ : ℕ => True) (fun n => ((locIdeal D₀.P D₀.T D₀.s ^ n :
          Ideal (locSubring D₀.P D₀.T D₀.s)) : Set (locSubring D₀.P D₀.T D₀.s))) := by
      rw [nhds_induced, show ((locSubring D₀.P D₀.T D₀.s).subtype :
          (locSubring D₀.P D₀.T D₀.s) → Localization.Away D₀.s) 0 = 0 from map_zero _]
      exact (hbasis_loc.comap (locSubring D₀.P D₀.T D₀.s).subtype).congr
        (fun _ => Iff.rfl) (fun n _ => hpreimage_eq n)
    ext U; rw [hbasis_ind.mem_iff, (locIdeal D₀.P D₀.T D₀.s).hasBasis_nhds_zero_adic.mem_iff]
  apply UniformSpace.ext; rw [uniformity_comap]
  change Filter.comap (Prod.map (locSubring D₀.P D₀.T D₀.s).subtype
      (locSubring D₀.P D₀.T D₀.s).subtype)
    (Filter.comap (fun p : _ × _ => p.2 - p.1) (@nhds _ D₀.topology 0)) =
    Filter.comap (fun p : _ × _ => p.2 - p.1)
      (@nhds _ (locIdeal D₀.P D₀.T D₀.s).adicTopology 0)
  have hcomm :
      (fun p : (Localization.Away D₀.s) × (Localization.Away D₀.s) => p.2 - p.1) ∘
      (Prod.map (locSubring D₀.P D₀.T D₀.s).subtype (locSubring D₀.P D₀.T D₀.s).subtype) =
      (locSubring D₀.P D₀.T D₀.s).subtype ∘
      (fun p : _ × _ => p.2 - p.1) := by
    ext ⟨a, b⟩; exact (map_sub (locSubring D₀.P D₀.T D₀.s).subtype b a).symm
  rw [Filter.comap_comap, hcomm, ← Filter.comap_comap]; congr 1
  conv_lhs => rw [show (0 : Localization.Away D₀.s) =
    (locSubring D₀.P D₀.T D₀.s).subtype 0 from (map_zero _).symm]
  rw [← nhds_induced, key]

/-- The ring hom from `locSubring` into `presheafValue_ringOfDef D₀`. -/
noncomputable def locSubringToRingOfDef (D₀ : RationalLocData A) :
    locSubring D₀.P D₀.T D₀.s →+* presheafValue_ringOfDef D₀ :=
  letI := D₀.uniformSpace
  (D₀.coeRingHom.comp (locSubring D₀.P D₀.T D₀.s).subtype).codRestrict
    (presheafValue_ringOfDef D₀) fun d =>
    subset_closure (RingHom.mem_range.mpr ⟨d, rfl⟩)

/-- The ideal of definition inside the ring of definition. -/
noncomputable def presheafValue_idealOfDef (D₀ : RationalLocData A) :
    Ideal (presheafValue_ringOfDef D₀) :=
  Ideal.map (locSubringToRingOfDef D₀) (locIdeal D₀.P D₀.T D₀.s)

omit [PlusSubring A] in
/-- The ideal of definition is finitely generated. -/
theorem presheafValue_idealOfDef_fg (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)] :
    (presheafValue_idealOfDef D₀).FG :=
  (locIdeal_fg D₀.P D₀.T D₀.s).map _

omit [PlusSubring A] in
private theorem idealOfDef_pow_sub_val_preimage_closure (D₀ : RationalLocData A) (n : ℕ) :
    ((presheafValue_idealOfDef D₀ ^ n : Ideal (presheafValue_ringOfDef D₀)) :
      Set (presheafValue_ringOfDef D₀)) ⊆
    Subtype.val ⁻¹' closure ((D₀.coeRingHom : Localization.Away D₀.s → presheafValue D₀) ''
      (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s))) := by
  letI := D₀.uniformSpace
  letI := D₀.isUniformAddGroup
  letI := D₀.isTopologicalRing
  let fh := D₀.coeRingHom
  let sub := (locSubring D₀.P D₀.T D₀.s).subtype
  let comp_sub := fh.comp sub
  let g := locSubringToRingOfDef D₀
  set T := (fh : Localization.Away D₀.s → presheafValue D₀) ''
    (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s)) with hT_def
  rw [show presheafValue_idealOfDef D₀ = Ideal.map g (locIdeal D₀.P D₀.T D₀.s) from rfl,
      show (Ideal.map g (locIdeal D₀.P D₀.T D₀.s)) ^ n =
        Ideal.map g ((locIdeal D₀.P D₀.T D₀.s) ^ n) from (Ideal.map_pow _ _ n).symm]
  have hact : ∀ c ∈ (comp_sub.range : Set (presheafValue D₀)), ∀ y ∈ T, c * y ∈ T := by
    rintro c ⟨a, rfl⟩ y ⟨z, hz, rfl⟩
    obtain ⟨d, hd, hdz⟩ := hz
    refine ⟨sub (a * d), ⟨a * d, Ideal.mul_mem_left _ a hd, rfl⟩, ?_⟩
    change fh (sub (a * d)) = comp_sub a * fh z
    have hdz' : sub d = z := hdz
    rw [show sub (a * d) = sub a * sub d from map_mul sub a d,
        map_mul fh, show fh (sub a) = comp_sub a from rfl, hdz']
  have hringOfDef_eq : (presheafValue_ringOfDef D₀ : Set (presheafValue D₀)) =
      closure (comp_sub.range : Set (presheafValue D₀)) := rfl
  intro x hx
  change x.val ∈ closure T
  refine Submodule.span_induction (p := fun x _ => x.val ∈ closure T) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨d, hd, rfl⟩
    exact subset_closure ⟨sub d, ⟨d, hd, rfl⟩, rfl⟩
  · exact subset_closure ⟨0, (locNhd D₀.P D₀.T D₀.s n).zero_mem, map_zero _⟩
  · intro a b _ _ ha hb
    change (a + b).val ∈ closure T
    rw [show (a + b).val = a.val + b.val from rfl]
    exact ((locNhd D₀.P D₀.T D₀.s n).map
      fh.toAddMonoidHom).topologicalClosure.add_mem
      (show a.val ∈ ((locNhd D₀.P D₀.T D₀.s n).map
        fh.toAddMonoidHom).topologicalClosure from ha)
      (show b.val ∈ ((locNhd D₀.P D₀.T D₀.s n).map
        fh.toAddMonoidHom).topologicalClosure from hb)
  · intro ⟨r, hr⟩ x _ hx_ih
    change ((⟨r, hr⟩ : presheafValue_ringOfDef D₀) • x).val ∈ closure T
    change r * x.val ∈ closure T
    exact map_mem_closure₂' (fun _ => continuous_const_mul _) (fun _ => continuous_mul_const _)
      (hringOfDef_eq ▸ hr) hx_ih (fun a ha b hb => hact a ha b hb)

/-- Corollary: the val-image of `idealOfDef^n` is contained in `closure(coe '' locNhd n)`. -/
private theorem idealOfDef_pow_val_sub_closure (D₀ : RationalLocData A) (n : ℕ) :
    Subtype.val '' ((presheafValue_idealOfDef D₀ ^ n : Ideal (presheafValue_ringOfDef D₀)) :
      Set (presheafValue_ringOfDef D₀)) ⊆
    closure ((D₀.coeRingHom : Localization.Away D₀.s → presheafValue D₀) ''
      (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s))) := by
  rintro x ⟨y, hy, rfl⟩
  exact idealOfDef_pow_sub_val_preimage_closure D₀ n hy

omit [PlusSubring A] in
/-- Helper: `coe '' locNhd n ⊆ val '' idealOfDef^n`. The image of `locIdeal^n` generators
under `g = locSubringToRingOfDef` produces elements of `idealOfDef^n` whose `val` coincides
with the corresponding element of `coe '' locNhd n`. -/
private theorem locNhd_sub_idealOfDef_pow_val (D₀ : RationalLocData A) (n : ℕ) :
    (D₀.coeRingHom : Localization.Away D₀.s → presheafValue D₀) ''
      (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s)) ⊆
    Subtype.val '' ((presheafValue_idealOfDef D₀ ^ n : Ideal (presheafValue_ringOfDef D₀)) :
      Set (presheafValue_ringOfDef D₀)) := by
  letI := D₀.uniformSpace
  rw [show presheafValue_idealOfDef D₀ = Ideal.map (locSubringToRingOfDef D₀)
    (locIdeal D₀.P D₀.T D₀.s) from rfl,
    show (Ideal.map (locSubringToRingOfDef D₀) (locIdeal D₀.P D₀.T D₀.s)) ^ n =
      Ideal.map (locSubringToRingOfDef D₀) ((locIdeal D₀.P D₀.T D₀.s) ^ n)
    from (Ideal.map_pow _ _ n).symm]
  intro x ⟨y, hy, hyx⟩
  obtain ⟨d, hd, hdy⟩ := hy
  refine ⟨(locSubringToRingOfDef D₀) d,
    Ideal.mem_map_of_mem _ hd, ?_⟩
  change ((locSubringToRingOfDef D₀) d).val = x
  exact hyx ▸ congrArg D₀.coeRingHom hdy

-- The AdicCompletion bridge proof has deep elaboration chains through ring equivs.
set_option maxHeartbeats 800000 in
/-- `val '' idealOfDef^n` is closed in `presheafValue D₀`.

**Proof strategy** (non-circular, via AdicCompletionBridge):

1. `ringOfDef` is a closed subring of `presheafValue`, giving a closed embedding
   `val : ringOfDef → presheafValue`.
2. Reduce to showing `idealOfDef^n` is closed in the subspace topology on `ringOfDef`.
3. For the subspace closedness: `locSubring_subspace_eq_adic` says the subspace uniformity
   on `locSubring` equals the J-adic uniformity. Via `AdicCompletionBridge.adicCompletionRingEquiv`,
   `Completion(locSubring, J-adic) ≃+* AdicCompletion(J, locSubring)` as a homeomorphism.
4. In `AdicCompletion`: `evalₐ n` is continuous (projects to discrete quotient), so
   `ker(evalₐ n)` is closed. By `AdicCompletion.map_exact` on the exact sequence
   `0 → J^n → locSubring → locSubring/J^n → 0`, `ker(evalₐ n) = Ideal.map of (J^n)`.
5. Under the composed homeomorphism: `idealOfDef^n = Ideal.map g (J^n)` corresponds to
   `Ideal.map of (J^n) = ker(evalₐ n)`, which is closed.

**Why simpler approaches are circular**: The sandwich
`coe '' locNhd n ⊆ val '' idealOfDef^n ⊆ closure(coe '' locNhd n)` gives
`val '' idealOfDef^n = closure(coe '' locNhd n)` only IF we know `val '' idealOfDef^n`
is closed. And `closure_locNhd_sub_idealOfDef_pow` USES this result.

**See also**: `locSubring_subspace_eq_adic`, `AdicCompletionBridge.lean`. -/
private theorem idealOfDef_pow_val_isClosed (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)] (n : ℕ) :
    IsClosed (Subtype.val '' ((presheafValue_idealOfDef D₀ ^ n :
      Ideal (presheafValue_ringOfDef D₀)) :
      Set (presheafValue_ringOfDef D₀)) : Set (presheafValue D₀)) := by
  letI := D₀.uniformSpace; letI := D₀.isUniformAddGroup; letI := D₀.isTopologicalRing
  -- ringOfDef is a closed subring of presheafValue (it's a topological closure)
  have hclosed_ring : IsClosed (presheafValue_ringOfDef D₀ : Set (presheafValue D₀)) :=
    Subring.isClosed_topologicalClosure _
  -- Part (B): reduce to showing idealOfDef^n is closed in ringOfDef.
  -- val : ringOfDef → presheafValue is a closed embedding since ringOfDef is closed.
  apply hclosed_ring.isClosedEmbedding_subtypeVal.isClosedMap
  -- Now need: IsClosed ((idealOfDef^n).carrier) in ringOfDef (subspace topology).
  -- The subspace topology on ringOfDef comes from instUniformSpaceSubtype.
  -- We use Subring.instIsTopologicalRing for the ring topology on the subtype.
  haveI : IsTopologicalRing (presheafValue_ringOfDef D₀) :=
    Subring.instIsTopologicalRing _
  -- Part (A): Show idealOfDef^n is closed in the subspace topology on ringOfDef.
  -- Strategy: build a continuous ring hom π : ringOfDef → locSubring/J^n whose
  -- kernel is idealOfDef^n. Since the target is discrete (hence T₁), the
  -- preimage of {0} is closed, so idealOfDef^n = ker(π) is closed.
  --
  -- The construction uses the J-adic completion of locSubring and the bridge
  -- to AdicCompletion, where AdicCompletion.map_exact gives the kernel identity.
  -- STEP 1: The subspace topology on locSubring = J-adic topology.
  have hadic_eq : TopologicalSpace.induced (locSubring D₀.P D₀.T D₀.s).subtype D₀.topology =
      (locIdeal D₀.P D₀.T D₀.s).adicTopology := by
    have hunif := locSubring_subspace_eq_adic D₀
    have h1 : @UniformSpace.toTopologicalSpace _
        (UniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype D₀.uniformSpace) =
      @UniformSpace.toTopologicalSpace _
        (@IsTopologicalAddGroup.rightUniformSpace _ _
          (locIdeal D₀.P D₀.T D₀.s).adicTopology inferInstance) :=
      congrArg (fun u => @UniformSpace.toTopologicalSpace _ u) hunif
    rw [UniformSpace.toTopologicalSpace_comap] at h1
    exact h1
  -- STEP 2: Show idealOfDef^n = closure(g(J^n)) in ringOfDef, hence closed.
  set J := locIdeal D₀.P D₀.T D₀.s with hJ_def
  set g := locSubringToRingOfDef D₀ with hg_def
  set gJn := g '' (↑(J ^ n) : Set (locSubring D₀.P D₀.T D₀.s)) with hgJn_def
  suffices h_eq : ((presheafValue_idealOfDef D₀ ^ n :
      Ideal (presheafValue_ringOfDef D₀)) : Set (presheafValue_ringOfDef D₀)) =
      closure gJn by
    have : IsClosed (closure gJn) := isClosed_closure
    rwa [← h_eq] at this
  -- DenseRange g: ringOfDef = topological closure of range(g).
  have hg_dense : DenseRange g := by
    intro ⟨z, hz⟩
    have hval_range : Subtype.val '' Set.range g =
        ((D₀.coeRingHom.comp (locSubring D₀.P D₀.T D₀.s).subtype).range :
          Set (presheafValue D₀)) := by
      ext w; constructor
      · rintro ⟨y, ⟨d, hd⟩, hw⟩; exact ⟨d, by rw [← hw, ← hd]; rfl⟩
      · rintro ⟨d, hd⟩; exact ⟨g d, ⟨d, rfl⟩, hd⟩
    have h1 : z ∈ closure (Subtype.val '' Set.range g) := hval_range ▸ hz
    -- closure in induced topology = preimage of closure in ambient
    simp only [closure_subtype]
    exact h1
  -- range(g) * gJn ⊆ gJn (ideal absorption).
  have hact : ∀ a ∈ Set.range g, ∀ b ∈ gJn, a * b ∈ gJn := by
    rintro _ ⟨s, rfl⟩ _ ⟨d, hd, rfl⟩
    exact ⟨s * d, Ideal.mul_mem_left _ s hd, map_mul g s d⟩
  apply Set.Subset.antisymm
  · -- ⊆: idealOfDef^n ⊆ closure(gJn)
    -- span_induction: generators → closure, add → closure, smul → closure (density).
    rw [show presheafValue_idealOfDef D₀ = Ideal.map g J from rfl,
        (Ideal.map_pow g J n).symm]
    intro y hy
    refine Submodule.span_induction (p := fun y _ => y ∈ closure gJn) ?_ ?_ ?_ ?_ hy
    · rintro y ⟨d, hd, rfl⟩; exact subset_closure ⟨d, hd, rfl⟩
    · exact subset_closure ⟨0, (J ^ n).zero_mem, map_zero g⟩
    · intro a b _ _ ha hb
      exact ((J ^ n).toAddSubgroup.map g.toAddMonoidHom).topologicalClosure.add_mem ha hb
    · intro ⟨r, hr_mem⟩ y _ hy
      exact map_mem_closure₂' (fun _ => continuous_const_mul _)
        (fun _ => continuous_mul_const _)
        (hg_dense.closure_eq ▸ Set.mem_univ _) hy hact
  · -- ⊇: closure(gJn) ⊆ idealOfDef^n
    -- Step 1: gJn ⊆ idealOfDef^n (trivial: g(J^n) ⊆ Ideal.map g (J^n)).
    have hgJn_sub : gJn ⊆ ((presheafValue_idealOfDef D₀ ^ n :
        Ideal (presheafValue_ringOfDef D₀)) : Set (presheafValue_ringOfDef D₀)) := by
      rintro _ ⟨d, hd, rfl⟩
      rw [show presheafValue_idealOfDef D₀ = Ideal.map g J from rfl,
          (Ideal.map_pow g J n).symm]
      exact Ideal.mem_map_of_mem g hd
    -- Step 2: idealOfDef^n is closed in the subspace topology on ringOfDef.
    --
    -- **Why this is non-trivial**: We showed idealOfDef^n ⊆ closure(gJn) (⊆ direction).
    -- The closure of gJn equals val⁻¹(closure(coeRingHom '' locNhd n)), which is
    -- OPEN in ringOfDef (preimage of a basic nhd). So closure(gJn) is an open
    -- additive subgroup, hence also closed. But idealOfDef^n ⊆ closure(gJn)
    -- does NOT imply idealOfDef^n is closed.
    --
    -- **Why simpler approaches are circular**: To show closure(gJn) ⊆ idealOfDef^n
    -- (completing the set equality), one needs idealOfDef^n to contain a 0-nhd.
    -- The natural 0-nhd is val⁻¹(closure(coe '' locNhd n)) ⊆ idealOfDef^n, but
    -- establishing ⊇ (closure_locNhd_sub_idealOfDef_pow) uses
    -- idealOfDef_pow_val_isClosed — the very theorem we are proving.
    --
    -- **Required approach (AdicCompletion bridge)**:
    -- 1. locSubring_subspace_eq_adic gives subspace uniformity = J-adic uniformity.
    -- 2. AdicCompletionBridge.adicCompletionRingEquiv gives
    --    Completion(locSubring, J-adic) ≃+* AdicCompletion(J, locSubring).
    -- 3. Identify ringOfDef with Completion(locSubring) via the completion embedding
    --    locSubring → Localization.Away s → presheafValue.
    -- 4. AdicCompletion.map_exact (Mathlib, needs IsNoetherianRing + Module.Finite)
    --    on 0 → J^n → locSubring → locSubring/J^n → 0 gives:
    --    ker(map I g) = range(map I f) where g is the quotient, f is inclusion.
    -- 5. Under the bridge, range(map I f) ↔ closure(g(J^n)) = closure(gJn) in ringOfDef,
    --    and ker(map I g) ↔ ker(evalₐ n) (the kernel of evaluation at level n).
    -- 6. evalₐ n has discrete target (locSubring / J^n), so ker(evalₐ n) is closed.
    -- 7. Therefore idealOfDef^n = closure(gJn) = ker(evalₐ n ∘ bridge) is closed.
    --
    -- This requires ~150 lines of new infrastructure to formalize the identification
    -- in step 3 (Completion(locSubring) ≃ ringOfDef as topological rings) and the
    -- kernel computation in steps 4-5. The AdicCompletionBridge file provides the
    -- ring isomorphism but not yet the specific composition needed here.
    have hclosed : IsClosed ((presheafValue_idealOfDef D₀ ^ n :
        Ideal (presheafValue_ringOfDef D₀)) : Set (presheafValue_ringOfDef D₀)) := by
      -- Proof: idealOfDef^n = ker(π) for a continuous ring hom
      --   π : ringOfDef → locSubring ⧸ (J ^ n)
      -- and ker(π) is closed since the target is discrete (T₁).
      --
      -- Construction of π: g : locSubring → ringOfDef is a dense uniform
      -- inducing (locSubring_subspace_eq_adic). The quotient
      -- q = Ideal.Quotient.mk(J^n) extends to π by the completion universal
      -- property (target is discrete, hence complete T₂).
      --
      -- ker(π) = idealOfDef^n = Ideal.map g (J^n):
      -- (⊆) π is a ring hom (density + T₂) killing g(J^n), so the generated
      --     ideal Ideal.map g (J^n) = idealOfDef^n ⊆ ker(π).
      -- (⊇) By AdicCompletion.map_exact (Mathlib.RingTheory.AdicCompletion.Exactness)
      --     on 0 → J^n → locSubring → locSubring/J^n → 0, using IsNoetherianRing.
      --     Transported through adicCompletionRingEquiv (AdicCompletionBridge.lean).
      --
      -- Proof: idealOfDef^n is closed in ringOfDef because it equals
      -- a closed set in the J-adic completion, transported through two
      -- homeomorphisms. In AdicCompletion J locSubring (bridge topology),
      -- Ideal.map (of J) (J^n) = ker(map J mkQ) (by map_exact for the
      -- SES 0 -> J^n -> locSubring -> locSubring/J^n -> 0, combined with
      -- ofTensorProduct_surjective). ker(map J mkQ) is closed since map J mkQ
      -- is continuous (componentwise quotient maps between discrete types)
      -- and {0} is closed in the T2 target. Transport through the bridge
      -- homeomorphism Completion(locSubring) ~= AdicCompletion(J, locSubring)
      -- and the AbstractCompletion comparison ringOfDef ~= Completion(locSubring)
      -- preserves closedness, giving IsClosed(idealOfDef^n) in ringOfDef.
      --
      -- The composed identification maps of(r) |-> coe(r) |-> g(r) for
      -- r in locSubring, so Ideal.map of (J^n) |-> Ideal.map g (J^n) = idealOfDef^n.
      --
      -- Key Mathlib results used:
      -- * AdicCompletion.map_exact (Exactness.lean): exactness on f.g. modules
      -- * AdicCompletion.ofTensorProduct_surjective_of_finite (AsTensorProduct.lean):
      --   surjectivity identifying range(map) with ideal image
      -- * AdicCompletionBridge.adicCompletionRingEquiv: bridge homeomorphism
      -- * AbstractCompletion.compareEquiv: completion comparison homeomorphism
      --
      -- Step A: g : locSubring -> ringOfDef is IsUniformInducing.
      -- val . g = coeRingHom . subtype is uniform inducing (composition
      -- of Completion.coe and subtype embedding). Since val is a subtype
      -- embedding (hence injective uniform inducing), g is uniform inducing.
      have hg_ui : @IsUniformInducing _ _
          (UniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype D₀.uniformSpace)
          (UniformSpace.comap Subtype.val inferInstance) g := by
        have h_comp : (Subtype.val : presheafValue_ringOfDef D₀ → presheafValue D₀) ∘ g =
            (D₀.coeRingHom : Localization.Away D₀.s → presheafValue D₀) ∘
            (locSubring D₀.P D₀.T D₀.s).subtype := by ext d; rfl
        have h_valg_ui : @IsUniformInducing _ _
            (UniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype D₀.uniformSpace)
            (inferInstance : UniformSpace (presheafValue D₀))
            (Subtype.val ∘ g) := h_comp ▸
          (UniformSpace.Completion.isUniformInducing_coe _).comp ⟨rfl⟩
        -- If h ∘ g is uniform inducing and h is uniform inducing, g is uniform inducing.
        have hval_ui : @IsUniformInducing _ _
            (UniformSpace.comap Subtype.val inferInstance)
            (inferInstance : UniformSpace (presheafValue D₀))
            (Subtype.val : presheafValue_ringOfDef D₀ → presheafValue D₀) := ⟨rfl⟩
        constructor
        rw [← hval_ui.comap_uniformity, Filter.comap_comap]
        exact h_valg_ui.comap_uniformity
      -- Step B: ringOfDef is complete (closed subspace of complete space).
      have hcomplete : @CompleteSpace (presheafValue_ringOfDef D₀)
          (UniformSpace.comap Subtype.val inferInstance) :=
        (Subring.isClosed_topologicalClosure
          (D₀.coeRingHom.comp (locSubring D₀.P D₀.T D₀.s).subtype).range).completeSpace_coe
      -- Step C: Package (g, ringOfDef) as AbstractCompletion of locSubring.
      let pkg : @AbstractCompletion (locSubring D₀.P D₀.T D₀.s)
          (UniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype D₀.uniformSpace) :=
        ⟨_, g, UniformSpace.comap Subtype.val inferInstance,
         hcomplete, inferInstance, hg_ui, hg_dense⟩
      -- Step D: Use completionRingEquiv to build a ring equiv ringOfDef ≃+* Completion.
      -- Then compose with extensionHom (quotient map extended to Completion)
      -- to get a continuous ring hom π : ringOfDef →+* locSubring/J^n.
      -- ker(π) = idealOfDef^n (by ker_evalₐ_eq + ring equiv transport).
      -- Conclude IsClosed from continuous hom to discrete T₁ target.
      -- Ring equiv: ringOfDef ≃+* Completion(locSubring)
      -- (g is continuous: val ∘ g = coeRingHom ∘ subtype, both continuous)
      have hg_cont : Continuous g := by
        have : Continuous (Subtype.val ∘ g : locSubring D₀.P D₀.T D₀.s →
            presheafValue D₀) := UniformSpace.Completion.isDenseInducing_coe.continuous.comp
          continuous_subtype_val
        exact continuous_induced_rng.mpr this
      haveI : IsUniformAddGroup (presheafValue_ringOfDef D₀) :=
        AddSubgroup.isUniformAddGroup (presheafValue_ringOfDef D₀).toAddSubgroup
      haveI : IsUniformAddGroup (locSubring D₀.P D₀.T D₀.s) :=
        AddSubgroup.isUniformAddGroup (locSubring D₀.P D₀.T D₀.s).toAddSubgroup
      let eRE := (AdicCompletionBridge.completionRingEquiv g hg_cont
        hg_ui hg_dense).symm
      -- Extend quotient map to Completion.
      -- Follow TopologyComparison.lean pattern: derive UniformSpace on R/J^n
      -- from the quotient topology via rightUniformSpace (no diamond).
      -- First show the quotient is discrete (J^n is open).
      have htop_eq : (instTopologicalSpaceSubtype :
          TopologicalSpace (locSubring D₀.P D₀.T D₀.s)) = J.adicTopology := by
        change TopologicalSpace.induced _ _ = _; convert hadic_eq using 1
      -- R/J^n is discrete: J^n is open (adic nhd), quotient map is open.
      have hJn_open : IsOpen (SetLike.coe (J ^ n).toAddSubgroup :
          Set (locSubring D₀.P D₀.T D₀.s)) := by
        rw [show instTopologicalSpaceSubtype =
            (J.adicTopology : TopologicalSpace _) from htop_eq]
        letI : TopologicalSpace (locSubring D₀.P D₀.T D₀.s) := J.adicTopology
        haveI : IsTopologicalAddGroup (locSubring D₀.P D₀.T D₀.s) :=
          @IsTopologicalRing.to_topologicalAddGroup _ _ J.adicTopology
            (RingFilterBasis.isTopologicalRing
              J.adic_basis.toRing_subgroups_basis.toRingFilterBasis)
        exact AddSubgroup.isOpen_of_mem_nhds _
          (J.hasBasis_nhds_zero_adic.mem_of_mem (i := n) trivial)
      haveI hdisc : DiscreteTopology (locSubring D₀.P D₀.T D₀.s ⧸ J ^ n) := by
        rw [discreteTopology_iff_isOpen_singleton_zero]
        convert @QuotientAddGroup.isOpenMap_coe _ _ _ inferInstance
          (N := (J ^ n).toAddSubgroup) _ hJn_open using 1
        ext x; constructor
        · rintro rfl; exact ⟨0, (J ^ n).zero_mem, rfl⟩
        · rintro ⟨a, ha, heq⟩
          rw [Set.mem_singleton_iff, ← heq]
          change Ideal.Quotient.mk (J ^ n) a = 0
          exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
      -- Derive uniform space instances from TopologyComparison.lean pattern:
      haveI : @IsTopologicalAddGroup (locSubring D₀.P D₀.T D₀.s ⧸ J ^ n)
          inferInstance _ :=
        @IsTopologicalRing.to_topologicalAddGroup _ _ inferInstance inferInstance
      letI : UniformSpace (locSubring D₀.P D₀.T D₀.s ⧸ J ^ n) :=
        @IsTopologicalAddGroup.rightUniformSpace _ _ inferInstance inferInstance
      haveI : @IsUniformAddGroup (locSubring D₀.P D₀.T D₀.s ⧸ J ^ n) _ _ :=
        @isUniformAddGroup_of_addCommGroup _ _ inferInstance inferInstance
      -- Factor out: rightUniformSpace on discrete quotient = ⊥.
      have hrus_bot : @IsTopologicalAddGroup.rightUniformSpace
          (locSubring D₀.P D₀.T D₀.s ⧸ J ^ n) _ _ _ = ⊥ := by
        apply @UniformSpace.ext _ _ ⊥
        rw [uniformity_eq_comap_nhds_zero' _, nhds_discrete, Filter.comap_pure]
        congr 1; ext ⟨a, b⟩; simp [add_neg_eq_zero, eq_comm]
      haveI hcs : CompleteSpace (locSubring D₀.P D₀.T D₀.s ⧸ J ^ n) := by
        change @CompleteSpace _ (@IsTopologicalAddGroup.rightUniformSpace _ _ _ _)
        rw [hrus_bot]; infer_instance
      let πc := @UniformSpace.Completion.extensionHom
        (locSubring D₀.P D₀.T D₀.s) _ _ _ _
        (locSubring D₀.P D₀.T D₀.s ⧸ J ^ n) _ _ _ _
        (Ideal.Quotient.mk (J ^ n)) continuous_quotient_mk' hcs inferInstance
      -- Compose: π = πc ∘ eRE : ringOfDef →+* locSubring/J^n
      let π := πc.comp eRE.toRingHom
      -- ker(π) ⊇ idealOfDef^n:
      have hge : (presheafValue_idealOfDef D₀ ^ n :
          Ideal _) ≤ RingHom.ker π := by
        rw [show presheafValue_idealOfDef D₀ = Ideal.map g J from rfl,
          (Ideal.map_pow g J n).symm, Ideal.map_le_iff_le_comap]
        intro a ha; rw [Ideal.mem_comap, RingHom.mem_ker]
        change πc (eRE (g a)) = 0
        -- eRE(g a) = (completionRingEquiv g).symm(g a) = coe(a)
        have : eRE (g a) = (↑a : UniformSpace.Completion _) := by
          change (AdicCompletionBridge.completionRingEquiv g hg_cont hg_ui hg_dense).symm
            (g a) = ↑a
          rw [(AdicCompletionBridge.completionRingEquiv g hg_cont hg_ui hg_dense).symm_apply_eq]
          exact (UniformSpace.Completion.extensionHom_coe g hg_cont a).symm
        rw [this]
        haveI : T0Space (locSubring D₀.P D₀.T D₀.s ⧸ J ^ n) := by
          haveI := hdisc; infer_instance
        change πc (↑a) = 0
        change (UniformSpace.Completion.extensionHom
          (Ideal.Quotient.mk (J ^ n)) continuous_quotient_mk') (↑a) = 0
        rw [UniformSpace.Completion.extensionHom_coe]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
      -- ker(π) ⊆ idealOfDef^n:
      -- eRE is a ring iso, so ker(π) = eRE⁻¹(ker πc) = eRE⁻¹(Ideal.map coe (J^n))
      -- = Ideal.map (eRE⁻¹ ∘ coe) (J^n) = Ideal.map g (J^n) = idealOfDef^n.
      -- (This uses ker_evalₐ_eq through the bridge to identify ker πc.)
      have hle : RingHom.ker π ≤ (presheafValue_idealOfDef D₀ ^ n :
          Ideal _) := by
        set_option maxHeartbeats 4000000 in
        -- Factor πc through the bridge: πc = evalₐ ∘ eAC (by uniqueness).
        -- Then ker(π) = eRE⁻¹(eAC⁻¹(ker(evalₐ))) = idealOfDef^n.
        -- Set up the bridge: Completion(locSubring) ≃+* AdicCompletion(J, locSubring).
        -- Needs IsAdic J on locSubring (from hadic_eq) and compatible instances.
        have hadic_loc : @IsAdic (locSubring D₀.P D₀.T D₀.s) _
            instTopologicalSpaceSubtype J := hadic_eq
        let eAC := @AdicCompletionBridge.adicCompletionRingEquiv
          (locSubring D₀.P D₀.T D₀.s) _ J instUniformSpaceSubtype
          inferInstance inferInstance hadic_loc
        -- Transport: ker(π) = eRE⁻¹(eAC⁻¹(ker(evalₐ))) = idealOfDef^n.
        -- π = πc ∘ eRE, so ker(π) = Ideal.comap eRE (ker πc).
        -- For ker(πc): πc = evalₐ ∘ eAC (both extend q, T₂ uniqueness),
        -- so ker(πc) = Ideal.comap eAC (ker evalₐ).
        -- ker(evalₐ) = Ideal.map algebraMap (J^n) by ker_evalₐ_eq.
        -- Composing the comap chain and using the ring equiv properties:
        -- ker(π) = Ideal.comap (eRE ∘ eAC⁻¹ ∘ algebraMap) ...
        --       = Ideal.map g (J^n).
        -- We use: for a ring equiv e, Ideal.comap e I = Ideal.map e.symm I.
        -- And the composition eRE⁻¹ ∘ eAC⁻¹ ∘ of maps r ↦ coe(r) ↦ g(r).
        -- ker(π) = ker(πc ∘ eRE) = Ideal.comap eRE (ker πc).
        -- Step 1: πc = evalₐ ∘ eAC (both extend mk along coe, target T₂).
        -- Step 2: ker(πc) = Ideal.comap eAC (ker evalₐ) = Ideal.comap eAC (Ideal.map algebraMap (J^n)).
        -- Step 3: ker(π) = Ideal.comap eRE (Ideal.comap eAC (Ideal.map algebraMap (J^n)))
        --        = Ideal.comap (eAC ∘ eRE) (Ideal.map algebraMap (J^n))
        --        = Ideal.map g (J^n) (since eAC ∘ eRE ∘ g = algebraMap, ring equivs).
        -- We combine the transport through the two ring equivs.
        rw [show presheafValue_idealOfDef D₀ = Ideal.map g J from rfl,
          (Ideal.map_pow g J n).symm]
        -- Step 1: πc = (evalₐ J n).toRingHom ∘ eAC (by Completion.induction_on).
        -- Both are continuous ring homs Completion → locSubring/J^n that extend
        -- Ideal.Quotient.mk (J^n) along coe. Target is T₂ (discrete). So equal.
        letI := (@UniformSpace.Completion.cPkg
          (locSubring D₀.P D₀.T D₀.s) _).uniformStruct
        haveI := (@UniformSpace.Completion.cPkg
          (locSubring D₀.P D₀.T D₀.s) _).complete
        haveI := (@UniformSpace.Completion.cPkg
          (locSubring D₀.P D₀.T D₀.s) _).separation
        have hπc_eq : ∀ y, πc y = (AdicCompletion.evalₐ J n) (eAC y) := by
          refine fun y => UniformSpace.Completion.induction_on y ?_ ?_
          · -- Both sides are continuous to T₂ (discrete) target.
            haveI := hdisc
            exact isClosed_eq
              UniformSpace.Completion.continuous_extension
              (by -- evalₐ ∘ eAC : Completion → locSubring/J^n is continuous.
                  -- eAC = bridge comparison (uniformly continuous).
                  -- evalₐ = component projection (continuous for bridge topology).
                  -- Install cPkg instances for the comparison:
                  letI := (@UniformSpace.Completion.cPkg
                    (locSubring D₀.P D₀.T D₀.s)
                    (UniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype
                      D₀.uniformSpace)).uniformStruct
                  haveI := (@UniformSpace.Completion.cPkg
                    (locSubring D₀.P D₀.T D₀.s)
                    (UniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype
                      D₀.uniformSpace)).complete
                  haveI := (@UniformSpace.Completion.cPkg
                    (locSubring D₀.P D₀.T D₀.s)
                    (UniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype
                      D₀.uniformSpace)).separation
                  -- Install adicAbstractCompletion instances:
                  letI := (AdicCompletionBridge.adicAbstractCompletion J hadic_loc).uniformStruct
                  haveI := (AdicCompletionBridge.adicAbstractCompletion J hadic_loc).complete
                  haveI := (AdicCompletionBridge.adicAbstractCompletion J hadic_loc).separation
                  -- eAC is continuous (bridge comparison):
                  have heAC_cont : Continuous eAC :=
                    (AbstractCompletion.uniformContinuous_compare
                      (@UniformSpace.Completion.cPkg _ _)
                      (AdicCompletionBridge.adicAbstractCompletion J hadic_loc)).continuous
                  -- evalₐ is continuous (component projection in bridge topology):
                  -- evalₐ J n = Ideal.quotientEquivAlgOfEq ∘ eval J R n
                  -- eval extracts the n-th component (continuous in product topology).
                  -- evalₐ J n : AdicCompletion → R/J^n.
                  -- evalₐ = quotientEquivAlgOfEq ∘ eval.
                  -- eval = (·.val n) = (continuous_apply n).comp continuous_subtype_val.
                  -- quotientEquivAlgOfEq : from discrete R/J^n•⊤ to discrete R/J^n.
                  have hevalₐ_cont : Continuous (AdicCompletion.evalₐ J n) := by
                    unfold AdicCompletion.evalₐ
                    simp only []
                    letI : ∀ i, TopologicalSpace
                        (locSubring D₀.P D₀.T D₀.s ⧸ J ^ i • ⊤) :=
                      fun i => (AdicCompletionBridge.quotientDiscreteTopology J i)
                    haveI : DiscreteTopology
                        (locSubring D₀.P D₀.T D₀.s ⧸ J ^ n • ⊤) :=
                      AdicCompletionBridge.quotientDiscrete J n
                    have h1 : Continuous
                        (AdicCompletion.eval J (locSubring D₀.P D₀.T D₀.s) n) :=
                      (continuous_apply n).comp continuous_subtype_val
                    have h2 : Continuous (Ideal.quotientEquivAlgOfEq
                        (locSubring D₀.P D₀.T D₀.s)
                        (AdicCompletionBridge.ideal_smul_top_eq_self J n)) :=
                      continuous_of_discreteTopology
                    exact h2.comp h1
                  exact hevalₐ_cont.comp heAC_cont)
          · intro a
            show πc (↑a) = (AdicCompletion.evalₐ J n) (eAC (↑a))
            rw [UniformSpace.Completion.extensionHom_coe,
              show eAC (↑a) = AdicCompletion.of J _ a from
                AbstractCompletion.compare_coe _ _ a,
              AdicCompletion.evalₐ_of]
        -- Step 2: ker(πc) = Ideal.comap eAC (ker evalₐ).
        -- Step 3: ker(π) = Ideal.comap eRE (ker πc)
        --   = Ideal.comap eRE (Ideal.comap eAC (ker evalₐ))
        --   = Ideal.comap eRE (Ideal.comap eAC (Ideal.map algebraMap (J^n)))
        --   [by ker_evalₐ_eq]
        -- Step 4: Transport: Ideal.comap (eAC ∘ eRE) (Ideal.map algebraMap (J^n))
        --   = Ideal.map ((eAC ∘ eRE).symm) (Ideal.map algebraMap (J^n))  [ring equiv]
        --   = Ideal.map g (J^n)
        --   [since (eAC ∘ eRE).symm ∘ algebraMap = g: eRE.symm(eAC.symm(of r)) = g(r)]
        intro x hx; rw [RingHom.mem_ker] at hx
        -- hx : πc (eRE x) = 0. By hπc_eq: evalₐ (eAC (eRE x)) = 0.
        have hmem_ker : eAC (eRE x) ∈ RingHom.ker (AdicCompletion.evalₐ J n) := by
          rw [RingHom.mem_ker]; rwa [← hπc_eq]
        rw [AdicCompletionBridge.ker_evalₐ_eq] at hmem_ker
        -- hmem_ker : eAC (eRE x) ∈ Ideal.map algebraMap (J^n)
        -- x = eRE.symm (eAC.symm (eAC (eRE x)))
        -- x = (eRE.symm ∘ eAC.symm)(eAC(eRE(x))):
        have hx_eq : x = (eRE.symm.toRingHom.comp eAC.symm.toRingHom) (eAC (eRE x)) := by
          simp [RingHom.comp_apply, RingEquiv.symm_apply_apply]
        -- Ideal.map (eRE.symm ∘ eAC.symm) (Ideal.map algebraMap (J^n))
        --   = Ideal.map (eRE.symm ∘ eAC.symm ∘ algebraMap) (J^n)  [by map_map]
        --   = Ideal.map g (J^n)  [since eRE.symm(eAC.symm(of a)) = g(a)]
        have h_map_eq : Ideal.map (eRE.symm.toRingHom.comp eAC.symm.toRingHom)
            (Ideal.map (algebraMap _ _) (J ^ n)) = Ideal.map g (J ^ n) := by
          rw [Ideal.map_map]; congr 1
          ext a; simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
            RingHom.coe_coe]
          -- eAC.symm(algebraMap a) = coe(a), eRE.symm(coe a) = g(a).
          -- eAC = bridge (compare cPkg adicPkg), eRE = completionRingEquiv.symm.
          have h1 : eAC.symm (algebraMap _ _ a) =
              (↑a : UniformSpace.Completion _) := by
            rw [eAC.symm_apply_eq]
            -- Goal: algebraMap a = eAC (↑a). eAC(coe a) = of(a) = algebraMap a.
            exact (AbstractCompletion.compare_coe
              (@UniformSpace.Completion.cPkg _ _)
              (AdicCompletionBridge.adicAbstractCompletion J hadic_loc) a).symm
          have h2 : eRE.symm (↑a : UniformSpace.Completion _) = g a := by
            change (AdicCompletionBridge.completionRingEquiv g hg_cont hg_ui
              hg_dense).symm.symm (↑a) = g a
            rw [RingEquiv.symm_symm]
            exact UniformSpace.Completion.extensionHom_coe g hg_cont a
          set_option maxHeartbeats 800000 in rw [h1, h2]
        set_option maxHeartbeats 800000 in rw [hx_eq, ← h_map_eq]
        set_option maxHeartbeats 800000 in exact Ideal.mem_map_of_mem _ hmem_ker
      have hset : (↑(presheafValue_idealOfDef D₀ ^ n) :
          Set (presheafValue_ringOfDef D₀)) = ↑(RingHom.ker π) :=
        SetLike.coe_set_eq.mpr (le_antisymm hge hle)
      rw [hset]
      -- IsClosed (ker π): π is continuous to discrete T₁ target.
      set_option maxHeartbeats 800000 in
      have hπ_cont : Continuous π := by
        change Continuous (πc ∘ eRE)
        -- Install cPkg instances (same pattern as completionRingEquiv):
        letI := (@UniformSpace.Completion.cPkg
          (locSubring D₀.P D₀.T D₀.s)
          (UniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype
            D₀.uniformSpace)).uniformStruct
        haveI := (@UniformSpace.Completion.cPkg
          (locSubring D₀.P D₀.T D₀.s)
          (UniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype
            D₀.uniformSpace)).complete
        haveI := (@UniformSpace.Completion.cPkg
          (locSubring D₀.P D₀.T D₀.s)
          (UniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype
            D₀.uniformSpace)).separation
        exact UniformSpace.Completion.continuous_extension.comp
          (AbstractCompletion.uniformContinuous_compare pkg
            (@UniformSpace.Completion.cPkg _ _)).continuous
      rw [show (↑(RingHom.ker π) : Set _) = π ⁻¹' {0} from by
        ext x; exact ⟨id, id⟩]
      exact isClosed_singleton.preimage hπ_cont
    -- Step 3: closure_minimal.
    exact closure_minimal hgJn_sub hclosed

private theorem closure_locNhd_sub_idealOfDef_pow (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)] (n : ℕ) :
    (closure ((D₀.coeRingHom : Localization.Away D₀.s → presheafValue D₀) ''
      (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s)))) ∩
    (presheafValue_ringOfDef D₀ : Set (presheafValue D₀)) ⊆
    Subtype.val '' ((presheafValue_idealOfDef D₀ ^ n : Ideal (presheafValue_ringOfDef D₀)) :
      Set (presheafValue_ringOfDef D₀)) := by
  letI := D₀.uniformSpace
  letI := D₀.isUniformAddGroup
  letI := D₀.isTopologicalRing
  -- The proof uses the sandwiching:
  -- (A) coe '' locNhd n ⊆ val '' idealOfDef^n  (locNhd_sub_idealOfDef_pow_val)
  -- (B) val '' idealOfDef^n ⊆ closure(coe '' locNhd n)  (idealOfDef_pow_val_sub_closure)
  -- (C) val '' idealOfDef^n is closed  (idealOfDef_pow_val_isClosed)
  -- From (A): closure(coe '' locNhd n) ⊆ closure(val '' idealOfDef^n) = val '' idealOfDef^n.
  -- The intersection with ringOfDef is contained since val '' idealOfDef^n ⊆ ringOfDef.
  intro x ⟨hx_closure, _⟩
  exact (idealOfDef_pow_val_isClosed D₀ n).closure_subset_iff.mpr
    (locNhd_sub_idealOfDef_pow_val D₀ n) hx_closure

/-- The subspace topology on the ring of definition equals the
ideal-of-definition-adic topology.

This is the deepest fact needed for Proposition 8.15: the subspace topology
on the closure of locSubring in the completion equals the adic topology for
the image of locIdeal.

The proof uses `isAdic_iff`, reducing to two conditions:
1. Each `(presheafValue_idealOfDef)^n` is open in the subspace topology
2. Each subspace-nhd of 0 contains some `(presheafValue_idealOfDef)^n`

Both follow from the interleaving of ideal powers with the completion nhds
basis `closure(coe '' locNhd n)`, established by the helper lemmas
`idealOfDef_pow_val_sub_closure` and `closure_locNhd_sub_idealOfDef_pow`. -/
theorem presheafValue_isAdic (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)] :
    @IsAdic (presheafValue_ringOfDef D₀) _
      (TopologicalSpace.induced Subtype.val inferInstance)
      (presheafValue_idealOfDef D₀) := by
  -- Use isAdic_iff: show (1) each power is open and (2) powers form nhds basis.
  -- The subspace topology on ringOfDef is a topological ring (subring of a top ring).
  letI : TopologicalSpace (presheafValue_ringOfDef D₀) :=
    TopologicalSpace.induced Subtype.val inferInstance
  haveI : IsTopologicalRing (presheafValue_ringOfDef D₀) :=
    Subring.instIsTopologicalRing _
  rw [isAdic_iff]
  letI := D₀.uniformSpace
  letI := D₀.isUniformAddGroup
  letI := D₀.isTopologicalRing
  open Filter Topology in
  set f := (D₀.coeRingHom : Localization.Away D₀.s → presheafValue D₀) with hf_def
  have hbasis := (locBasis D₀.P D₀.T D₀.s D₀.hopen).hasBasis_nhds_zero
  have hbasis_compl : (nhds (0 : presheafValue D₀)).HasBasis (fun _ : ℕ => True)
      (fun n => closure (f '' (locNhd D₀.P D₀.T D₀.s n :
        Set (Localization.Away D₀.s)))) := by
    rw [← (map_zero D₀.coeRingHom : f 0 = 0)]
    exact hbasis.hasBasis_of_isDenseInducing UniformSpace.Completion.isDenseInducing_coe
  have himage_sub : ∀ n,
      f '' (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s)) ⊆
      ((D₀.coeRingHom.comp (locSubring D₀.P D₀.T D₀.s).subtype).range :
        Set (presheafValue D₀)) := by
    intro n x hx
    obtain ⟨y, hy, hyx⟩ := hx
    obtain ⟨d, _, hdy⟩ := hy
    refine ⟨d, ?_⟩
    change D₀.coeRingHom ((locSubring D₀.P D₀.T D₀.s).subtype d) = x
    exact hdy ▸ hyx
  have hclosure_sub : ∀ n,
      closure (f '' (locNhd D₀.P D₀.T D₀.s n :
        Set (Localization.Away D₀.s))) ⊆
      (presheafValue_ringOfDef D₀ : Set (presheafValue D₀)) :=
    fun n => closure_mono (himage_sub n)
  have hsubspace_basis : (nhds (0 : presheafValue_ringOfDef D₀)).HasBasis
      (fun _ : ℕ => True) (fun n => Subtype.val ⁻¹'
        (closure (f '' (locNhd D₀.P D₀.T D₀.s n :
          Set (Localization.Away D₀.s))))) := by
    rw [nhds_induced]
    exact hbasis_compl.comap Subtype.val
  constructor
  · intro n
    apply AddSubgroup.isOpen_of_mem_nhds
      (((presheafValue_idealOfDef D₀) ^ n).toAddSubgroup)
    apply hsubspace_basis.mem_of_superset (i := n) trivial
    intro ⟨x, hx_mem⟩ hx_closure
    obtain ⟨y, hy_mem, hy_eq⟩ := closure_locNhd_sub_idealOfDef_pow D₀ n
      ⟨hx_closure, hx_mem⟩
    rw [show (⟨x, hx_mem⟩ : presheafValue_ringOfDef D₀) = y from Subtype.ext hy_eq.symm]
    exact hy_mem
  · intro s hs
    obtain ⟨m, -, hm⟩ := hsubspace_basis.mem_iff.mp hs
    exact ⟨m, fun x hx => hm (idealOfDef_pow_val_sub_closure D₀ m ⟨x, hx, rfl⟩)⟩

/-- **Proposition 8.15 (partial)**: `presheafValue D₀` has a natural
pair of definition, making it a Huber ring. Combined with
`presheafValue_topNilUnit`, this gives `IsTateRing`. -/
theorem presheafValue_pairOfDefinition [IsTateRing A] [IsNoetherianRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)] :
    Nonempty (PairOfDefinition (presheafValue D₀)) :=
  ⟨{ A₀ := presheafValue_ringOfDef D₀
     I := presheafValue_idealOfDef D₀
     isOpen := presheafValue_ringOfDef_isOpen D₀
     fg := presheafValue_idealOfDef_fg D₀
     isAdic := presheafValue_isAdic D₀ }⟩

/-- **Proposition 8.15**: `presheafValue D₀` is a Tate ring.

Combines:
- `presheafValue_pairOfDefinition`: the pair of definition exists
- `presheafValue_topNilUnit`: a topologically nilpotent unit exists -/
theorem presheafValue_isTateRing [IsTateRing A] [IsNoetherianRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)] :
    IsTateRing (presheafValue D₀) :=
  { exists_pairOfDefinition := presheafValue_pairOfDefinition P D₀
    exists_topologicallyNilpotent_unit := presheafValue_topNilUnit D₀ }

/-! ### Proposition 8.15: key lemmas for restriction as localization

The restriction map `sigma = restrictionMapHom D₀ D h` is surjective and
injective. Both facts follow from the deep topological result that the
algebraic lift between localizations is a uniform embedding with respect
to the localization topologies (Wedhorn Proposition 8.15).

**Proof architecture**: `restrictionMapAlg D₀ D h` factors as
`D.coeRingHom ∘ locLift` where `locLift : Loc.Away D₀.s →+* Loc.Away D.s`
exists because `D₀.s` becomes a unit in `Loc.Away D.s` (rational containment).
The key topological input (Wedhorn Prop 8.15) is that `restrictionMapAlg` is
a `IsUniformInducing` map from `(Loc.Away D₀.s, D₀.uniformSpace)` to
`(presheafValue D, Completion.uniformSpace)`. Then:

- **Injectivity** of `sigma`: `isUniformInducing_extension` gives sigma is
  `IsUniformInducing`, hence injective (in T₀ spaces).
- **Surjectivity** of `sigma`: The range is complete
  (`IsUniformInducing.isComplete_range` + `CompleteSpace`), hence closed
  (`IsComplete.isClosed` in T₀). The range is also dense (contains the dense
  image `restrictionMapAlg(Loc.Away D₀.s)` which contains `D.canonicalMap(A)`).
  Dense + closed = everything. -/

/-! ### Key topological input (Wedhorn Prop 8.15)

The algebraic restriction map `restrictionMapAlg D₀ D h : Localization.Away D₀.s →
presheafValue D` is `IsUniformInducing` from `D₀.uniformSpace` to the completion
uniformity, AND has dense range.

**IsUniformInducing**: The localization topologies on `Loc.Away D₀.s` and
`Loc.Away D.s` are compatible under the algebraic lift. Concretely, for the
pair of definition `(A₀, I)`:
- Source neighborhoods: `locNhd D₀.P D₀.T D₀.s n` (based on `I^n` in `A[1/D₀.s]`)
- Target neighborhoods: completion of `locNhd D.P D.T D.s n`
- The composition `D.coeRingHom ∘ locLift` maps source nhds into target nhds
  and reflects them.
This factors as `D.coeRingHom ∘ locLift`. `D.coeRingHom` is `IsUniformInducing`
(by `Completion.isUniformInducing_coe`). The `locLift` between localizations
preserves the adic uniformity by the Noetherian hypothesis: `I^n·A[1/D₀.s]` maps into
`I^n·A[1/D.s]` (forward), and the reverse uses the Artin-Rees lemma for Noetherian
adic filtrations.

**DenseRange**: The image of `Loc.Away D₀.s` under `restrictionMapAlg` is dense in
`presheafValue D`. Since `restrictionMapAlg(algebraMap a) = D.canonicalMap a` for all
`a : A`, the image contains `range(D.canonicalMap)` which topologically generates the
completion.

**Wedhorn reference**: Proposition 8.15 + Lemma 8.5 (Noetherian adic completion). -/

/-- `D₀.s` is a unit in `Localization.Away D.s` when `R(D.T/D.s) ⊆ R(D₀.T/D₀.s)`.

This is the localization-level analogue of `isUnit_canonicalMap_s`. The proof uses
the prime ideal criterion: for every prime `p` containing `D₀.s`, we have `D.s ∈ p`
(by Wedhorn Prop 7.52, proved as `mem_prime_of_rational_subset` in Presheaf.lean).
Hence `D.s` lies in the radical of `(D₀.s)`, so a power of `D.s` is divisible by
`D₀.s`, making `D₀.s` a unit in `Localization.Away D.s`.

The proof duplicates the `hu_loc` step from `restrictionMapAlg_continuous_of_huber`
in Presheaf.lean (which is private and hence inaccessible from this file). -/
private theorem isUnit_algebraMap_s_of_rational_subset
    (D₀ D : RationalLocData A) (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    IsUnit (algebraMap A (Localization.Away D.s) D₀.s) := by
  have hrad : D.s ∈ Ideal.radical (Ideal.span {D₀.s}) := by
    classical
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    intro p ⟨hsp, hp⟩
    exact mem_prime_of_rational_subset D₀ D h p hp
      (hsp (Ideal.subset_span (Set.mem_singleton D₀.s)))
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hn
  have hunit_pow : IsUnit (algebraMap A (Localization.Away D.s) D.s ^ n) :=
    (IsLocalization.map_units (Localization.Away D.s)
      (⟨D.s, ⟨1, pow_one D.s⟩⟩ : Submonoid.powers D.s)).pow n
  have heq : algebraMap A (Localization.Away D.s) a *
      algebraMap A (Localization.Away D.s) D₀.s =
      algebraMap A (Localization.Away D.s) D.s ^ n := by
    rw [← map_mul, ← map_pow, ha]
  rw [← heq] at hunit_pow
  exact isUnit_of_mul_isUnit_right hunit_pow

/-- The localization-level lift between localizations: `D₀.s` is a unit in
`Localization.Away D.s` when `R(D.T/D.s) ⊆ R(D₀.T/D₀.s)`, so
`IsLocalization.Away.lift` gives a ring hom
`Localization.Away D₀.s →+* Localization.Away D.s`. -/
private noncomputable def locLift
    (D₀ D : RationalLocData A) (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    Localization.Away D₀.s →+* Localization.Away D.s :=
  IsLocalization.Away.lift D₀.s (isUnit_algebraMap_s_of_rational_subset D₀ D h)

/-- The algebraic restriction map factors as `D.coeRingHom ∘ locLift D₀ D h`. -/
private theorem restrictionMapAlg_eq_comp_locLift
    (D₀ D : RationalLocData A) (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    restrictionMapAlg D₀ D h = D.coeRingHom.comp (locLift D₀ D h) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers D₀.s)
  ext a
  simp only [RingHom.comp_apply, restrictionMapAlg, IsLocalization.Away.lift_eq,
    RationalLocData.coeRingHom, RationalLocData.canonicalMap, locLift]

/-- **Forward continuity** of locLift: for every target neighborhood level `m`, there
exists a source level `n` such that `locLift` maps `locNhd D₀ n` into `locNhd D m`.

This follows from the universal property of the localization topology (Wedhorn §5.51):
the localization topology is the coarsest making `algebraMap` continuous and `s` a unit.
Since `locLift ∘ algebraMap = algebraMap` and `algebraMap` is continuous into `D.topology`,
the lift is continuous by the universal property. The neighborhood-level version here is
the explicit formulation needed for `IsUniformInducing`.

**Wedhorn reference**: Proposition 8.2, §5.51. -/
private theorem locLift_maps_locNhd
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [FirstCountableTopology A]
    (D₀ D : RationalLocData A) (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    ∀ m : ℕ, ∃ n : ℕ,
      ∀ x ∈ @locNhd A _ _ D₀.P D₀.T D₀.s n,
        (locLift D₀ D h) x ∈ @locNhd A _ _ D.P D.T D.s m := by
  -- locLift is continuous from D₀.topology to D.topology.
  -- Proof: restrictionMapAlg = D.coeRingHom ∘ locLift is continuous (Presheaf.lean),
  -- and D.coeRingHom is IsUniformInducing (embedding), so locLift is continuous.
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  haveI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  haveI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  have hcont_alg := restrictionMapAlg_continuous D₀ D h
  have hfactor := restrictionMapAlg_eq_comp_locLift D₀ D h
  have hcoe_ui : @IsUniformInducing _ _ D.uniformSpace
      (@UniformSpace.Completion.uniformSpace _ D.uniformSpace) D.coeRingHom :=
    UniformSpace.Completion.isUniformInducing_coe _
  have hcont_lift : @Continuous _ _ D₀.topology D.topology (locLift D₀ D h) := by
    have : D.topology = @UniformSpace.toTopologicalSpace _ D.uniformSpace := rfl
    rw [this]
    apply hcoe_ui.isInducing.continuous_iff.mpr
    show @Continuous _ _ D₀.topology _ (D.coeRingHom ∘ locLift D₀ D h)
    have : (D.coeRingHom ∘ locLift D₀ D h : Localization.Away D₀.s →
        presheafValue D) = restrictionMapAlg D₀ D h :=
      congrArg DFunLike.coe hfactor.symm
    rw [this]; exact hcont_alg
  intro m
  have hmem : (locNhd D.P D.T D.s m : Set (Localization.Away D.s)) ∈
      @nhds _ D.topology 0 :=
    (locBasis D.P D.T D.s D.hopen).hasBasis_nhds_zero.mem_of_mem trivial
  have hpre : (locLift D₀ D h) ⁻¹' (locNhd D.P D.T D.s m : Set (Localization.Away D.s)) ∈
      @nhds _ D₀.topology 0 := by
    have htend : Filter.Tendsto (locLift D₀ D h) (@nhds _ D₀.topology 0)
        (@nhds _ D.topology 0) :=
      (map_zero (locLift D₀ D h)) ▸ hcont_lift.continuousAt
    exact htend hmem
  obtain ⟨n, -, hn⟩ := (locBasis D₀.P D₀.T D₀.s D₀.hopen).hasBasis_nhds_zero.mem_iff.mp hpre
  exact ⟨n, fun x hx => hn hx⟩

/-- **Backward inducing** of locLift: for every source neighborhood level `n`, there
exists a target level `m` such that the preimage of `locNhd D m` under `locLift` is
contained in `locNhd D₀ n`.

This is the harder direction of the proof that `locLift` is a topological embedding.
The forward direction (continuity, `locLift_maps_locNhd`) follows from the factoring
`restrictionMapAlg = D.coeRingHom ∘ locLift`. The backward direction requires the
Noetherian hypothesis and uses the following key inputs:

1. **Ideal filtration interleaving**: Both `D₀.P.I` and `D.P.I` define the same
   topology on `A`, so their filtrations on `A` are cofinal: for every `n`, ∃ `c` with
   `val '' (D.P.I^c) ⊆ val '' (D₀.P.I^n)` (from `hasBasis_nhds_zero`).

2. **locLift preserves algebraMap**: `locLift ∘ algebraMap = algebraMap` (from
   `IsLocalization.Away.lift`), so elements of the form `algebraMap(a)` are
   preserved.

3. **The hopen condition**: For both `D₀` and `D`, high powers of the ideal of
   definition under `divByS` land in the respective `locSubring`. This ensures
   that the `s⁻¹`-factors in the Localization can be absorbed.

4. **Artin-Rees (Noetherian control)**: The Artin-Rees lemma for the Noetherian
   ring `locSubring D` controls the intersection of `(locIdeal D)^n` with the
   image of `locLift`. Specifically, the image of `locSubring D₀` in
   `Localization.Away D.s` intersected with the adic filtration of `locSubring D`
   stabilizes at some depth `k₀` (the Artin-Rees constant).

Together: for `m` large enough (depending on `n` and the interleaving/Artin-Rees
constants), any `x` with `locLift(x) ∈ locNhd D m` must have `x ∈ locNhd D₀ n`.

**Wedhorn reference**: Proposition 8.15 + Lemma 8.5 (Artin-Rees for adic rings). -/
private theorem locLift_preimage_locNhd
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [FirstCountableTopology A]
    (D₀ D : RationalLocData A) (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    ∀ n : ℕ, ∃ m : ℕ,
      ∀ x : Localization.Away D₀.s,
        (locLift D₀ D h) x ∈ @locNhd A _ _ D.P D.T D.s m →
          x ∈ @locNhd A _ _ D₀.P D₀.T D₀.s n := by
  intro n
  -- Step 1: Establish the ideal interleaving.
  -- Both D₀.P and D.P are pairs of definition for A, so their ideal
  -- filtrations are cofinal on A: for every n, ∃ c with
  -- val '' (D.P.I^c) ⊆ val '' (D₀.P.I^n).
  have h_interleave : ∀ k : ℕ, ∃ c : ℕ,
      Subtype.val '' ((D.P.I ^ c : Ideal D.P.A₀) : Set D.P.A₀) ⊆
        Subtype.val '' ((D₀.P.I ^ k : Ideal D₀.P.A₀) : Set D₀.P.A₀) := by
    intro k
    have h_nhd : Subtype.val '' ((D₀.P.I ^ k : Ideal D₀.P.A₀) : Set D₀.P.A₀) ∈
        nhds (0 : A) :=
      D₀.P.hasBasis_nhds_zero.mem_of_mem trivial
    exact (D.P.hasBasis_nhds_zero.mem_iff.mp h_nhd).imp fun c h => h.2
  -- Step 2: locLift preserves algebraMap.
  have h_lift_alg : ∀ a : A,
      (locLift D₀ D h) (algebraMap A (Localization.Away D₀.s) a) =
        algebraMap A (Localization.Away D.s) a := by
    intro a; simp only [locLift, IsLocalization.Away.lift_eq]
  -- Steps 3-4: The backward inclusion using the Artin-Rees lemma.
  -- The remaining argument requires:
  -- (a) From h_interleave: algebraMap(D.P.I^c) maps into algebraMap(D₀.P.I^n)
  --     in any localization. Under locLift, this gives control over the
  --     algebraMap-components.
  -- (b) From D₀.hopen + locNhd_invS_step: the (D₀.s)⁻¹ factors are absorbed
  --     into the locSubring D₀ at the cost of increasing the ideal power.
  -- (c) From Artin-Rees (via IsNoetherianRing + locSubring Noetherian):
  --     the intersection of (locIdeal D)^m with the image of locLift
  --     stabilizes, giving uniform control over the shift constant.
  -- Combining (a)-(c) gives m = f(n, c, k₀) where c is the interleaving
  -- constant and k₀ is the Artin-Rees constant.
  sorry

/-- The locLift between localizations is `IsUniformInducing` from `D₀.uniformSpace`
to `D.uniformSpace`.

**Proof**: Both localization topologies use the SAME base ideal I from the pair of
definition. The locLift fixes `algebraMap`, so it maps `I^n·A[1/D₀.s]` into
`I^n·A[1/D.s]` (forward continuity). The reverse (inducing) uses the Noetherian
hypothesis: by the Artin-Rees lemma, `locLift⁻¹(locNhd D m) ⊇ locNhd D₀ n` for some n.
**Wedhorn reference**: Proposition 8.15 + Lemma 8.5. -/
private theorem locLift_isUniformInducing
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [FirstCountableTopology A]
    (D₀ D : RationalLocData A) (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    @IsUniformInducing _ _ D₀.uniformSpace D.uniformSpace (locLift D₀ D h) := by
  -- Strategy: reduce IsUniformInducing to IsInducing via the uniform group lemma,
  -- then reduce IsInducing to nhds 0 equality via IsTopologicalAddGroup.ext.
  letI uD₀ : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI uD : UniformSpace (Localization.Away D.s) := D.uniformSpace
  haveI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  haveI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  rw [@isUniformInducing_iff_uniformSpace _ _ uD₀ uD]
  apply @IsUniformAddGroup.ext (Localization.Away D₀.s) _
  · exact IsUniformAddGroup.comap (locLift D₀ D h)
  · exact D₀.isUniformAddGroup
  · -- nhds 0 in comap uniform space = nhds 0 in D₀.uniformSpace.
    -- LHS: nhds 0 in (uD.comap locLift).toTopologicalSpace
    --     = nhds 0 in (induced locLift uD.toTopologicalSpace)
    --     = comap locLift (nhds_D 0) [by nhds_induced + map_zero]
    -- RHS: nhds 0 in D₀.topology [= uD₀.toTopologicalSpace]
    rw [show @UniformSpace.toTopologicalSpace _ (uD.comap (locLift D₀ D h)) =
      TopologicalSpace.induced (locLift D₀ D h) uD.toTopologicalSpace from
      UniformSpace.toTopologicalSpace_comap,
      nhds_induced, show (locLift D₀ D h : Localization.Away D₀.s →
        Localization.Away D.s) 0 = 0 from map_zero _]
    have hbasis₀ := (locBasis D₀.P D₀.T D₀.s D₀.hopen).hasBasis_nhds_zero
    have hbasisD := (locBasis D.P D.T D.s D.hopen).hasBasis_nhds_zero
    ext S
    rw [Filter.mem_comap, hbasis₀.mem_iff]
    constructor
    · rintro ⟨V, hV, hVS⟩
      obtain ⟨m, -, hm⟩ := hbasisD.mem_iff.mp hV
      obtain ⟨n, hn⟩ := locLift_maps_locNhd D₀ D h m
      exact ⟨n, trivial, fun x hx => hVS (hm (hn x hx))⟩
    · rintro ⟨n, -, hn⟩
      obtain ⟨m, hm⟩ := locLift_preimage_locNhd D₀ D h n
      exact ⟨(locNhd D.P D.T D.s m : Set (Localization.Away D.s)),
        hbasisD.mem_of_mem trivial (i := m),
        fun x hx_mem => hn (hm x hx_mem)⟩

private theorem restrictionMapAlg_isUniformInducing
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [FirstCountableTopology A]
    (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    @IsUniformInducing _ _ D₀.uniformSpace
      (@UniformSpace.Completion.uniformSpace _ D.uniformSpace)
      (restrictionMapAlg D₀ D h) := by
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  rw [show (restrictionMapAlg D₀ D h : Localization.Away D₀.s → presheafValue D) =
    D.coeRingHom ∘ locLift D₀ D h from
      congrArg DFunLike.coe (restrictionMapAlg_eq_comp_locLift D₀ D h)]
  exact (UniformSpace.Completion.isUniformInducing_coe _).comp
    (locLift_isUniformInducing D₀ D h)

/-- **Sigma surj condition (Wedhorn Prop 8.15)**: The restriction map
`restrictionMapHom D₀ D h` satisfies the `IsLocalization.Away.surj` condition:
for every `z`, there exist `n` and `a` with `z * sigma(s')^n = sigma(a)`.

**WARNING**: `Function.Surjective sigma` is FALSE in general -- it would require
`DenseRange locLift` (density of `A[1/D0.s]` in `A[1/D.s]` with the localization
topology), but `D.s` need not be a unit in `Localization.Away D0.s`.
Counterexample: the p-adic completion map from p-adic integers to p-adic numbers
is injective with closed range but NOT surjective.
The correct result is the surj condition below.

**Proof (Baire category)**: Define `S_n = {z | ∃ a, z * u^n = sigma(a)}`.
Each `S_n` is closed (preimage of closed `range(sigma)` under the homeomorphism
`z ↦ z * u^n`). `S = ∪_n S_n` is ascending, dense (contains
`D.coeRingHom(Localization.Away D.s)` from `h_dense`), and an additive subgroup.
By Baire category (presheafValue D is complete metrizable), some `S_N` has
nonempty interior, making `S` open. Open + dense subgroup = everything. -/
theorem restrictionMapHom_surj
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [FirstCountableTopology A]
    (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    ∀ z : presheafValue D,
      ∃ (n : ℕ) (a : presheafValue D₀),
        z * (restrictionMapHom D₀ D h) (D₀.canonicalMap D.s) ^ n =
        (restrictionMapHom D₀ D h) a := by
  -- The surj set S = {z | ∃ n a, z * u^n = sigma(a)} is:
  --   (1) an additive subgroup of presheafValue D
  --   (2) dense (contains the image of the dense D.coeRingHom)
  --   (3) F_sigma (union of closed S_n)
  -- By the Baire category theorem on the complete metrizable presheafValue D,
  -- some S_N has nonempty interior, so S is open. Open + dense subgroup = everything.
  -- Full formalization requires BaireSpace + AddSubgroup infrastructure.
  sorry

-- NOTE: `Function.Surjective (restrictionMapHom D₀ D h)` is FALSE in general.
-- sigma's range = closure(range(restrictionMapAlg)) ⊊ presheafValue D when
-- D.s is not a unit in Localization.Away D₀.s.
-- Use `restrictionMapHom_surj` (the IsLocalization.Away.surj condition) instead.

/-- **Sigma injectivity (Wedhorn Prop 8.15)**: The restriction map
`restrictionMapHom D₀ D h` is injective.

**Proof**: From `restrictionMapAlg_isUniformInducing`, the extension
`sigma` is `IsUniformInducing` (by `isUniformInducing_extension`). A
`IsUniformInducing` map between T₀ spaces is injective: if `sigma(x) = sigma(y)`,
then `x` and `y` are inseparable in the source (by the inducing property),
hence equal (by T₀). -/
theorem restrictionMapHom_injective
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [FirstCountableTopology A]
    (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    Function.Injective (restrictionMapHom D₀ D h) := by
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  intro x y hxy
  exact ((UniformSpace.Completion.isUniformInducing_extension
    (restrictionMapAlg_isUniformInducing D₀ D h)).isInducing.inseparable_iff.mp
      (Inseparable.of_eq hxy)).eq

/-! ### Proposition 8.15: restriction maps are rational localizations

The core of Prop 8.15: for D ≤ D₀, the restriction map
`restrictionMapHom D₀ D h : presheafValue D₀ →+* presheafValue D`
makes `presheafValue D` a localization of `presheafValue D₀` at the
image of `D.s` under `canonicalMap`.

This identification is the KEY infrastructure for Tate acyclicity:
- Each restriction is flat (localization = flat)
- Covering → Spec surjective → faithfully flat → IsSheafy

The proof requires:
1. presheafValue D₀ is a Tate ring (presheafValue_isTateRing, proved)
2. The restriction sends canonicalMap(D.s) to a unit (isUnit_canonicalMap_s)
3. presheafValue D = (presheafValue D₀)[1/canonicalMap(D.s)]
   (this is the ISOMORPHISM, not just a factoring)

Step 3 is the deepest part. It uses the localization-of-completion theorem:
Completion(R[1/s]) ≃ Completion(R)[1/s'] where R = locSubring, s = D.s.
This requires:
- The subspace uniformity identification (locSubring_subspace_eq_adic, proved)
- The completion embedding preserving the localization structure
- The universal property of localization in the completion -/

/-- The restriction map on the dense image equals the algebraic restriction map.
This re-proves the private `restrictionMapHom_coe` from `Presheaf.lean`,
needed here for the localization proof. -/
private theorem restrictionMapHom_coe' (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s)
    (a : Localization.Away D₀.s) :
    restrictionMapHom D₀ D h
      (@UniformSpace.Completion.coeRingHom _ _ D₀.uniformSpace
        D₀.isTopologicalRing D₀.isUniformAddGroup a) =
      restrictionMapAlg D₀ D h a := by
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe
    (restrictionMapAlg D₀ D h) (restrictionMapAlg_continuous D₀ D h) a

/-- **Proposition 8.15**: the restriction map is a localization.

`presheafValue D` is the localization of `presheafValue D₀` at
`D₀.canonicalMap D.s`. This makes each restriction map a localization,
hence flat (by `Localization.flat`).

**Proof strategy**: Apply `IsLocalization.Away.mk` with three conditions:
1. **Unit**: `sigma(s')` is a unit in `presheafValue D` (from `isUnit_s_in_presheafValue`).
2. **Surj**: For every `z`, exists `n, a` with `z * sigma(s')^n = sigma(a)`.
   Proved on the dense image via `IsLocalization.Away.surj`, extended to the
   completion via the subring argument: the set S = {z | exists n a, ...} is a
   dense subring of presheafValue D, and by the Baire category theorem on the
   complete metrizable space, S is open hence closed hence everything.
3. **Eq**: If `sigma(a) = sigma(b)`, exists `n` with `s'^n * a = s'^n * b`.
   For n=0 this is injectivity of sigma. On the dense image, injectivity follows
   from injectivity of the algebraic restriction map (domain assumption + T0
   completion embedding). Extension to completion by density + T2. -/
theorem restrictionMap_isLocalization
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [FirstCountableTopology A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    @IsLocalization.Away (presheafValue D₀) _ (D₀.canonicalMap D.s)
      (presheafValue D) _ (restrictionMapHom D₀ D h).toAlgebra := by
  letI : Algebra (presheafValue D₀) (presheafValue D) := (restrictionMapHom D₀ D h).toAlgebra
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  set sigma := restrictionMapHom D₀ D h with hsigma_def
  set s' := D₀.canonicalMap D.s with hs'_def
  have hsigma_coe : ∀ a : Localization.Away D₀.s,
      sigma (D₀.coeRingHom a) = restrictionMapAlg D₀ D h a :=
    fun a => restrictionMapHom_coe' D₀ D h a
  have hunit : IsUnit (sigma s') := by
    change IsUnit (sigma (D₀.coeRingHom (algebraMap A (Localization.Away D₀.s) D.s)))
    rw [hsigma_coe]
    simp only [restrictionMapAlg, IsLocalization.Away.lift_eq]
    exact isUnit_s_in_presheafValue D
  exact IsLocalization.Away.mk (D₀.canonicalMap D.s) hunit
    (restrictionMapHom_surj D₀ D h)
    (fun a b hab => by
      suffices ∀ c : presheafValue D₀, sigma c = 0 → ∃ n : ℕ, s' ^ n * c = 0 by
        obtain ⟨n, hn⟩ := this (a - b) (by rw [map_sub]; exact sub_eq_zero.mpr hab)
        exact ⟨n, by rw [mul_sub, sub_eq_zero] at hn; exact hn⟩
      intro c hc
      exact ⟨0, by simp [restrictionMapHom_injective D₀ D h
        (hc.trans (map_zero sigma).symm)]⟩)

end ValuationSpectrum
