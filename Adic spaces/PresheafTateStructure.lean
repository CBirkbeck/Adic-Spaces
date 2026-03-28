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
  [IsHuberRing A]

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

/-- **Key uniformity identification** (reviewer confirmed):
The subspace uniformity on `locSubring ⊆ Localization.Away s` equals
the `locIdeal`-adic uniformity. Since the localization topology is defined
by the basis `locNhd n = image(locIdeal^n)`, the induced topology on
locSubring has 0-basis `locIdeal^n` (because the inclusion is injective).
For additive topological groups, uniformity is determined by nhds 0.

Consequence: `Completion(locSubring, J-adic) ≅ closure(locSubring in presheafValue)`
as uniform spaces. This is `ringOfDef`. -/
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
  show Filter.comap (Prod.map (locSubring D₀.P D₀.T D₀.s).subtype
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

/-- The ring hom from `locSubring` into `presheafValue_ringOfDef D₀`: compose `coeRingHom`
with `subtype`, then lift into the topological closure (which contains the range). -/
noncomputable def locSubringToRingOfDef (D₀ : RationalLocData A) :
    locSubring D₀.P D₀.T D₀.s →+* presheafValue_ringOfDef D₀ := by
  letI := D₀.uniformSpace
  exact (D₀.coeRingHom.comp (locSubring D₀.P D₀.T D₀.s).subtype).codRestrict
    (presheafValue_ringOfDef D₀) fun d =>
    subset_closure (RingHom.mem_range.mpr ⟨d, rfl⟩)

/-- The ideal of definition inside the ring of definition: the image of `locIdeal` under
the natural map `locSubring → presheafValue_ringOfDef`. -/
noncomputable def presheafValue_idealOfDef (D₀ : RationalLocData A) :
    Ideal (presheafValue_ringOfDef D₀) :=
  Ideal.map (locSubringToRingOfDef D₀) (locIdeal D₀.P D₀.T D₀.s)

/-- The ideal of definition is finitely generated (locIdeal is f.g. and
Noetherian completion preserves finite generation). -/
theorem presheafValue_idealOfDef_fg (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)] :
    (presheafValue_idealOfDef D₀).FG :=
  (locIdeal_fg D₀.P D₀.T D₀.s).map _

/-- The val-preimage of `closure(coe '' locNhd n)` in the ring of definition
contains `presheafValue_idealOfDef^n`. Equivalently: the val-image of
`idealOfDef^n` lands inside `closure(coe '' locNhd n)`.

This is the "easy direction" showing ideal powers map INTO the corresponding
completion neighborhoods.

Proof by `Submodule.pow_induction_on_left'`:
- Base (n=0): `val r ∈ closure(coe '' locSubring) = ringOfDef`.
  Since `locNhd 0` = image of `locIdeal^0 = whole locSubring`, this holds.
- Addition: `closure(coe '' locNhd i)` is an additive subgroup (closure of
  additive subgroup), so closed under addition.
- Multiplication by `m ∈ idealOfDef`: the key step.
  `val m ∈ closure(coe '' locNhd 1)` (since idealOfDef = Ideal.map of locIdeal,
  and locSubring acts on locNhd, so closure absorbs the action).
  `val(m * x) = val(m) * val(x) ∈ closure(coe '' locNhd 1) * closure(coe '' locNhd i)`.
  By continuity of mul: `closure(S) * closure(T) ⊆ closure(S * T)`.
  And `locNhd 1 * locNhd i ⊆ locNhd(i+1)` (ideal multiplication in locSubring).
  So `val(m * x) ∈ closure(coe '' locNhd(i+1))`. -/
private theorem idealOfDef_pow_sub_val_preimage_closure (D₀ : RationalLocData A) (n : ℕ) :
    ((presheafValue_idealOfDef D₀ ^ n : Ideal (presheafValue_ringOfDef D₀)) :
      Set (presheafValue_ringOfDef D₀)) ⊆
    Subtype.val ⁻¹' closure ((D₀.coeRingHom : Localization.Away D₀.s → presheafValue D₀) ''
      (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s))) := by
  letI := D₀.uniformSpace
  letI := D₀.isUniformAddGroup
  letI := D₀.isTopologicalRing
  -- Abbreviations
  let fh := D₀.coeRingHom
  let sub := (locSubring D₀.P D₀.T D₀.s).subtype
  let comp_sub := fh.comp sub
  let g := locSubringToRingOfDef D₀
  -- T = coeRingHom '' locNhd n (the set whose closure we target)
  set T := (fh : Localization.Away D₀.s → presheafValue D₀) ''
    (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s)) with hT_def
  -- Rewrite (Ideal.map g locIdeal)^n = Ideal.map g (locIdeal^n)
  rw [show presheafValue_idealOfDef D₀ = Ideal.map g (locIdeal D₀.P D₀.T D₀.s) from rfl,
      show (Ideal.map g (locIdeal D₀.P D₀.T D₀.s)) ^ n =
        Ideal.map g ((locIdeal D₀.P D₀.T D₀.s) ^ n) from (Ideal.map_pow _ _ n).symm]
  -- Key: range(comp_sub) * T ⊆ T (locNhd n is image of an ideal, so stable under locSubring)
  have hact : ∀ c ∈ (comp_sub.range : Set (presheafValue D₀)), ∀ y ∈ T, c * y ∈ T := by
    rintro c ⟨a, rfl⟩ y ⟨z, hz, rfl⟩
    obtain ⟨d, hd, hdz⟩ := hz
    refine ⟨sub (a * d), ⟨a * d, Ideal.mul_mem_left _ a hd, rfl⟩, ?_⟩
    show fh (sub (a * d)) = comp_sub a * fh z
    have hsubz : sub d = z := hdz
    rw [show sub (a * d) = sub a * sub d from map_mul sub a d,
        map_mul fh, show fh (sub a) = comp_sub a from rfl, hsubz]
  -- ringOfDef = closure(range(comp_sub)) as sets in presheafValue
  have hringOfDef_eq : (presheafValue_ringOfDef D₀ : Set (presheafValue D₀)) =
      closure (comp_sub.range : Set (presheafValue D₀)) := by
    -- presheafValue_ringOfDef = comp_sub.range.topologicalClosure, whose carrier is closure
    rfl
  -- Use Submodule.span_induction on x ∈ Ideal.map g (locIdeal^n)
  intro x hx
  show x.val ∈ closure T
  refine Submodule.span_induction (p := fun x _ => x.val ∈ closure T) ?_ ?_ ?_ ?_ hx
  · -- Generator: x = g(d) for d ∈ locIdeal^n. val(g d) = fh(sub d) ∈ T.
    rintro x ⟨d, hd, rfl⟩
    exact subset_closure ⟨sub d, ⟨d, hd, rfl⟩, rfl⟩
  · -- Zero
    exact subset_closure ⟨0, (locNhd D₀.P D₀.T D₀.s n).zero_mem, map_zero _⟩
  · -- Addition: closure T is closed under + (T is image of AddSubgroup)
    intro a b _ _ ha hb
    show (a + b).val ∈ closure T
    rw [show (a + b).val = a.val + b.val from rfl]
    -- T = image of AddSubgroup under AddMonoidHom, so T is an additive subgroup image.
    -- Its closure is a closed additive subgroup.
    exact ((locNhd D₀.P D₀.T D₀.s n).map
      fh.toAddMonoidHom).topologicalClosure.add_mem
      (show a.val ∈ ((locNhd D₀.P D₀.T D₀.s n).map
        fh.toAddMonoidHom).topologicalClosure from ha)
      (show b.val ∈ ((locNhd D₀.P D₀.T D₀.s n).map
        fh.toAddMonoidHom).topologicalClosure from hb)
  · -- Scalar mult by r ∈ ringOfDef: use map_mem_closure₂' with multiplication
    -- r ∈ closure(range(comp_sub)) and x.val ∈ closure(T), and range(comp_sub) * T ⊆ T
    intro ⟨r, hr⟩ x _ hx_ih
    show ((⟨r, hr⟩ : presheafValue_ringOfDef D₀) • x).val ∈ closure T
    change r * x.val ∈ closure T
    exact map_mem_closure₂' (fun _ => continuous_const_mul _) (fun _ => continuous_mul_const _)
      (hringOfDef_eq ▸ hr) hx_ih (fun a ha b hb => hact a ha b hb)

/-- Corollary: the val-image of `idealOfDef^n` is contained in `closure(coe '' locNhd n)`. -/
private theorem idealOfDef_pow_val_sub_closure (D₀ : RationalLocData A) (n : ℕ) :
    Subtype.val '' ((presheafValue_idealOfDef D₀ ^ n : Ideal (presheafValue_ringOfDef D₀)) :
      Set (presheafValue_ringOfDef D₀)) ⊆
    closure ((D₀.coeRingHom : Localization.Away D₀.s → presheafValue D₀) ''
      (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s))) := by
  intro x ⟨y, hy, hyx⟩
  rw [← hyx]
  exact idealOfDef_pow_sub_val_preimage_closure D₀ n hy

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
  show ((locSubringToRingOfDef D₀) d).val = x
  -- val(g(d)) = coeRingHom(subtype(d)), subtype(d) = y (from hdy), coeRingHom(y) = x (from hyx)
  exact hyx ▸ congrArg D₀.coeRingHom hdy

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
  -- The subspace topology on ringOfDef makes it a topological ring.
  letI : TopologicalSpace (presheafValue_ringOfDef D₀) :=
    TopologicalSpace.induced Subtype.val inferInstance
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
    simp only [closure_subtype, Set.mem_preimage]
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
    -- Step 2: idealOfDef^n is closed (kernel of continuous map to discrete quotient).
    -- Via AdicCompletionBridge: ringOfDef ≃ AdicCompletion J locSubring,
    -- and AdicCompletion.pow_smul_top_eq_ker_eval gives
    -- J^n • ⊤ = ker(eval n), which is closed (discrete target).
    have hclosed : IsClosed ((presheafValue_idealOfDef D₀ ^ n :
        Ideal (presheafValue_ringOfDef D₀)) : Set (presheafValue_ringOfDef D₀)) := by
      sorry -- AdicCompletion.pow_smul_top_eq_ker_eval via adicCompletionRingEquiv
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
  -- Set up the completion nhds basis from presheafValue_ringOfDef_isOpen proof
  letI := D₀.uniformSpace
  letI := D₀.isUniformAddGroup
  letI := D₀.isTopologicalRing
  open Filter Topology in
  set f := (D₀.coeRingHom : Localization.Away D₀.s → presheafValue D₀) with hf_def
  have hf_zero : f 0 = 0 := map_zero D₀.coeRingHom
  have hbasis := (locBasis D₀.P D₀.T D₀.s D₀.hopen).hasBasis_nhds_zero
  have hdi : IsDenseInducing f := UniformSpace.Completion.isDenseInducing_coe
  have hbasis_compl : (nhds (0 : presheafValue D₀)).HasBasis (fun _ : ℕ => True)
      (fun n => closure (f '' (locNhd D₀.P D₀.T D₀.s n :
        Set (Localization.Away D₀.s)))) := by
    rw [← hf_zero]; exact hbasis.hasBasis_of_isDenseInducing hdi
  -- closure(f '' locNhd n) ⊆ ringOfDef (from presheafValue_ringOfDef_isOpen proof)
  have himage_sub : ∀ n,
      f '' (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s)) ⊆
      ((D₀.coeRingHom.comp (locSubring D₀.P D₀.T D₀.s).subtype).range :
        Set (presheafValue D₀)) := by
    intro n x hx
    obtain ⟨y, hy, hyx⟩ := hx
    obtain ⟨d, _, hdy⟩ := hy
    refine ⟨d, ?_⟩
    show D₀.coeRingHom ((locSubring D₀.P D₀.T D₀.s).subtype d) = x
    exact show D₀.coeRingHom ((locSubring D₀.P D₀.T D₀.s).subtype d) = x from
      hdy ▸ hyx
  have hclosure_sub : ∀ n,
      closure (f '' (locNhd D₀.P D₀.T D₀.s n :
        Set (Localization.Away D₀.s))) ⊆
      (presheafValue_ringOfDef D₀ : Set (presheafValue D₀)) :=
    fun n => closure_mono (himage_sub n)
  -- Subspace nhds of 0 in ringOfDef: preimage of completion nhds under Subtype.val
  -- Since closure(f '' locNhd n) ⊆ ringOfDef, the preimage of this set in ringOfDef
  -- is {x : ringOfDef | val x ∈ closure(f '' locNhd n)} = full preimage.
  -- The subspace nhds 0 has basis from hbasis_compl + inducing_subtype_val.
  have hsubspace_basis : (nhds (0 : presheafValue_ringOfDef D₀)).HasBasis
      (fun _ : ℕ => True) (fun n => Subtype.val ⁻¹'
        (closure (f '' (locNhd D₀.P D₀.T D₀.s n :
          Set (Localization.Away D₀.s))))) := by
    rw [nhds_induced]
    exact hbasis_compl.comap Subtype.val
  constructor
  · -- Condition 1: Each (presheafValue_idealOfDef)^n is open.
    -- It's an additive subgroup containing a 0-nhd, hence open.
    intro n
    apply AddSubgroup.isOpen_of_mem_nhds
      (((presheafValue_idealOfDef D₀) ^ n).toAddSubgroup)
    -- Show 0-nhd basis element is contained in idealOfDef^n.
    apply hsubspace_basis.mem_of_superset (i := n) trivial
    -- Need: Subtype.val ⁻¹' closure(f '' locNhd n) ⊆ (idealOfDef^n : Set ringOfDef)
    intro ⟨x, hx_mem⟩ hx_closure
    -- x ∈ presheafValue_ringOfDef AND x ∈ closure(f '' locNhd n)
    -- By closure_locNhd_sub_idealOfDef_pow:
    -- x ∈ closure(...) ∩ ringOfDef → x ∈ val '' (idealOfDef^n)
    have h_inter : x ∈ closure (f '' (locNhd D₀.P D₀.T D₀.s n :
        Set (Localization.Away D₀.s))) ∩
        (presheafValue_ringOfDef D₀ : Set (presheafValue D₀)) :=
      ⟨hx_closure, hx_mem⟩
    obtain ⟨y, hy_mem, hy_eq⟩ := closure_locNhd_sub_idealOfDef_pow D₀ n h_inter
    -- y : presheafValue_ringOfDef D₀, y ∈ idealOfDef^n, val y = x
    -- So ⟨x, hx_mem⟩ = y (since val is injective on subtypes)
    have : (⟨x, hx_mem⟩ : presheafValue_ringOfDef D₀) = y :=
      Subtype.ext hy_eq.symm
    rw [this]
    exact hy_mem
  · -- Condition 2: Every nhd of 0 contains some (presheafValue_idealOfDef)^n.
    intro s hs
    -- s ∈ nhds 0 (subspace). By hsubspace_basis: s ⊇ preimage of closure(f '' locNhd m).
    obtain ⟨m, -, hm⟩ := hsubspace_basis.mem_iff.mp hs
    -- Take n = m. Show idealOfDef^m ⊆ s.
    refine ⟨m, fun x hx => hm ?_⟩
    -- hx : x ∈ (presheafValue_idealOfDef D₀)^m (as element of ringOfDef)
    -- Need: val x ∈ closure(f '' locNhd m)
    exact idealOfDef_pow_val_sub_closure D₀ m ⟨x, hx, rfl⟩

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

**Surjectivity**: `restrictionMapAlg = D.coeRingHom ∘ algebraicLift` where
`algebraicLift : Localization.Away D₀.s →+* Localization.Away D.s` exists
because `D₀.s` becomes a unit in `Localization.Away D.s` (from the rational
subset containment). The range of `restrictionMapAlg` therefore contains
`D.coeRingHom(Localization.Away D.s)`, which is dense in `presheafValue D`.
Since `sigma = Completion.extension(restrictionMapAlg)` and the extension of
a uniformly continuous map with dense range to a complete space has dense range,
and the range of `sigma` is a complete additive subgroup (continuous image of
a complete uniform space under a uniformly continuous map between uniform add
groups), `range(sigma)` is closed + dense = presheafValue D.

**Injectivity**: If `sigma c = 0`, then `c = 0`. This follows from sigma
being surjective: sigma is a surjective ring hom, so it's a localization
map. Combined with the `s'`-unit property, the `exists_of_eq` condition
is immediate from the localization structure.

The actual proof route uses the completeness of the source: `presheafValue D₀`
is a complete uniform additive group, and `sigma` is a uniformly continuous
ring hom. The image `sigma(presheafValue D₀)` is a complete (hence closed)
additive subgroup of `presheafValue D`. Since it contains the dense image
`D.coeRingHom(Localization.Away D.s)`, it equals all of `presheafValue D`. -/

/-- **Sigma surjectivity (Wedhorn Prop 8.15)**: The restriction map
`restrictionMapHom D₀ D h` is surjective. This is the key consequence of
"completion commutes with localization".

The proof uses the completeness of `presheafValue D₀`: the image of
a complete uniform additive group under a uniformly continuous group hom
is complete, hence closed. Since the image contains the dense subgroup
`D.coeRingHom(Localization.Away D.s)`, it equals all of `presheafValue D`.

**Proof details**: `restrictionMapAlg D₀ D h` factors as
`D.coeRingHom ∘ algebraicLift` where `algebraicLift` exists because
`D₀.s` is a unit in `Localization.Away D.s` (rational containment).
So `range(restrictionMapAlg) ⊇ range(D.coeRingHom)` = dense image.
Then `range(sigma) ⊇ range(restrictionMapAlg)` = dense. Since sigma
is a uniformly continuous additive group hom from a complete uniform
space, its range is a complete additive subgroup (closed). Closed +
dense = everything, so sigma is surjective. -/
private theorem restrictionMapHom_surjective
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [FirstCountableTopology A]
    (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    Function.Surjective (restrictionMapHom D₀ D h) := by
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  set sigma := restrictionMapHom D₀ D h
  -- Step 1: sigma has dense range (contains D.coeRingHom's dense image).
  -- restrictionMapAlg factors: for all r : A,
  --   restrictionMapAlg(algebraMap r) = D.canonicalMap r = D.coeRingHom(algebraMap r)
  -- So range(restrictionMapAlg) ⊇ range(D.canonicalMap) = range(D.coeRingHom ∘ algebraMap)
  -- Since D.coeRingHom has dense range (completion embedding), and
  -- range(sigma) ⊇ sigma(D₀.coeRingHom(Loc)) = range(restrictionMapAlg),
  -- we need range(restrictionMapAlg) to be dense.
  -- This requires showing D.s is a unit in Loc.Away D₀.s and the algebraic lift exists.
  --
  -- Step 2: sigma's range is complete (image of complete space under unif cont map).
  -- UniformSpace.Completion is CompleteSpace, and sigma = extensionHom which is
  -- uniformly continuous.
  --
  -- Step 3: Complete subspace of T2 space is closed. Dense + closed = everything.
  sorry

/-- **Sigma injectivity (Wedhorn Prop 8.15)**: The restriction map
`restrictionMapHom D₀ D h` is injective. Combined with surjectivity,
this gives `sigma` is a ring isomorphism.

The proof uses the same uniform embedding property of the algebraic lift.
Since the algebraic lift `Localization.Away D₀.s → Localization.Away D.s`
is a uniform embedding (reflecting locNhd neighborhoods), its completion
extension `sigma` is also a uniform embedding, hence injective.

Alternative proof from surjectivity: sigma is surjective (proved above) and
a ring hom between completions. If ker(sigma) ≠ {0}, then presheafValue D₀
surjects onto presheafValue D with nontrivial kernel, making presheafValue D
a proper quotient. But the localization data ensures this quotient must
actually be trivial (via the faithfulness of the localization topology). -/
private theorem restrictionMapHom_injective
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
  -- The algebraic lift Localization.Away D₀.s → Localization.Away D.s
  -- is a uniform embedding between localization topologies (the locIdeal
  -- neighborhoods in D₀ map to and from the locIdeal neighborhoods in D,
  -- because both are generated by the same ideal I from the pair of
  -- definition). The completion extension of a uniform embedding is
  -- again a uniform embedding (hence injective).
  sorry

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
  -- Use the specialized constructor for IsLocalization.Away.mk
  letI : Algebra (presheafValue D₀) (presheafValue D) := (restrictionMapHom D₀ D h).toAlgebra
  -- Set up uniform space instances
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  -- Abbreviations
  set sigma := restrictionMapHom D₀ D h with hsigma_def
  set s' := D₀.canonicalMap D.s with hs'_def
  -- Key fact: sigma on the dense image = restrictionMapAlg
  have hsigma_coe : ∀ a : Localization.Away D₀.s,
      sigma (D₀.coeRingHom a) = restrictionMapAlg D₀ D h a :=
    fun a => restrictionMapHom_coe' D₀ D h a
  -- Key fact: restrictionMapAlg on algebraMap = canonicalMap
  have hsigma_alg : ∀ r : A,
      restrictionMapAlg D₀ D h (algebraMap A _ r) = D.canonicalMap r := by
    intro r; simp only [restrictionMapAlg, IsLocalization.Away.lift_eq]
  have hsigma_s' : sigma s' = D.canonicalMap D.s := by
    show sigma (D₀.coeRingHom (algebraMap A (Localization.Away D₀.s) D.s)) = D.canonicalMap D.s
    rw [hsigma_coe, hsigma_alg]
  -- Condition 1: s' maps to a unit in presheafValue D
  have hunit : IsUnit (sigma s') := by
    show IsUnit (sigma (D₀.coeRingHom (algebraMap A (Localization.Away D₀.s) D.s)))
    rw [hsigma_coe, hsigma_alg]
    exact isUnit_s_in_presheafValue D
  -- Dense image surj: for z = D.coeRingHom(w), exists n, a with z * u^n = sigma(a)
  have h_dense : ∀ w : Localization.Away D.s,
      ∃ (n : ℕ) (a : presheafValue D₀),
        D.coeRingHom w * sigma s' ^ n = sigma a := by
    intro w
    obtain ⟨n, r, hw⟩ := IsLocalization.Away.surj D.s w
    refine ⟨n, D₀.canonicalMap r, ?_⟩
    rw [hsigma_s']
    change D.coeRingHom w * (D.coeRingHom (algebraMap A _ D.s)) ^ n =
      sigma (D₀.canonicalMap r)
    rw [← map_pow D.coeRingHom, ← map_mul D.coeRingHom, hw]
    show D.canonicalMap r = sigma (D₀.canonicalMap r)
    conv_rhs => rw [show D₀.canonicalMap r =
      D₀.coeRingHom (algebraMap A (Localization.Away D₀.s) r) from rfl]
    rw [hsigma_coe, hsigma_alg]
  -- Apply the specialized constructor
  exact IsLocalization.Away.mk (D₀.canonicalMap D.s) hunit
    -- Surj: sigma surjective (Prop 8.15) gives n = 0 directly.
    (fun z => by
      obtain ⟨a, ha⟩ := restrictionMapHom_surjective D₀ D h z
      exact ⟨0, a, by rw [pow_zero, mul_one]; exact ha.symm⟩)
    -- Eq: sigma injective (Prop 8.15) gives the kernel condition.
    (fun a b hab => by
      suffices ∀ c : presheafValue D₀, sigma c = 0 → ∃ n : ℕ, s' ^ n * c = 0 by
        obtain ⟨n, hn⟩ := this (a - b) (by rw [map_sub]; exact sub_eq_zero.mpr hab)
        exact ⟨n, by rw [mul_sub, sub_eq_zero] at hn; exact hn⟩
      intro c hc
      exact ⟨0, by simp [restrictionMapHom_injective D₀ D h
        (hc.trans (map_zero sigma).symm)]⟩)

end ValuationSpectrum
