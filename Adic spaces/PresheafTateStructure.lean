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

/-- `val '' idealOfDef^n` is closed in `presheafValue`. Equivalent to:
`idealOfDef^n` is closed in the subspace topology on `ringOfDef`.

**Proof route** (via AdicCompletionBridge):
1. The subspace topology on `locSubring ⊆ Localization` = `locIdeal`-adic topology
   (nhds basis `locNhd m = subtype '' locIdeal^m` restricts to `locIdeal^m`).
2. `Completion(locSubring) ≃+* AdicCompletion(locIdeal, locSubring)` via bridge.
3. `ringOfDef ≃ₜ Completion(locSubring) ≃ₜ AdicCompletion(locIdeal, locSubring)`.
4. Under this homeomorphism, `idealOfDef^n` corresponds to `ker(evalₐ n)`:
   For Noetherian `locSubring`: `ker(evalₐ n) = Ideal.map of (locIdeal^n)`
   by `AdicCompletion.map_exact` (`0 → locIdeal^n → locSubring → R/I^n → 0`).
5. `ker(evalₐ n)` is closed (preimage of `{0}` in discrete `locSubring/locIdeal^n`).
6. Transfer closedness through the homeomorphism.

**Missing infrastructure**: Steps (3)-(4) require formalizing the homeomorphism
`ringOfDef ≃ₜ AdicCompletion(locIdeal, locSubring)` and the kernel identification
`ker(evalₐ n) = Ideal.map of (locIdeal^n)`. See `AdicCompletionBridge.lean`. -/
private theorem idealOfDef_pow_val_isClosed (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)] (n : ℕ) :
    IsClosed (Subtype.val '' ((presheafValue_idealOfDef D₀ ^ n :
      Ideal (presheafValue_ringOfDef D₀)) :
      Set (presheafValue_ringOfDef D₀)) : Set (presheafValue D₀)) := by
  letI := D₀.uniformSpace; letI := D₀.isUniformAddGroup; letI := D₀.isTopologicalRing
  -- ringOfDef is a closed subring of presheafValue (it's a topological closure)
  have hclosed_ring : IsClosed (presheafValue_ringOfDef D₀ : Set (presheafValue D₀)) :=
    Subring.isClosed_topologicalClosure _
  -- The subspace topology on ringOfDef makes it a topological ring
  letI : TopologicalSpace (presheafValue_ringOfDef D₀) :=
    TopologicalSpace.induced Subtype.val inferInstance
  haveI : IsTopologicalRing (presheafValue_ringOfDef D₀) :=
    Subring.instIsTopologicalRing _
  -- Per reviewer: the non-circular route uses the AdicCompletionBridge.
  --
  -- Step 1: The subspace uniformity on locSubring ⊆ Localization.Away s
  --         equals the locIdeal-adic uniformity (reviewer confirmed).
  -- Step 2: Completion(locSubring, J-adic) ≅ ringOfDef (closure in ambient completion)
  --         by the standard completion fact for uniform embeddings.
  -- Step 3: AdicCompletionBridge gives Completion(locSubring) ≃ AdicCompletion(J, locSubring).
  -- Step 4: In AdicCompletion: ker(eval_n) is closed (preimage of {0} in discrete quotient).
  -- Step 5: Under the bridge + step 2: ker(eval_n) transfers to a closed subset of ringOfDef.
  -- Step 6: This closed subset = idealOfDef^n (by ideal_smul_top_eq_self + Ideal.map_pow).
  -- Step 7: val '' (closed subset of closed subring) is closed in the ambient ring.
  --
  -- Alternatively (Wedhorn Prop 6.17): every ideal in a complete Noetherian
  -- topological ring is closed. Since ringOfDef = Completion(locSubring) is
  -- complete and Noetherian, idealOfDef^n is closed in ringOfDef.
  -- Then val '' (idealOfDef^n) is closed by closed embedding.
  sorry -- Needs: AdicCompletionBridge homeomorphism for locSubring
        -- OR: Prop 6.17 (ideals in complete Noetherian rings are closed)

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

end ValuationSpectrum
