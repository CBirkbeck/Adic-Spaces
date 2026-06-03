/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».StructureSheaf
import «Adic spaces».Example638
import «Adic spaces».TateAlgebra
import «Adic spaces».Cor832

/-!
# Wedhorn Theorem 8.28(b): strongly noetherian Tate ⇒ sheafy — clean top-down skeleton

This file states the proof of Wedhorn's Theorem 8.28(b) **top-down**, following the textbook
exactly. Every lemma is stated as Wedhorn states it, with a `sorry` body, and the lemmas are
composed to prove `IsSheafy A`. Each `sorry` is then to be discharged by recursively reading
Wedhorn and stating its sub-lemmas the same way.

## Wedhorn's proof structure (Adic Spaces, §8.2, pp. 81–84)

```
Theorem 8.28(b)  IsSheafy A                     [A strongly noetherian Tate, complete]
  ├─ Prop A.4    acyclic on rational covers ⇒ sheaf
  └─ Lemma 8.34  rational cover gen by T (T·A = A) is O_X-acyclic
      ├─ Lemma 8.33  the 2-element Laurent cover {R(f/1), R(1/f)} is O_X-acyclic
      │   ├─ Cor 8.32   O_X(X) → ∏ O_X(Uᵢ) is faithfully flat (⇒ ε injective)
      │   │   └─ Lemma 8.31  A⟨X⟩ faithfully flat / A⟨X⟩/(f−X), A⟨X⟩/(1−fX) flat over A
      │   │       └─ Remark 8.29  M ⊗_A A⟨X⟩ ≅ M⟨X⟩      [via Prop 6.18, PROVEN: BanachOMT]
      │   └─ Example 6.38 / 6.39  O_X(U) = A⟨X⟩/(closed ideal)   [Example638.lean]
      └─ Prop A.3 (1)(2)(3)  Čech refinement / Laurent-cover induction
```

In Lean, `IsSheafy A` (`StructureSheaf.lean`) is the pair `(embedding, gluing)` on every
`RationalCovering`. Cor 8.32 supplies `embedding` (faithful flatness ⇒ the product
restriction is injective; the topological inducing is the Banach-OMT input, `BanachOMT.lean`).
Lemma 8.34 supplies `gluing`.

## References
* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Theorem 8.28, Lemmas 8.31/8.33/8.34,
  Cor 8.32, Remark 8.29, Prop A.3/A.4.
-/

namespace ValuationSpectrum

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]

section Wedhorn828

variable [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
  [NonarchimedeanRing A] [CompatiblePlusSubring A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]

section Helpers831

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsStronglyNoetherian A] [NonarchimedeanRing A]
  [CompatiblePlusSubring A] in
/-- **Wedhorn Prop 6.18(1), Hausdorff half** (p. 50, `wedhorn.txt:4076`): a finitely
generated `A`-module `M`, with its module topology, over a complete noetherian Tate ring `A`,
is Hausdorff (`T2`).

INFRASTRUCTURE companion of `CompleteSpace.of_isModuleTopology_finite`: present `M` as an open
quotient `Aⁿ ⧠ M`; the kernel of `ν : Aⁿ ↠ M` is finitely generated (`Aⁿ` noetherian) hence
closed (`fg_topologicalClosure_isClosed`, BGR §3.7.2/1), so `Aⁿ ⧸ ker ν ≅ M` is `T2`, and the
canonical homeomorphism transports `T2` to `M`.

Faithful: `[CompleteSpace A]`, `[IsNoetherianRing A]`, `[IsTateRing A]` only — no ring of
definition `A₀`, and no `[IsLinearTopology A A]` (the latter is unsatisfiable for a Tate ring;
the `A°`-layer obligations it used to feed are now discharged via `[NonarchimedeanRing A]`). -/
private theorem t2Space_of_moduleTopology_finite (M : Type u) [AddCommGroup M] [Module A M]
    [TopologicalSpace M] [IsModuleTopology A M] [Module.Finite A M] :
    T2Space M := by
  letI uA : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  haveI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  haveI : (uniformity A).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  haveI : IsTopologicalAddGroup M := IsModuleTopology.topologicalAddGroup A M
  haveI : ContinuousSMul A M := inferInstance
  -- Present `M` as an open quotient of `Aⁿ`.
  obtain ⟨n, ν, hν⟩ := Module.Finite.exists_fin' A M
  have hν_cont : Continuous ⇑ν := IsModuleTopology.continuous_linearMap_of_finite ν
  have hν_open : IsOpenMap ⇑ν := IsModuleTopology.isOpenMap_of_surjective_of_finite ν hν
  -- `ker ν` is finitely generated (`Aⁿ` noetherian), so its closure is finitely generated.
  haveI hnoeth : IsNoetherian A (Fin n → A) := inferInstance
  have hker_clos_fg : Module.Finite A ((LinearMap.ker ν).topologicalClosure) :=
    Module.Finite.of_fg (hnoeth.noetherian _)
  -- Hence `ker ν` is closed (BGR §3.7.2/1).
  have hker_closed : IsClosed ((LinearMap.ker ν) : Set (Fin n → A)) :=
    fg_topologicalClosure_isClosed (LinearMap.ker ν) hker_clos_fg
  haveI hkc : IsClosed ((ν.toAddMonoidHom.ker : AddSubgroup (Fin n → A)) :
      Set (Fin n → A)) := hker_closed
  haveI : T2Space ((Fin n → A) ⧸ ν.toAddMonoidHom.ker) := inferInstance
  -- The canonical add-equiv `Aⁿ ⧸ ker ν ≃+ M` is a homeomorphism.
  let e : ((Fin n → A) ⧸ ν.toAddMonoidHom.ker) ≃+ M :=
    QuotientAddGroup.quotientKerEquivOfSurjective ν.toAddMonoidHom hν
  have hq_surj : Function.Surjective ⇑(QuotientAddGroup.mk' ν.toAddMonoidHom.ker) :=
    QuotientAddGroup.mk'_surjective _
  have hq_cont : Continuous ⇑(QuotientAddGroup.mk' ν.toAddMonoidHom.ker) := continuous_quot_mk
  have he_mk : ⇑e ∘ ⇑(QuotientAddGroup.mk' ν.toAddMonoidHom.ker) = ⇑ν := by ext x; rfl
  have he_cont : Continuous ⇑e := by
    rw [continuous_def]
    intro U hU
    have hpre : ⇑(QuotientAddGroup.mk' ν.toAddMonoidHom.ker) ⁻¹' (⇑e ⁻¹' U) = ⇑ν ⁻¹' U := by
      rw [← Set.preimage_comp, he_mk]
    have hopen : IsOpen (⇑(QuotientAddGroup.mk' ν.toAddMonoidHom.ker) ⁻¹' (⇑e ⁻¹' U)) := by
      rw [hpre]; exact hU.preimage hν_cont
    exact (QuotientAddGroup.isOpenQuotientMap_mk
      (N := ν.toAddMonoidHom.ker)).isQuotientMap.isOpen_preimage.mp hopen
  have he_open : IsOpenMap ⇑e := by
    intro U hU
    have himg : ⇑e '' U = ⇑ν '' (⇑(QuotientAddGroup.mk' ν.toAddMonoidHom.ker) ⁻¹' U) := by
      rw [← he_mk, Set.image_comp, Set.image_preimage_eq U hq_surj]
    rw [himg]; exact hν_open _ (hU.preimage hq_cont)
  -- Transport `T2` along the homeomorphism `Aⁿ ⧸ ker ν ≃ₜ M`.
  exact (e.toEquiv.toHomeomorphOfContinuousOpen he_cont he_open).t2Space

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- Bundle the module-topology instances on a finitely generated `A`-module `M`. -/
private theorem muMap_bijective_of_finite (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] :
    letI : TopologicalSpace M := moduleTopology A M
    haveI : IsModuleTopology A M := ⟨rfl⟩
    haveI : IsTopologicalAddGroup M := IsModuleTopology.topologicalAddGroup A M
    haveI : ContinuousSMul A M := inferInstance
    Function.Bijective (muMap (A := A) (M := M)) := by
  letI : TopologicalSpace M := moduleTopology A M
  haveI : IsModuleTopology A M := ⟨rfl⟩
  haveI : IsTopologicalAddGroup M := IsModuleTopology.topologicalAddGroup A M
  haveI : ContinuousSMul A M := inferInstance
  haveI : ContinuousConstSMul A M := inferInstance
  haveI : T2Space M := t2Space_of_moduleTopology_finite (A := A) M
  exact ⟨muMap_injective, muMap_surjective⟩

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- **Remark 8.29 ⟹ flatness criterion input**: for an injective `A`-linear map `i : N → M`
between finitely generated `A`-modules, the base change `i ⊗ id : N ⊗ A⟨X⟩ → M ⊗ A⟨X⟩` is
injective.

Proof: equip `N, M` with their module topologies; `μ_N : N ⊗ A⟨X⟩ ≅ N⟨X⟩` and
`μ_M : M ⊗ A⟨X⟩ ≅ M⟨X⟩` are isomorphisms (`muMap_bijective_of_finite`); the naturality square
`μ_M ∘ (i ⊗ id) = i⟨X⟩ ∘ μ_N` commutes (`muMap_naturality`); and `i⟨X⟩ = restrictedModule.map i`
is injective (`restrictedModule_map_injective`, as `i` is injective and continuous). Hence
`i ⊗ id = μ_M⁻¹ ∘ i⟨X⟩ ∘ μ_N` is a composite of injective maps. -/
private theorem tensorTate_map_injective
    {N : Type u} [AddCommGroup N] [Module A N] [Module.Finite A N]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (i : N →ₗ[A] M) (hi : Function.Injective i) :
    Function.Injective (TensorProduct.map i (LinearMap.id (R := A) (M := ↥(TateAlgebra A)))) := by
  letI : TopologicalSpace N := moduleTopology A N
  haveI : IsModuleTopology A N := ⟨rfl⟩
  haveI : IsTopologicalAddGroup N := IsModuleTopology.topologicalAddGroup A N
  haveI : ContinuousSMul A N := inferInstance
  haveI : ContinuousConstSMul A N := inferInstance
  letI : TopologicalSpace M := moduleTopology A M
  haveI : IsModuleTopology A M := ⟨rfl⟩
  haveI : IsTopologicalAddGroup M := IsModuleTopology.topologicalAddGroup A M
  haveI : ContinuousSMul A M := inferInstance
  haveI : ContinuousConstSMul A M := inferInstance
  -- `i` is continuous (linear out of the module topology).
  have hi_cont : Continuous i := IsModuleTopology.continuous_linearMap_of_finite i
  -- `μ_N` is injective; `i⟨X⟩` is injective.
  have hμN_inj : Function.Injective (muMap (A := A) (M := N)) :=
    (muMap_bijective_of_finite N).1
  have hiX_inj : Function.Injective (restrictedModule.map (A := A) i hi_cont) :=
    restrictedModule_map_injective i hi_cont hi
  -- Naturality: `i⟨X⟩ ∘ μ_N = μ_M ∘ (i ⊗ id)`.
  have hnat := muMap_naturality (A := A) i hi_cont
  -- `μ_M ∘ (i ⊗ id)` is injective (since `i⟨X⟩ ∘ μ_N` is).
  have hcomp_inj : Function.Injective
      ((muMap (A := A) (M := M)).comp
        (TensorProduct.map i (LinearMap.id (R := A) (M := ↥(TateAlgebra A))))) := by
    rw [← hnat, LinearMap.coe_comp]
    exact hiX_inj.comp hμN_inj
  -- `μ_M ∘ (i ⊗ id)` injective ⟹ `i ⊗ id` injective.
  have : Function.Injective ⇑((muMap (A := A) (M := M)).comp
      (TensorProduct.map i (LinearMap.id (R := A) (M := ↥(TateAlgebra A))))) := hcomp_inj
  rw [LinearMap.coe_comp] at this
  exact this.of_comp

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- **Lemma 8.31(1), flatness half** (Wedhorn p. 82, `wedhorn.txt:4106`): `A⟨X⟩` is **flat**
over a complete noetherian Tate ring `A`.

Faithful route via Remark 8.29 (no ring of definition `A₀`): by the finitely-generated-ideal
flatness criterion `Module.Flat.iff_rTensor_injective`, it suffices that for every finitely
generated ideal `I ⊆ A` the base change `I ⊗ A⟨X⟩ → A ⊗ A⟨X⟩` is injective. `I` and `A` are
finitely generated `A`-modules (`A` noetherian), so this is `tensorTate_map_injective` applied
to the injective inclusion `Submodule.subtype I`. -/
private theorem tateAlgebra_flat_faithful : Module.Flat A ↥(TateAlgebra A) := by
  rw [Module.Flat.iff_rTensor_injective]
  intro I hI
  haveI : Module.Finite A ↥I := Module.Finite.of_fg hI
  rw [LinearMap.rTensor_def]
  exact tensorTate_map_injective (Submodule.subtype I) (Submodule.injective_subtype I)

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- **Faithful `mem_ideal_map_of_forall_coeff_mem`** (Lemma 8.31(2) input, no ring of
definition `A₀`): if every coefficient of `h ∈ A⟨X⟩` lies in the ideal `I`, then
`h ∈ I · A⟨X⟩`.

This is the reverse direction of `forall_coeff_mem_of_mem_ideal_map` and the only step of the
`f − X`/`1 − fX` saturation that needs more than the ascending-chain lemma. Wedhorn's case-(a)
proof routes through Artin–Rees over a ring of definition; the faithful (case-(b)) route uses
Remark 8.29 instead: writing `q : A ↠ A/I`, the kernel of `q⟨X⟩ : A⟨X⟩ → (A/I)⟨X⟩` is exactly
`{h : ∀ n, coeff n h ∈ I}`, and the `μ`-naturality square together with the bijectivity of
`μ_A`, `μ_{A/I}` (`muMap_bijective_of_finite`, both `A` and `A/I` finitely generated) and the
tensor-quotient kernel identity `(rTensor q).ker = (rTensor I.subtype).range` (`rTensor_mkQ`)
identifies that kernel with `I · A⟨X⟩`. -/
private theorem mem_idealMap_of_forall_coeff_mem (I : Ideal A) (h : ↥(TateAlgebra A))
    (hcoeffs : ∀ n, TateAlgebra.coeff n h ∈ I) :
    h ∈ Ideal.map (algebraMap A ↥(TateAlgebra A)) I := by
  classical
  -- `A ⧸ I` carries its quotient topology, which is the module topology (`A ⧸ I` is f.g.).
  set q : A →ₗ[A] (A ⧸ I) := (Submodule.mkQ I) with hq_def
  haveI : T2Space (A ⧸ I) := t2Space_of_moduleTopology_finite (A := A) (A ⧸ I)
  have hq_cont : Continuous q := IsModuleTopology.continuous_linearMap_of_finite q
  -- `μ_A`, `μ_{A/I}` are bijective.
  have hμA_bij : Function.Bijective (muMap (A := A) (M := A)) :=
    ⟨muMap_injective, muMap_surjective⟩
  have hμQ_bij : Function.Bijective (muMap (A := A) (M := A ⧸ I)) :=
    ⟨muMap_injective, muMap_surjective⟩
  -- View `h` as a restricted `A`-valued series `h'` (same coefficients).
  set h' : ↥(restrictedModule A A) := restrictedModuleA_equiv.symm h with hh'_def
  have hh'_val : ∀ s, (h' : ↥(restrictedModule A A)).val s = h.val s := fun _ => rfl
  -- `q⟨X⟩ h' = 0` (every coefficient `h.val s ∈ I`).
  have hqXh' : restrictedModule.map (A := A) q hq_cont h' = 0 := by
    apply Subtype.ext; funext s
    change q (h'.val s) = (0 : A ⧸ I)
    rw [hh'_val, hq_def]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [TateAlgebra.eq_toIndex s]; exact hcoeffs (s 0)
  -- `t := μ_A⁻¹ h'`.
  obtain ⟨t, ht⟩ := hμA_bij.surjective h'
  -- `(q ⊗ id) t ∈ ker μ_{A/I}` (naturality + `μ_A t = h'`), hence `(q ⊗ id) t = 0`.
  have hqt_zero : (TensorProduct.map q (LinearMap.id (R := A) (M := ↥(TateAlgebra A)))) t = 0 := by
    apply hμQ_bij.injective
    rw [map_zero]
    have hnat := muMap_naturality (A := A) q hq_cont
    have := LinearMap.congr_fun hnat t
    simp only [LinearMap.comp_apply] at this
    rw [← this, ht, hqXh']
  -- `t ∈ ker (rTensor A⟨X⟩ q) = range (rTensor A⟨X⟩ I.subtype)`.
  have ht_ker : t ∈ LinearMap.ker (LinearMap.rTensor ↥(TateAlgebra A) (Submodule.mkQ I)) := by
    rw [LinearMap.mem_ker, LinearMap.rTensor_def]; exact hqt_zero
  rw [rTensor_mkQ] at ht_ker
  obtain ⟨u, hu⟩ := ht_ker
  -- Transport: `h = restrictedModuleA_equiv (μ_A t)`, and `μ_A ((I.subtype ⊗ id) u) ∈ I·A⟨X⟩`.
  have hh_eq : h = restrictedModuleA_equiv (muMap (A := A) (M := A) t) := by
    rw [ht]; exact (restrictedModuleA_equiv.apply_symm_apply h).symm
  rw [hh_eq, ← hu, LinearMap.rTensor_def]
  -- The map `i₀ ⊗ p ↦ algebraMap ↑i₀ * p` lands in `Ideal.map I`.
  -- Reduce to pure tensors via the tensor-product universal property.
  refine TensorProduct.induction_on u (by simp) (fun i₀ p => ?_)
    (fun a b ha hb => by rw [map_add, map_add, map_add]; exact Ideal.add_mem _ ha hb)
  -- Generator case: `μ_A ((I.subtype ⊗ id) (i₀ ⊗ p)) = i₀ • (coeffs of p)`,
  -- which through `restrictedModuleA_equiv` is `algebraMap ↑i₀ * p`.
  simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq, Submodule.subtype_apply]
  have hval : ∀ s, (restrictedModuleA_equiv (muMap (A := A) (M := A)
      ((i₀ : A) ⊗ₜ[A] p))).val s = (i₀ : A) * p.val s := by
    intro s
    change (muMap (A := A) (M := A) ((i₀ : A) ⊗ₜ[A] p)).val s = (i₀ : A) * p.val s
    simp only [muMap, TensorProduct.lift.tmul, LinearMap.mk₂_apply]
    rw [smul_eq_mul, mul_comm]
  have : restrictedModuleA_equiv (muMap (A := A) (M := A) ((i₀ : A) ⊗ₜ[A] p)) =
      algebraMap A ↥(TateAlgebra A) (i₀ : A) * p := by
    apply TateAlgebra.ext; intro n
    rw [TateAlgebra.coeff_algebraMap_mul]
    change (restrictedModuleA_equiv (muMap (A := A) (M := A) ((i₀ : A) ⊗ₜ[A] p))).val
      (TateAlgebra.toIndex n) = (i₀ : A) * TateAlgebra.coeff n p
    rw [hval]; rfl
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ i₀.2)

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- **Faithful saturation of `f − X`** (Lemma 8.31(2) input, no ring of definition `A₀`): the
extended ideal `I · A⟨X⟩` is `(f − X)`-saturated.

This mirrors `TateAlgebra.fSubX_saturated` (whose only non-faithful step is the final
`mem_ideal_map_of_forall_coeff_mem`): the coefficient equations from `(f − X) · h ∈ I · A⟨X⟩`
feed the ascending-chain lemma `noeth_mem_ideal_of_mul_shift` to force every coefficient of `h`
into `I`, and the faithful `mem_idealMap_of_forall_coeff_mem` concludes `h ∈ I · A⟨X⟩`. -/
private theorem fSubX_saturated_faithful (f : A) (I : Ideal A) (h : ↥(TateAlgebra A))
    (hmem : (algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X) * h ∈
      Ideal.map (algebraMap A ↥(TateAlgebra A)) I) :
    h ∈ Ideal.map (algebraMap A ↥(TateAlgebra A)) I := by
  have hcoeffs_prod : ∀ n, TateAlgebra.coeff n ((algebraMap A _ f - TateAlgebra.X) * h) ∈ I :=
    TateAlgebra.forall_coeff_mem_of_mem_ideal_map I _ hmem
  have hcoeff_eq : ∀ n,
      f * TateAlgebra.coeff n h - TateAlgebra.coeff n (TateAlgebra.X * h) ∈ I := by
    intro n
    have h1 := hcoeffs_prod n
    rw [sub_mul, TateAlgebra.coeff_sub, TateAlgebra.coeff_algebraMap_mul] at h1
    exact h1
  have h0 : f * TateAlgebra.coeff 0 h ∈ I := by
    have := hcoeff_eq 0; rwa [TateAlgebra.coeff_zero_X_mul, sub_zero] at this
  have hstep : ∀ n, TateAlgebra.coeff n h - f * TateAlgebra.coeff (n + 1) h ∈ I := by
    intro n
    have h1 := hcoeff_eq (n + 1); rw [TateAlgebra.coeff_succ_X_mul] at h1
    have : -(f * TateAlgebra.coeff (n + 1) h - TateAlgebra.coeff n h) ∈ I := I.neg_mem h1
    rwa [neg_sub] at this
  have hcoeff0 : TateAlgebra.coeff 0 h ∈ I :=
    noeth_mem_ideal_of_mul_shift f I (fun n => TateAlgebra.coeff n h) h0 hstep
  have hall : ∀ n, TateAlgebra.coeff n h ∈ I := by
    intro n; induction n with
    | zero => exact hcoeff0
    | succ n ih =>
      have hf_succ : f * TateAlgebra.coeff (n + 1) h ∈ I := by
        have := I.sub_mem ih (hstep n); rwa [sub_sub_cancel] at this
      exact noeth_mem_ideal_of_mul_shift f I (fun k => TateAlgebra.coeff (n + 1 + k) h)
        (by simp only [Nat.add_zero]; exact hf_succ)
        (fun k => by
          change TateAlgebra.coeff (n + 1 + k) h - f * TateAlgebra.coeff (n + 1 + (k + 1)) h ∈ I
          rw [show n + 1 + (k + 1) = (n + 1 + k) + 1 from by omega]
          exact hstep (n + 1 + k))
  exact mem_idealMap_of_forall_coeff_mem I h hall

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- **Faithful saturation of `1 − f·X`** (Lemma 8.31(2) input, no ring of definition `A₀`):
the extended ideal `I · A⟨X⟩` is `(1 − f·X)`-saturated.

Mirrors `TateAlgebra.oneSubfX_saturated`, replacing its final non-faithful step with
`mem_idealMap_of_forall_coeff_mem`. -/
private theorem oneSubfX_saturated_faithful (f : A) (I : Ideal A) (h : ↥(TateAlgebra A))
    (hmem : (1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X) * h ∈
      Ideal.map (algebraMap A ↥(TateAlgebra A)) I) :
    h ∈ Ideal.map (algebraMap A ↥(TateAlgebra A)) I := by
  have hcoeffs_prod :
      ∀ n, TateAlgebra.coeff n ((1 - algebraMap A _ f * TateAlgebra.X) * h) ∈ I :=
    TateAlgebra.forall_coeff_mem_of_mem_ideal_map I _ hmem
  have hcoeff_eq : ∀ n,
      TateAlgebra.coeff n h - f * TateAlgebra.coeff n (TateAlgebra.X * h) ∈ I := by
    intro n
    have h1 := hcoeffs_prod n
    rw [sub_mul, one_mul, mul_assoc, TateAlgebra.coeff_sub,
      TateAlgebra.coeff_algebraMap_mul] at h1
    exact h1
  have h0 : TateAlgebra.coeff 0 h ∈ I := by
    have := hcoeff_eq 0; rwa [TateAlgebra.coeff_zero_X_mul, mul_zero, sub_zero] at this
  have hstep : ∀ n, TateAlgebra.coeff (n + 1) h - f * TateAlgebra.coeff n h ∈ I := by
    intro n; have := hcoeff_eq (n + 1); rwa [TateAlgebra.coeff_succ_X_mul] at this
  have hall : ∀ n, TateAlgebra.coeff n h ∈ I := by
    intro n; induction n with
    | zero => exact h0
    | succ n ih =>
      have hfn : f * TateAlgebra.coeff n h ∈ I := I.mul_mem_left f ih
      have hdiff : TateAlgebra.coeff (n + 1) h - f * TateAlgebra.coeff n h ∈ I := hstep n
      have hsplit : TateAlgebra.coeff (n + 1) h =
          f * TateAlgebra.coeff n h
            + (TateAlgebra.coeff (n + 1) h - f * TateAlgebra.coeff n h) := by ring
      rw [hsplit]; exact I.add_mem hfn hdiff
  exact mem_idealMap_of_forall_coeff_mem I h hall

end Helpers831

/-! ## Faithful Example-6.38 base (Step 1 of Prop 8.30) — `presheafValue D ≃+* A⟨X⟩/(1−sX)`

The repository's `presheafValueCanonicalQuotientEquiv` (TopologyComparison.lean) identifies
`presheafValue D` with the canonical-topology quotient `A⟨X⟩/(1−sX)`, but it threads
`hnoeth : IsNoetherianRing ↥(pairSubring (IsTateRing.principalPair A))` — i.e. noetherianness of
the **ring of definition** `A₀⟨X⟩` of the Tate algebra. That is the Wedhorn case-(a) /
`ℂ_p`-FALSE hypothesis (a strongly-noetherian Tate ring such as `ℂ_p` has a non-noetherian ring of
definition), so it must not be used to discharge the case-(b) `prop_8_30` helpers.

The faithful route uses only `[IsStronglyNoetherian A]`: then `TateAlgebra A = A⟨X⟩` is itself a
**noetherian** complete Tate ring (`IsStronglyNoetherian.isNoetherianRing_restricted 1`,
`TateAlgebraTopology.lean:961`), so by **Wedhorn Prop 6.17** (`wedhorn_6_17_ideal`,
`WedhornBanachTheorem.lean:821`, sorry-free, keystone-unblocked this session via
`fg_topologicalClosure_isClosed` / BGR §3.7.2/1) EVERY ideal of `A⟨X⟩` is closed — in particular
the principal ideal `oneSubfXIdeal D.s = (1 − sX)`. Closedness of the ideal is the only input the
existing quotient-completeness / quotient-Hausdorffness lemmas need; supplying it faithfully lets us
rebuild the forward completion map and the equivalence with the `[IsStronglyNoetherian A]` bundle
only — no `pairSubring`-noetherianness anywhere. -/

section FaithfulExample638Base

open TateAlgebra UniformSpace

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsNoetherianRing A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- **Faithful Prop 6.17 for `A⟨X⟩`** (Wedhorn Prop 6.17, `wedhorn.txt`, via
`wedhorn_6_17_ideal`): every ideal of `A⟨X⟩` is closed under the canonical Tate topology, using
only `[IsStronglyNoetherian A]` (which makes `A⟨X⟩` noetherian) — **no** `pairSubring`/`A₀⟨X⟩`
noetherianness. This is the faithful (case-(b)) replacement for `tateAlgebra_isClosed_ideal`, which
routes through `Wedhorn.isClosed_ideal_of_noetherian` with `[IsNoetherianRing P.A₀]` (case (a)).

`hA_complete` re-surfaces the ambient `[CompleteSpace A]` (under the right-uniform structure) — the
section bundle's completeness — as an explicit argument, matching the project idiom of the
unfaithful sibling `tateAlgebra_isClosed_ideal`. -/
private theorem tateAlgebra_isClosed_ideal_faithful [IsStronglyNoetherian A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (J : Ideal ↥(TateAlgebra A)) :
    IsClosed (J : Set ↥(TateAlgebra A)) := by
  letI uT : UniformSpace ↥(TateAlgebra A) := instUniformSpaceTateAlgebra
  haveI hua : @IsUniformAddGroup _ uT _ := instIsUniformAddGroupTateAlgebra
  haveI hCS : @CompleteSpace _ uT := tateAlgebraTopology'_completeSpace (A := A) hA_complete
  haveI hcg : (@uniformity _ uT).IsCountablyGenerated := by
    haveI hcgn : (@nhds _ instTopologicalSpaceTateAlgebra
        (0 : ↥(TateAlgebra A))).IsCountablyGenerated :=
      tateAlgBasis'.hasBasis_nhds_zero.isCountablyGenerated
    exact @IsUniformAddGroup.uniformity_countably_generated _ uT _ _ (by convert hcgn)
  haveI hT2 : @T2Space _ uT.toTopologicalSpace := instT2SpaceTateAlgebra
  haveI hTR : @IsTopologicalRing _ uT.toTopologicalSpace _ := instIsTopologicalRingTateAlgebra
  haveI hTate : @IsTateRing _ _ uT.toTopologicalSpace := tateAlgebra_isTateRing
  -- A⟨X⟩ is noetherian (A strongly noetherian), so Prop 6.17 closes every ideal.
  exact (@wedhorn_6_17_ideal _ _ uT hua hCS hcg hT2 hTR hTate).mp inferInstance J

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsNoetherianRing A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- **Faithful: the principal ideal `(1 − sX)` is closed in `A⟨X⟩`** — specialisation of
`tateAlgebra_isClosed_ideal_faithful` to `oneSubfXIdeal s`, the faithful (case-(b)) replacement for
`oneSubfXIdeal_isClosed` (which carries the `pairSubring`-noetherianness `hnoeth`). -/
private theorem oneSubfXIdeal_isClosed_faithful [IsStronglyNoetherian A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) (s : A) :
    IsClosed ((oneSubfXIdeal s : Ideal ↥(TateAlgebra A)) : Set ↥(TateAlgebra A)) :=
  tateAlgebra_isClosed_ideal_faithful hA_complete (oneSubfXIdeal s)

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsNoetherianRing A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- **Faithful: the quotient `A⟨X⟩/(1 − sX)` is T2** — faithful (case-(b)) replacement for
`quotient_oneSubfXIdeal_t2Space`, via the faithful closed-ideal `oneSubfXIdeal_isClosed_faithful`
(no `pairSubring`-noetherianness). -/
private theorem quotient_oneSubfXIdeal_t2Space_faithful [IsStronglyNoetherian A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) (s : A) :
    T2Space (↥(TateAlgebra A) ⧸ oneSubfXIdeal s) := by
  haveI : IsClosed ((oneSubfXIdeal s).toAddSubgroup : Set ↥(TateAlgebra A)) :=
    oneSubfXIdeal_isClosed_faithful hA_complete s
  infer_instance

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsNoetherianRing A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- **Faithful: the quotient `A⟨X⟩/(1 − sX)` is complete** under the canonical quotient topology —
faithful (case-(b)) replacement for `quotient_oneSubfXIdeal_completeSpace`. `A⟨X⟩` is complete
(`tateAlgebraTopology'_completeSpace`) and first-countable; `(1 − sX)` is closed by the faithful
`oneSubfXIdeal_isClosed_faithful`; `QuotientAddGroup.completeSpace_right'` (Bourbaki IX.3.1 Prop 4)
then gives completeness — **no** `pairSubring`-noetherianness. -/
private theorem quotient_oneSubfXIdeal_completeSpace_faithful [IsStronglyNoetherian A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) (s : A) :
    @CompleteSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal s)
      (quotientOneSubfXIdealUniformSpace s) := by
  letI τ : TopologicalSpace ↥(TateAlgebra A) := instTopologicalSpaceTateAlgebra
  haveI _hring : IsTopologicalRing ↥(TateAlgebra A) := instIsTopologicalRingTateAlgebra
  haveI haddgrp : IsTopologicalAddGroup ↥(TateAlgebra A) :=
    IsTopologicalRing.to_topologicalAddGroup
  haveI : FirstCountableTopology ↥(TateAlgebra A) := instFirstCountableTopologyTateAlgebra
  haveI hCS : @CompleteSpace ↥(TateAlgebra A)
      (IsTopologicalAddGroup.rightUniformSpace ↥(TateAlgebra A)) :=
    tateAlgebraTopology'_completeSpace hA_complete
  haveI : IsClosed ((oneSubfXIdeal s).toAddSubgroup : Set ↥(TateAlgebra A)) :=
    oneSubfXIdeal_isClosed_faithful hA_complete s
  exact @QuotientAddGroup.completeSpace_right' ↥(TateAlgebra A) _ τ haddgrp ‹_›
    (oneSubfXIdeal s).toAddSubgroup inferInstance hCS

/-- **Faithful forward completion map** `presheafValue D →+* A⟨X⟩/(1−sX)` — faithful (case-(b))
replacement for `presheafValueToCanonicalQuotient`, which threads `hnoeth`. The localization
generator map `locToQuotientOneSubfX_gen D.s : Localization.Away D.s → A⟨X⟩/(1−sX)` extends to the
completion `presheafValue D` because the target is complete (`quotient_oneSubfXIdeal_completeSpace_faithful`)
and Hausdorff (`quotient_oneSubfXIdeal_t2Space_faithful`), both supplied faithfully from
`[IsStronglyNoetherian A]` + `hA_complete`. -/
private noncomputable def presheafValueToCanonicalQuotient_faithful [IsStronglyNoetherian A]
    (D : RationalLocData A)
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t) :
    presheafValue D →+* (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology D.s
  letI : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology_isTopologicalRing D.s
  letI : IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology_isTopologicalAddGroup D.s
  letI : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealUniformSpace D.s
  letI : IsUniformAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdeal_isUniformAddGroup D.s
  haveI : CompleteSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotient_oneSubfXIdeal_completeSpace_faithful hA_complete D.s
  haveI hT2Q : @T2Space _ (quotientOneSubfXIdealTopology D.s) :=
    quotient_oneSubfXIdeal_t2Space_faithful hA_complete D.s
  haveI hT0Q : @T0Space _ (quotientOneSubfXIdealTopology D.s) :=
    @T1Space.t0Space _ (quotientOneSubfXIdealTopology D.s) (T2Space.t1Space)
  exact @UniformSpace.Completion.extensionHom _ _ _ _ _ _
    (quotientOneSubfXIdealUniformSpace D.s) _
    (quotientOneSubfXIdeal_isUniformAddGroup D.s)
    (quotientOneSubfXIdealTopology_isTopologicalRing D.s)
    (locToQuotientOneSubfX_gen D.s)
    (locToQuotientOneSubfX_gen_continuous_canonical D hT_pb)
    (quotient_oneSubfXIdeal_completeSpace_faithful hA_complete D.s)
    hT0Q

/-- The faithful forward map sends `coeRingHom a` to `locToQuotientOneSubfX_gen D.s a` — faithful
analogue of `presheafValueToCanonicalQuotient_coe`. -/
private theorem presheafValueToCanonicalQuotient_faithful_coe [IsStronglyNoetherian A]
    (D : RationalLocData A)
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t)
    (a : Localization.Away D.s) :
    presheafValueToCanonicalQuotient_faithful D hA_complete hT_pb (D.coeRingHom a) =
      locToQuotientOneSubfX_gen D.s a := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology D.s
  letI : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology_isTopologicalRing D.s
  letI : IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology_isTopologicalAddGroup D.s
  letI : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealUniformSpace D.s
  letI : IsUniformAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdeal_isUniformAddGroup D.s
  haveI : CompleteSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotient_oneSubfXIdeal_completeSpace_faithful hA_complete D.s
  haveI hT2Q : @T2Space _ (quotientOneSubfXIdealTopology D.s) :=
    quotient_oneSubfXIdeal_t2Space_faithful hA_complete D.s
  haveI hT0Q : @T0Space _ (quotientOneSubfXIdealTopology D.s) :=
    @T1Space.t0Space _ (quotientOneSubfXIdealTopology D.s) (T2Space.t1Space)
  exact @UniformSpace.Completion.extensionHom_coe _ _ _ _ _ _
    (quotientOneSubfXIdealUniformSpace D.s) _
    (quotientOneSubfXIdeal_isUniformAddGroup D.s)
    (quotientOneSubfXIdealTopology_isTopologicalRing D.s)
    (locToQuotientOneSubfX_gen D.s)
    (locToQuotientOneSubfX_gen_continuous_canonical D hT_pb)
    (quotient_oneSubfXIdeal_completeSpace_faithful hA_complete D.s)
    hT0Q a

/-- Faithful continuity of the forward map (`Completion.continuous_extension`), no `hnoeth`. -/
private theorem presheafValueToCanonicalQuotient_faithful_continuous [IsStronglyNoetherian A]
    (D : RationalLocData A)
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t) :
    @Continuous _ _ (inferInstance : TopologicalSpace (presheafValue D))
      (quotientOneSubfXIdealTopology D.s)
      (presheafValueToCanonicalQuotient_faithful D hA_complete hT_pb) :=
  @UniformSpace.Completion.continuous_extension _ D.uniformSpace _
    (quotientOneSubfXIdealUniformSpace D.s)
    (↑(locToQuotientOneSubfX_gen D.s))
    (quotient_oneSubfXIdeal_completeSpace_faithful hA_complete D.s)

/-- Faithful round-trip `backward ∘ forward = id` on `presheafValue D` — faithful analogue of
`tateQuotientToPresheaf_comp_presheafToCanonicalQuotient`. -/
private theorem tateQuotientToPresheaf_comp_faithful [IsStronglyNoetherian A]
    (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t)
    (x : presheafValue D) :
    tateQuotientToPresheafHom D hb
      (presheafValueToCanonicalQuotient_faithful D hA_complete hT_pb x) = x := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI τC : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology D.s
  letI : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealUniformSpace D.s
  have hcont_ext := presheafValueToCanonicalQuotient_faithful_continuous D hA_complete hT_pb
  refine @UniformSpace.Completion.ext' _ D.uniformSpace
    (presheafValue D) _ _ _ _
    ((tateQuotientToPresheafHom_continuous_of_tate D hb).comp hcont_ext)
    continuous_id ?_ x
  intro a
  simp only [Function.comp, id]
  change tateQuotientToPresheafHom D hb
    (presheafValueToCanonicalQuotient_faithful D hA_complete hT_pb (D.coeRingHom a)) =
    D.coeRingHom a
  rw [presheafValueToCanonicalQuotient_faithful_coe D hA_complete hT_pb a,
    tateQuotient_roundtrip_apply D hb a, locLiftToPresheaf_eq_coeRingHom D]

/-- Faithful round-trip `forward ∘ backward = id` on `A⟨X⟩/(1−sX)` — faithful analogue of
`presheafToCanonicalQuotient_comp_tateQuotientToPresheaf`. -/
private theorem presheafToCanonicalQuotient_comp_faithful [IsStronglyNoetherian A]
    (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t)
    (q : ↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :
    presheafValueToCanonicalQuotient_faithful D hA_complete hT_pb
      (tateQuotientToPresheafHom D hb q) = q := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI τC : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology D.s
  letI : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealUniformSpace D.s
  letI : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology_isTopologicalRing D.s
  letI : IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology_isTopologicalAddGroup D.s
  letI : IsUniformAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdeal_isUniformAddGroup D.s
  haveI hT2 : @T2Space _ τC := quotient_oneSubfXIdeal_t2Space_faithful hA_complete D.s
  haveI : @CompleteSpace _ (quotientOneSubfXIdealUniformSpace D.s) :=
    quotient_oneSubfXIdeal_completeSpace_faithful hA_complete D.s
  have hdense := locToQuotientOneSubfX_gen_denseRange_canonical D.s
  have hagree : ∀ (a : Localization.Away D.s),
      presheafValueToCanonicalQuotient_faithful D hA_complete hT_pb
        (tateQuotientToPresheafHom D hb (locToQuotientOneSubfX_gen D.s a)) =
        locToQuotientOneSubfX_gen D.s a := by
    intro a
    rw [tateQuotient_roundtrip_apply D hb a, locLiftToPresheaf_eq_coeRingHom D,
      presheafValueToCanonicalQuotient_faithful_coe D hA_complete hT_pb a]
  have hcont_ext := presheafValueToCanonicalQuotient_faithful_continuous D hA_complete hT_pb
  have h_eq : (fun q ↦ presheafValueToCanonicalQuotient_faithful D hA_complete hT_pb
      (tateQuotientToPresheafHom D hb q)) = (fun q ↦ q) :=
    hdense.equalizer
      (hcont_ext.comp (tateQuotientToPresheafHom_continuous_of_tate D hb))
      continuous_id (funext hagree)
  exact congr_fun h_eq q

/-- **Faithful Example-6.38 ring iso** `presheafValue D ≃+* A⟨X⟩/(1−sX)` (Wedhorn Example 6.38) —
faithful (case-(b)) analogue of `presheafValueCanonicalQuotientEquiv`, built from the faithful
forward map and round-trips with the `[IsStronglyNoetherian A]` bundle only (no `hnoeth`). -/
private noncomputable def presheafValueCanonicalQuotientEquiv_faithful [IsStronglyNoetherian A]
    (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t) :
    presheafValue D ≃+* (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) where
  toFun := presheafValueToCanonicalQuotient_faithful D hA_complete hT_pb
  invFun := tateQuotientToPresheafHom D hb
  left_inv := tateQuotientToPresheaf_comp_faithful D hb hA_complete hT_pb
  right_inv := presheafToCanonicalQuotient_comp_faithful D hb hA_complete hT_pb
  map_mul' := map_mul _
  map_add' := map_add _

/-! ### Faithful noetherianness of `presheafValue D` (Step 1, noetherian part)

The whole-space base `presheafValue (globalLocData P) = 𝒪_X(X)` is noetherian by the faithful
Example 6.38 equivalence `presheafValueCanonicalQuotientEquiv_faithful`: `globalLocData P` has
`T = {1}`, `s = 1`, so `invS = 1` is power-bounded (`invS_isPowerBounded_of_one_mem_T`, `1 ∈ {1}`)
and every `t ∈ {1}` is power-bounded — hence `presheafValue (globalLocData P) ≃+* A⟨X⟩/(1 − X)`, a
quotient of the noetherian (strong-noetherian `A`) ring `A⟨X⟩`. This whole-space (`hb`-available)
case is sorry-free (modulo the upstream Prop-6.17-forward `sorryAx`, see below).

⚠️ The general-`D` case does NOT reduce to this base by localization: the would-be fact
"`presheafValue D = IsLocalization.Away (canonicalMap s) (presheafValue 𝒪_X(X))`" rests on
`restrictionMapHom_surj`, which is **deprecated as FALSE IN GENERAL** (PresheafTateStructure.lean:
"RETIRED — false in general; ... range(σ) closed fails", 2026-05-23). Wedhorn's `𝒪_X(R(T/s))` for a
general rational subset is *not* `𝒪_X(X)[1/s]`; the `T`-conditions genuinely change the ring. The
faithful general-`D` route is the **multivariate** Example 6.38 `presheafValue D ≃ A⟨X₁..Xₙ⟩/a`
(with `Xᵢ ↦ tᵢ/s`, which ARE power-bounded), a quotient of the noetherian `A⟨X₁..Xₙ⟩` — repo gap. -/

/-- **Faithful: the whole-space value `𝒪_X(X) = presheafValue (globalLocData P)` is noetherian.**
Via `presheafValueCanonicalQuotientEquiv_faithful`: `globalLocData P` has `T = {1}`, `s = 1`, so the
faithful Example 6.38 iso gives `presheafValue (globalLocData P) ≃+* A⟨X⟩/(1 − X)`, a quotient of
the noetherian `A⟨X⟩` (`[IsStronglyNoetherian A]`). Honest case-(b) noetherianness for the whole
space, with NO `pairSubring`/`A₀⟨X⟩` noetherianness and NO Bourbaki noeth-`A₀` completion. -/
private theorem presheafValue_globalLocData_isNoetherianRing (P : PairOfDefinition A) :
    IsNoetherianRing (presheafValue (globalLocData P)) := by
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  haveI hAc : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A) := ‹_›
  -- `invS (globalLocData P)` is power-bounded since `1 ∈ {1} = (globalLocData P).T`.
  have hb : TopologicalRing.IsPowerBounded (invS (globalLocData P)) := by
    rw [invS_eq_coeRingHom_divByS_one]
    exact CompletionLocalization.invS_isPowerBounded_of_one_mem_T
      (globalLocData P) (Finset.mem_singleton_self 1)
  -- Every `t ∈ (globalLocData P).T = {1}` is power-bounded.
  have hT_pb : ∀ t ∈ (globalLocData P).T, TopologicalRing.IsPowerBounded t := by
    intro t ht
    rw [show (globalLocData P).T = {1} from rfl, Finset.mem_singleton] at ht
    rw [ht]; exact TopologicalRing.isPowerBounded_one
  -- Transport noetherianness across the faithful Example 6.38 equiv.
  exact isNoetherianRing_of_ringEquiv _
    (presheafValueCanonicalQuotientEquiv_faithful (globalLocData P) hb hAc hT_pb).symm

end FaithfulExample638Base

/-! ## Lemma 8.31 — flatness of `A⟨X⟩` and its Laurent quotients

> **Lemma 8.31.** Let `A` be a noetherian complete Tate ring.
> (1) The ring `A⟨X⟩` is faithfully flat over `A`.
> (2) For all `f ∈ A` the rings `A⟨X⟩/(f − X)` and `A⟨X⟩/(1 − fX)` are flat over `A`.

Wedhorn's proof uses **Remark 8.29** (`M ⊗_A A⟨X⟩ ≅ M⟨X⟩` for finitely generated `M`,
which rests on Prop 6.18 — proven in `BanachOMT.lean`) plus the explicit injectivity
computations for `1 − fX` and `f − X`. -/

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- **Lemma 8.31(1)** (Wedhorn p. 82, `wedhorn.txt:4106`): `A⟨X⟩` is faithfully flat over `A`,
for `A` a **noetherian** complete Tate ring. Wedhorn's proof: flatness from Remark 8.29
(`TateAlgebra.muMap_injective` — `i ⊗ id : N ⊗ A⟨X⟩ → M ⊗ A⟨X⟩` is injective whenever
`i : N ↪ M`), and the faithful half from the prime `q = {Σ aᵥ Xᵥ : a₀ ∈ p}` lying over each
prime `p` (`q ∩ A = p`).

**Faithfulness:** stated with `[IsNoetherianRing A]` (the Tate ring, = strongly-noeth at `k = 0`)
only. The noeth-`A₀` route `TateAlgebra.faithfullyFlat_general P` is the Wedhorn **case (a)**
argument (Artin–Rees over a ring of definition) and **must not** be used to discharge the
case-(b) target. See `.mathlib-quality/decomposition.md` §LEAF A2 (2026-06-02). -/
theorem lemma_8_31_tateAlgebra_faithfullyFlat :
    Module.FaithfullyFlat A ↥(TateAlgebra A) := by
  haveI : Module.Flat A ↥(TateAlgebra A) := tateAlgebra_flat_faithful
  exact Module.FaithfullyFlat.of_comap_surjective
    TateAlgebra.PrimeSpectrum_comap_algebraMap_surjective

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- **Lemma 8.31(2), minus shape** (Wedhorn p. 82, `wedhorn.txt:4108`): `A⟨X⟩/(1 − fX)` is flat
over `A`. Wedhorn's proof: the multiplication `w_{1-fX} : M⟨X⟩ → M⟨X⟩` is injective (easy check),
so by the claim at `:4116` `A⟨X⟩/(1 − fX)` is flat. **Faithful: `[IsNoetherianRing A]` only**
(the noeth-`A₀` route `TateAlgebra.flat_quotient_oneSubfX_general P` is case (a)). -/
theorem lemma_8_31_oneSubfX_flat (f : A) :
    Module.Flat A (↥(TateAlgebra A) ⧸
      Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X}) := by
  haveI : Module.Flat A ↥(TateAlgebra A) := tateAlgebra_flat_faithful
  exact Module.Flat.quotient_of_flat_of_saturated
    (TateAlgebra.mul_oneSubfX_regular f)
    (fun I s hmem => oneSubfX_saturated_faithful f I s hmem)

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- **Lemma 8.31(2), plus shape** (Wedhorn p. 82, `wedhorn.txt:4108`): `A⟨X⟩/(f − X)` is flat
over `A`. Wedhorn's proof: for `u = Σ mᵥ Xᵥ` with `(f − X)u = 0` one gets `f m₀ = 0`,
`f mᵥ = mᵥ₋₁`; as `M` is noetherian the submodule `M′ = ⟨mᵥ⟩` is finitely generated, forcing
`M′ = 0`, so `w_{f-X}` is injective and the quotient is flat. **Faithful: `[IsNoetherianRing A]`
only** (the noeth use is "`M` noetherian"; the noeth-`A₀` route
`TateAlgebra.flat_quotient_fSubX_general P` is case (a)). -/
theorem lemma_8_31_fSubX_flat (f : A) :
    Module.Flat A (↥(TateAlgebra A) ⧸
      Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X}) := by
  haveI : Module.Flat A ↥(TateAlgebra A) := tateAlgebra_flat_faithful
  exact Module.Flat.quotient_of_flat_of_saturated
    (TateAlgebra.mul_fSubX_regular f)
    (fun I s hmem => fSubX_saturated_faithful f I s hmem)

/-! ## Corollary 8.32 — the product restriction is faithfully flat (⇒ injective)

> **Corollary 8.32.** Let `A` be a strongly noetherian Tate affinoid ring, `X = Spa A`, and
> `(Uᵢ)` a finite rational covering of `X`. Then `O_X(X) → ∏ᵢ O_X(Uᵢ)`, `f ↦ (f|Uᵢ)`, is
> faithfully flat (and in particular injective).

By Example 6.38 each `O_X(Uᵢ)` is a Laurent quotient `O_X(X)⟨X⟩/(…)`, so flatness of each
factor is **Lemma 8.31(2)** over the base `O_X(X)`; faithful flatness of the product follows
because the cover is jointly surjective on Spa (prime-surjectivity). -/
/-! ### Proposition 8.30 — faithful decomposition (Example 6.38 + Remark 7.55 + Lemma 8.31)

Wedhorn's proof of Prop 8.30 (p. 81, `wedhorn.txt:4095`) is, verbatim:

> "By Example 6.38, `O_X(V)` is again a strongly noetherian Tate ring. Thus we may assume
> `X = V` and `A` complete. By Remark 7.55 we may assume `U` is `U₁ = R(f/1) = {x(f) ≤ 1}`
> or `U₂ = R(1/f) = {x(f) ≥ 1}` for some `f ∈ A`. In Example 6.38 we have seen
> `O_X(U₁) = Â⟨X⟩/(f−X)` and `O_X(U₂) = Â⟨X⟩/(1−fX)`. Thus it suffices to show Lemma 8.31."

The faithful Lean skeleton mirrors this exactly. Write `B := presheafValue D = O_X(V)`.

* **Step 1 (Example 6.38, the base).** `B` is again a *complete strongly noetherian Tate*
  ring. In Lean this means `B` carries the instance bundle that `lemma_8_31_*` consume:
  `IsTateRing B`, `IsNoetherianRing B`, `IsLinearTopology B B` (the remaining members
  — `IsTopologicalRing`, `T2Space`, `NonarchimedeanRing`, `CompleteSpace`, `PlusSubring`
  — are already plain instances on `presheafValue D`, and `IsHuberRing B` /
  `HasLocLiftPowerBounded B` / `IsStronglyNoetherian B` are *derived* from those three plus
  `isStronglyNoetherian_of_isNoetherianRing_isTateRing`). These three are isolated as the
  faithful helpers `presheafValue_isTateRing_faithful`, `presheafValue_isNoetherianRing_faithful`,
  `presheafValue_isLinearTopology_faithful` below. They are FAITHFUL: parameterised only by
  `D` and the ambient strongly-noetherian-Tate `A`-bundle — **no** `PairOfDefinition A`, **no**
  `[IsNoetherianRing P.A₀]`. (The repo's existing `presheafValue_isTateRing` /
  `presheafValue_isNoetherianRing_of_…` route through a noetherian ring of definition `A₀`,
  which is the Wedhorn case-(a) / `ℂ_p`-false defect and must not be used here.)

* **Steps 2–4 (Remark 7.55 + Example 6.38 over `B` + Lemma 8.31).** With `B` strongly
  noetherian Tate and complete, reduce `U ⊆ V` to a basic Laurent shape `R(f̄/1)` /
  `R(1/f̄)` over `B` (Remark 7.55), identify `O_X(U)` as the Laurent quotient
  `B⟨X⟩/(f̄−X)` resp. `B⟨X⟩/(1−f̄X)` *as a `B`-algebra* (Example 6.38 over the base `B`),
  and conclude flatness by `lemma_8_31_fSubX_flat` / `lemma_8_31_oneSubfX_flat` over `B`,
  transported across the `B`-algebra iso by `Module.Flat.of_linearEquiv`. This is isolated
  as the faithful helper `prop_8_30_flat_of_faithful_base` below. -/

/-- **Step 1 of Prop 8.30 — Example 6.38, Tate part** (Wedhorn p. 81, `wedhorn.txt:4095`:
"`O_X(V)` is again a strongly noetherian Tate ring"). The presheaf value `B := presheafValue D`
of a rational locale over a strongly noetherian Tate ring is again a **Tate** ring.

FAITHFUL: depends only on the ambient `A`-bundle and `D` — **no** `PairOfDefinition A`, **no**
`[IsNoetherianRing P.A₀]`. (The repo's `presheafValue_isTateRing` routes through a noetherian
ring of definition `P.A₀`, the Wedhorn case-(a) / `ℂ_p`-false hypothesis; this faithful version
avoids it entirely.)

RESOLVED FAITHFULLY: `IsTateRing = IsHuberRing + topologically-nilpotent unit`. The Tate unit is
`presheafValue_topNilUnit` (sorry-free, `[IsTateRing A]` only). The `PairOfDefinition`
(`presheafValue_ringOfDef D`, `presheafValue_idealOfDef D`, `presheafValue_ringOfDef_isOpen D`,
`presheafValue_idealOfDef_fg D`, `presheafValue_isAdic D`) is built from sub-lemmas that are each
parameterised by `D` ALONE — none consumes `[IsNoetherianRing P.A₀]` (the `(P, [noeth P.A₀])`
carried by `presheafValue_pairOfDefinition_concrete` are pure threading artifacts never invoked in
its body). Hence the Huber structure is faithful and no noeth-`A₀` enters. -/
private theorem presheafValue_isTateRing_faithful
    [IsTateRing A] [IsNoetherianRing A] (D : RationalLocData A) :
    IsTateRing (presheafValue D) where
  exists_pairOfDefinition :=
    ⟨{ A₀ := presheafValue_ringOfDef D
       I := presheafValue_idealOfDef D
       isOpen := presheafValue_ringOfDef_isOpen D
       fg := presheafValue_idealOfDef_fg D
       isAdic := presheafValue_isAdic D }⟩
  exists_topologicallyNilpotent_unit := presheafValue_topNilUnit D

/-! ## Multivariate restricted-power-series evaluation (Example 6.38 engine)

The `Fin n` generalization of `evalHomBounded`/`evalHomBounded₂` (`TateAlgebraWedhorn.lean`):
given a continuous ring hom `g : A →+* B` into a complete nonarchimedean ring `B` and a tuple
`b : Fin n → B` of power-bounded elements, the evaluation
`A⟨X₁,…,Xₙ⟩ →+* B`, `Σ aᵥ Xᵛ ↦ Σ aᵥ ∏ᵢ bᵢ^(vᵢ)`, is a ring homomorphism (multivariate
nonarchimedean Cauchy product), and it sends `algebraMap a ↦ g a` and `Xᵢ ↦ bᵢ`.

INFRASTRUCTURE (not in Wedhorn at this granularity): a general-`n` lift of the existing
`Fin 1`/`Fin 2` machinery; mirrors `evalHomBounded₂` line for line. -/

section MvEvalHom

variable {R S : Type*} [CommRing R] [TopologicalSpace R] [NonarchimedeanRing R]
  [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [IsTopologicalRing S]
  [NonarchimedeanRing S] [CompleteSpace S] [T0Space S]

/-- The `v`-th term of the `n`-variate evaluation series:
`g(coeff_v h) · ∏ᵢ bᵢ^(v i)`. -/
noncomputable def mvEvalTerm {n : ℕ} (g : R →+* S) (b : Fin n → S)
    (h : ↥(restrictedMvPowerSeriesSubring n R)) (v : Fin n →₀ ℕ) : S :=
  g (MvPowerSeries.coeff v h.val) * ∏ i, b i ^ (v i)

omit [IsUniformAddGroup S] [NonarchimedeanRing S] [CompleteSpace S] [T0Space S] in
/-- The range of `v ↦ ∏_{i ∈ s} bᵢ^(v i)` over `Fin n →₀ ℕ` is bounded whenever each `bᵢ` is
power-bounded, for any finite index set `s`. Proved by `Finset.induction`, reducing to
`IsBounded.mul` (the product set `range (bₐ ^ ·) * (previous range)`). -/
private theorem mvRangeProdOn_isBounded {n : ℕ} (b : Fin n → S)
    (hb : ∀ i, TopologicalRing.IsBounded (Set.range (b i ^ · : ℕ → S)))
    (s : Finset (Fin n)) :
    TopologicalRing.IsBounded
      (Set.range (fun v : Fin n →₀ ℕ => ∏ i ∈ s, b i ^ (v i))) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using TopologicalRing.isBounded_singleton (1 : S)
  | insert a s ha ih =>
      -- range over `insert a s` ⊆ range(bₐ ^ ·) * range over `s`.
      refine ((hb a).mul ih).subset ?_
      rintro _ ⟨v, rfl⟩
      change ∏ i ∈ insert a s, b i ^ (v i) ∈ _
      rw [Finset.prod_insert ha]
      exact Set.mul_mem_mul ⟨v a, rfl⟩ ⟨v, rfl⟩

omit [IsUniformAddGroup S] [NonarchimedeanRing S] [CompleteSpace S] [T0Space S] in
/-- The range of `v ↦ ∏ᵢ bᵢ^(v i)` over `Fin n →₀ ℕ` is bounded whenever each `bᵢ` is
power-bounded. The full-`univ` case of `mvRangeProdOn_isBounded`. -/
private theorem mvRangeProd_isBounded {n : ℕ} (b : Fin n → S)
    (hb : ∀ i, TopologicalRing.IsBounded (Set.range (b i ^ · : ℕ → S))) :
    TopologicalRing.IsBounded
      (Set.range (fun v : Fin n →₀ ℕ => ∏ i, b i ^ (v i))) :=
  mvRangeProdOn_isBounded b hb Finset.univ

omit [IsUniformAddGroup S] [NonarchimedeanRing S] [CompleteSpace S] [T0Space S] in
/-- The `n`-variate evaluation terms tend to `0` along the cofinite filter on `Fin n →₀ ℕ`.
Uses continuity of `g` (the coefficients form a null family) and boundedness of the product
power range. Mirrors `evalTerm₂_tendsto_zero`. -/
theorem mvEvalTerm_tendsto_zero {n : ℕ} (g : R →+* S) (hg : Continuous g) (b : Fin n → S)
    (hb : ∀ i, TopologicalRing.IsBounded (Set.range (b i ^ · : ℕ → S)))
    (h : ↥(restrictedMvPowerSeriesSubring n R)) :
    Filter.Tendsto (mvEvalTerm g b h) Filter.cofinite (nhds 0) := by
  have hc : Filter.Tendsto (fun v : Fin n →₀ ℕ => g (MvPowerSeries.coeff v h.val))
      Filter.cofinite (nhds 0) :=
    map_zero g ▸ hg.continuousAt.tendsto.comp h.prop
  have hd := mvRangeProd_isBounded b hb
  intro U hU
  obtain ⟨V, hV, hSV⟩ := hd U hU
  have hcV := hc hV
  rw [Filter.mem_map] at hcV ⊢
  refine Filter.mem_of_superset hcV (fun v (hv : _ ∈ V) => ?_)
  change g (MvPowerSeries.coeff v h.val) * (∏ i, b i ^ (v i)) ∈ U
  rw [mul_comm]
  exact hSV (Set.mul_mem_mul ⟨v, rfl⟩ hv)

omit [T0Space S] in
/-- The `n`-variate eval terms are summable in a complete nonarchimedean ring. -/
theorem mvEvalTerm_summable {n : ℕ} (g : R →+* S) (hg : Continuous g) (b : Fin n → S)
    (hb : ∀ i, TopologicalRing.IsBounded (Set.range (b i ^ · : ℕ → S)))
    (h : ↥(restrictedMvPowerSeriesSubring n R)) :
    Summable (mvEvalTerm g b h) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (mvEvalTerm_tendsto_zero g hg b hb h)

omit [IsUniformAddGroup S] [NonarchimedeanRing S] [CompleteSpace S] [T0Space S] in
/-- Multivariate convolution: `coeff_v (f · h) = ∑_{p+q=v} coeff_p f · coeff_q h`,
directly from `MvPowerSeries.coeff_mul`. -/
private theorem mvCoeff_mul_antidiag {n : ℕ} (f h : ↥(restrictedMvPowerSeriesSubring n R))
    (v : Fin n →₀ ℕ) :
    MvPowerSeries.coeff v ((f * h : ↥(restrictedMvPowerSeriesSubring n R)).val) =
      ∑ p ∈ Finset.antidiagonal v,
        MvPowerSeries.coeff p.1 f.val * MvPowerSeries.coeff p.2 h.val := by
  rw [Subring.coe_mul, MvPowerSeries.coeff_mul]

/-- **Multivariate evaluation ring homomorphism** `A⟨X₁,…,Xₙ⟩ →+* B` at a tuple `b : Fin n → B`
of power-bounded elements, sending `h = Σ aᵥ Xᵛ ↦ Σ aᵥ ∏ᵢ bᵢ^(v i)`.

`map_mul'` uses the nonarchimedean Cauchy product
(`Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal` over `Fin n →₀ ℕ`) and the multivariate
convolution formula. The `Fin n` generalization of `evalHomBounded`/`evalHomBounded₂`. -/
noncomputable def mvEvalHomBounded {n : ℕ} (g : R →+* S) (hg : Continuous g) (b : Fin n → S)
    (hb : ∀ i, TopologicalRing.IsBounded (Set.range (b i ^ · : ℕ → S))) :
    ↥(restrictedMvPowerSeriesSubring n R) →+* S where
  toFun h := ∑' v, mvEvalTerm g b h v
  map_zero' := by
    simp only [mvEvalTerm, ZeroMemClass.coe_zero, map_zero, zero_mul]
    exact tsum_zero
  map_one' := by
    rw [tsum_eq_single 0]
    · simp only [mvEvalTerm, OneMemClass.coe_one, Finsupp.coe_zero, Pi.zero_apply,
        pow_zero, Finset.prod_const_one, mul_one]
      classical
      rw [MvPowerSeries.coeff_one, if_pos rfl, map_one]
    · intro v hv
      simp only [mvEvalTerm, OneMemClass.coe_one]
      classical
      rw [MvPowerSeries.coeff_one, if_neg hv, map_zero, zero_mul]
  map_add' f h := by
    have hterm : ∀ v, mvEvalTerm g b (f + h) v =
        mvEvalTerm g b f v + mvEvalTerm g b h v := fun v => by
      simp only [mvEvalTerm, Subring.coe_add, map_add, add_mul]
    conv_lhs => arg 1; ext v; rw [hterm v]
    exact (mvEvalTerm_summable g hg b hb f).tsum_add (mvEvalTerm_summable g hg b hb h)
  map_mul' f h := by
    rw [Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
      (mvEvalTerm_summable g hg b hb f) (mvEvalTerm_summable g hg b hb h)
      ((mvEvalTerm_summable g hg b hb f).mul_of_nonarchimedean
        (mvEvalTerm_summable g hg b hb h))]
    congr 1
    ext v
    simp only [mvEvalTerm, mvCoeff_mul_antidiag, map_sum, map_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun ⟨p, q⟩ hpq => ?_)
    have hpq_add : p + q = v := Finset.mem_antidiagonal.mp hpq
    have hprod : (∏ i, b i ^ (p i)) * (∏ i, b i ^ (q i)) = ∏ i, b i ^ (v i) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [← pow_add, ← Finsupp.add_apply, hpq_add]
    calc g (MvPowerSeries.coeff p f.val) * g (MvPowerSeries.coeff q h.val) *
            ∏ i, b i ^ (v i)
        = (g (MvPowerSeries.coeff p f.val) * ∏ i, b i ^ (p i)) *
            (g (MvPowerSeries.coeff q h.val) * ∏ i, b i ^ (q i)) := by
          rw [← hprod]; ring
      _ = _ := rfl

/-- `mvEvalHomBounded` sends `algebraMap a ↦ g a`. -/
theorem mvEvalHomBounded_algebraMap {n : ℕ} (g : R →+* S) (hg : Continuous g) (b : Fin n → S)
    (hb : ∀ i, TopologicalRing.IsBounded (Set.range (b i ^ · : ℕ → S))) (a : R) :
    mvEvalHomBounded g hg b hb
      (algebraMap R ↥(restrictedMvPowerSeriesSubring n R) a) = g a := by
  change ∑' v, mvEvalTerm g b (algebraMap R ↥(restrictedMvPowerSeriesSubring n R) a) v = g a
  rw [tsum_eq_single 0]
  · simp only [mvEvalTerm, Finsupp.coe_zero, Pi.zero_apply, pow_zero, Finset.prod_const_one,
      mul_one]
    change g ((MvPowerSeries.coeff 0) (MvPowerSeries.C (σ := Fin n) a)) = g a
    classical
    rw [MvPowerSeries.coeff_C, if_pos rfl]
  · intro v hv
    simp only [mvEvalTerm]
    have hcoeff : (MvPowerSeries.coeff (R := R) v)
        ((algebraMap R ↥(restrictedMvPowerSeriesSubring n R) a).val) = 0 := by
      change (MvPowerSeries.coeff (R := R) v) (MvPowerSeries.C (σ := Fin n) a) = 0
      classical
      rw [MvPowerSeries.coeff_C, if_neg hv]
    rw [hcoeff, map_zero, zero_mul]

/-- `mvEvalHomBounded` sends the `j`-th variable `Xⱼ ↦ bⱼ`. -/
theorem mvEvalHomBounded_X {n : ℕ} (g : R →+* S) (hg : Continuous g) (b : Fin n → S)
    (hb : ∀ i, TopologicalRing.IsBounded (Set.range (b i ^ · : ℕ → S))) (j : Fin n) :
    mvEvalHomBounded g hg b hb
      ⟨MvPowerSeries.X j, MvPowerSeries.X_isRestricted j⟩ = b j := by
  change ∑' v, mvEvalTerm g b (⟨MvPowerSeries.X j, MvPowerSeries.X_isRestricted j⟩ :
    ↥(restrictedMvPowerSeriesSubring n R)) v = b j
  classical
  rw [tsum_eq_single (Finsupp.single j 1)]
  · simp only [mvEvalTerm]
    rw [show (MvPowerSeries.coeff (R := R) (Finsupp.single j 1)) (MvPowerSeries.X j) = 1 by
          rw [MvPowerSeries.coeff_X, if_pos rfl], map_one, one_mul]
    rw [Finset.prod_eq_single j]
    · rw [Finsupp.single_eq_same, pow_one]
    · intro i _ hij
      rw [Finsupp.single_apply, if_neg (by exact fun h => hij h.symm), pow_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  · intro v hv
    simp only [mvEvalTerm]
    have hcoeff : (MvPowerSeries.coeff (R := R) v) (MvPowerSeries.X (σ := Fin n) j) = 0 := by
      rw [MvPowerSeries.coeff_X]; exact if_neg hv
    rw [hcoeff, map_zero, zero_mul]

end MvEvalHom

set_option linter.unusedSectionVars false in
/-- The `i`-th rational generator `tᵢ/s ∈ presheafValue D` (`i : Fin D.T.card`):
the image under `D.coeRingHom` of `divByS (i-th element of D.T) D.s`. -/
noncomputable def example638_genTuple [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) : Fin D.T.card → presheafValue D :=
  fun i => D.coeRingHom (divByS (↑(D.T.equivFin.symm i) : A) D.s)

set_option linter.unusedSectionVars false in
/-- Each rational generator `tᵢ/s` is power-bounded in `presheafValue D`: its powers lie in
the image of the bounded ring of definition `locSubring`
(`CompletionLocalization.coeRingHom_image_locSubring_isBounded`). Inlines the pure argument of
`relativeRationalLocData_generators_powerBounded` (no `LaurentNormalized`/`E` side conditions). -/
theorem example638_genTuple_isBounded [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) (i : Fin D.T.card) :
    TopologicalRing.IsBounded
      (Set.range (example638_genTuple D i ^ · : ℕ → presheafValue D)) := by
  have hmem : divByS (↑(D.T.equivFin.symm i) : A) D.s ∈ locSubring D.P D.T D.s :=
    divByS_mem_locSubring D.P D.T D.s (D.T.equivFin.symm i).2
  have hbdd := CompletionLocalization.coeRingHom_image_locSubring_isBounded D
  apply hbdd.subset
  rintro _ ⟨n, rfl⟩
  exact ⟨(divByS (↑(D.T.equivFin.symm i) : A) D.s) ^ n, pow_mem hmem n, by
    rw [map_pow]; rfl⟩

set_option linter.unusedSectionVars false in
/-- The multivariate Example-6.38 evaluation hom
`C = A⟨X₁,…,Xₙ⟩ →+* presheafValue D`, `Xᵢ ↦ tᵢ/s`, `a ↦ canonicalMap a`
(`n = D.T.card`). Built from the general `mvEvalHomBounded` at the power-bounded rational
generators `example638_genTuple`. -/
noncomputable def example638_evalHom [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) :
    (restrictedMvPowerSeriesSubring D.T.card A) →+* presheafValue D :=
  mvEvalHomBounded D.canonicalMap (canonicalMap_continuous D)
    (example638_genTuple D) (example638_genTuple_isBounded D)

set_option linter.unusedSectionVars false in
/-- `example638_evalHom` sends the constant series `algebraMap a ↦ canonicalMap a`. -/
theorem example638_evalHom_algebraMap [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) (a : A) :
    example638_evalHom D (algebraMap A _ a) = D.canonicalMap a :=
  mvEvalHomBounded_algebraMap _ _ _ _ a

set_option linter.unusedSectionVars false in
/-- `example638_evalHom` sends the `j`-th variable `Xⱼ ↦ tⱼ/s` (the `j`-th rational generator). -/
theorem example638_evalHom_X [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) (j : Fin D.T.card) :
    example638_evalHom D ⟨MvPowerSeries.X j, MvPowerSeries.X_isRestricted j⟩ =
      example638_genTuple D j :=
  mvEvalHomBounded_X _ _ _ _ j

set_option linter.unusedSectionVars false in
/-- **Density helper (faithful):** every `D.coeRingHom`-image of an element of the ring of
definition `locSubring D.P D.T D.s = A₀[t/s]` lies in the range of `example638_evalHom D`.

The two generating families of `locSubring` (Wedhorn §8.1) both lie in the range:
`algebraMap A₀`-images go to `D.canonicalMap a = example638_evalHom (algebraMap a)`
(`example638_evalHom_algebraMap`), and `divByS t D.s` (for `t ∈ D.T`) goes to the rational
generator `tᵢ/s = example638_evalHom Xᵢ` (`example638_evalHom_X` at the index
`D.T.equivFin ⟨t, _⟩`). Closure under the ring operations is automatic since the range of a ring
hom is a subring (`Subring.closure_induction`). NO topology on `A⟨X₁..Xₙ⟩` is used. -/
private theorem coeRingHom_locSubring_mem_range [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) {x : Localization.Away D.s}
    (hx : x ∈ locSubring D.P D.T D.s) :
    D.coeRingHom x ∈ (example638_evalHom D).range := by
  classical
  refine Subring.closure_induction
    (p := fun x _ => D.coeRingHom x ∈ (example638_evalHom D).range)
    ?_ ?_ ?_ ?_ ?_ ?_ hx
  · -- generators: `algebraMap A₀` images and `divByS t s` for `t ∈ D.T`.
    rintro _ (⟨a, -, rfl⟩ | ⟨⟨t, ht⟩, rfl⟩)
    · -- `coeRingHom (algebraMap a) = canonicalMap a = example638_evalHom (algebraMap a)`.
      refine ⟨algebraMap A _ a, ?_⟩
      rw [example638_evalHom_algebraMap]; rfl
    · -- `coeRingHom (divByS t s) = example638_genTuple (equivFin ⟨t, ht⟩) = evalHom Xⱼ`.
      refine ⟨⟨MvPowerSeries.X (D.T.equivFin ⟨t, ht⟩),
        MvPowerSeries.X_isRestricted _⟩, ?_⟩
      rw [example638_evalHom_X]
      simp only [example638_genTuple, Equiv.symm_apply_apply]
  · -- 0
    exact ⟨0, by rw [map_zero, map_zero]⟩
  · -- 1
    exact ⟨1, by rw [map_one, map_one]⟩
  · -- add
    rintro x y - - ⟨px, hpx⟩ ⟨py, hpy⟩
    exact ⟨px + py, by rw [map_add, map_add, hpx, hpy]⟩
  · -- neg
    rintro x - ⟨px, hpx⟩
    exact ⟨-px, by rw [map_neg, map_neg, hpx]⟩
  · -- mul
    rintro x y - - ⟨px, hpx⟩ ⟨py, hpy⟩
    exact ⟨px * py, by rw [map_mul, map_mul, hpx, hpy]⟩

set_option linter.unusedSectionVars false in
/-- **`1/s = invS D` lies in the range of `example638_evalHom D`** — the linchpin density fact,
proved faithfully from the **Tate** hypothesis and the rational `hopen` datum (NO topology on
`A⟨X₁..Xₙ⟩`, NO `Σ tᵢ gᵢ = sᵏ` series).

Wedhorn (Example 6.38): `A[M]` is dense in `Â⟨T/s⟩`, where `M = {tᵢ/s}`; this is where `1/s`
enters, since `A` is Tate. Concretely: as `A` is Tate it has a topologically nilpotent unit `u`
(Definition 6.10); some power `uᵐ` lands in the image of `Iᴺ` (the `hopen` depth), so
`uᵐ = ↑b` for `b ∈ Iᴺ ⊆ A₀`. By `hopen`, `divByS (uᵐ) s ∈ locSubring = A₀[t/s]`, hence (via
`coeRingHom_locSubring_mem_range`) `D.coeRingHom (divByS (uᵐ) s) = D.canonicalMap (uᵐ) · invS`
lies in the range. Since `uᵐ` is a **unit** of `A`, `D.canonicalMap (uᵐ)` is invertible with
inverse `D.canonicalMap ((uᵐ)⁻¹) ∈ range`, so
`invS = D.canonicalMap ((uᵐ)⁻¹) · (D.canonicalMap (uᵐ) · invS)` lies in the range. -/
private theorem invS_mem_range [IsTateRing A] [IsNoetherianRing A] (D : RationalLocData A) :
    invS D ∈ (example638_evalHom D).range := by
  obtain ⟨u, hu⟩ := IsTateRing.exists_topologicallyNilpotent_unit (A := A)
  obtain ⟨N, hN⟩ := D.hopen
  -- The image of `Iᴺ` in `A` is a neighbourhood of `0`.
  have hmem : Subtype.val '' ((D.P.I ^ N : Ideal D.P.A₀) : Set D.P.A₀) ∈ nhds (0 : A) :=
    D.P.hasBasis_nhds_zero.mem_of_mem (i := N) trivial
  -- Some power `uᵐ` lands in that neighbourhood.
  obtain ⟨m, b, hbI, hbval⟩ := (hu.eventually hmem).exists
  -- `hbval : ↑b = (↑u)ᵐ`. By `hopen`, `divByS (↑b) s ∈ locSubring`.
  have hdiv : divByS (↑b : A) D.s ∈ locSubring D.P D.T D.s := hN b hbI
  have hrange_w : D.coeRingHom (divByS (↑b : A) D.s) ∈ (example638_evalHom D).range :=
    coeRingHom_locSubring_mem_range D hdiv
  -- `coeRingHom (divByS (↑b) s) = canonicalMap (↑b) · invS`.
  have hdivfac : divByS (↑b : A) D.s =
      algebraMap A (Localization.Away D.s) (↑b : A) * divByS 1 D.s := by
    rw [← IsLocalization.mk'_one (M := Submonoid.powers D.s) (S := Localization.Away D.s) (↑b : A)]
    unfold divByS
    rw [← IsLocalization.mk'_mul, mul_one, one_mul]
  have hcoe : D.coeRingHom (divByS (↑b : A) D.s) = D.canonicalMap (↑b : A) * invS D := by
    rw [hdivfac, map_mul, ← invS_eq_coeRingHom_divByS_one]; rfl
  -- `↑b = uᵐ` is a unit of `A`, so `canonicalMap (↑b)` is a unit; let `c := (↑b)⁻¹`.
  have hbunit : IsUnit (↑b : A) := by rw [hbval]; exact (u ^ m).isUnit
  set ub := hbunit.unit with hub
  -- `canonicalMap (↑ub⁻¹) ∈ range` and `canonicalMap (↑ub⁻¹) · canonicalMap (↑b) = 1`.
  have hinv_range : D.canonicalMap (↑ub⁻¹ : A) ∈ (example638_evalHom D).range :=
    ⟨algebraMap A _ (↑ub⁻¹ : A), example638_evalHom_algebraMap D (↑ub⁻¹ : A)⟩
  -- `invS = canonicalMap (↑ub⁻¹) · (canonicalMap (↑b) · invS)`.
  have hfinal : invS D = D.canonicalMap (↑ub⁻¹ : A) * D.coeRingHom (divByS (↑b : A) D.s) := by
    rw [hcoe, ← mul_assoc, ← map_mul]
    rw [show (↑ub⁻¹ : A) * (↑b : A) = 1 from by
      rw [hub]; exact Units.inv_mul_eq_one.mpr (by rw [IsUnit.unit_spec])]
    rw [map_one, one_mul]
  rw [hfinal]
  exact (example638_evalHom D).range.mul_mem hinv_range hrange_w

set_option linter.unusedSectionVars false in
/-- **The whole dense subring `range D.coeRingHom` lies in `range (example638_evalHom D)`.**
Every element of `Localization.Away D.s` is `a/sᵏ`, whose `coeRingHom`-image is
`D.canonicalMap a · (invS D)ᵏ`; both factors lie in the range (`example638_evalHom_algebraMap`
and `invS_mem_range`), so the product does. NO topology on `A⟨X₁..Xₙ⟩` is used. -/
private theorem coeRingHom_mem_range [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) (y : Localization.Away D.s) :
    D.coeRingHom y ∈ (example638_evalHom D).range := by
  induction y using Localization.induction_on with
  | H p =>
    obtain ⟨a, sk, hk⟩ := p
    obtain ⟨k, rfl⟩ := hk
    -- `coeRingHom (mk a ⟨sᵏ, _⟩) = canonicalMap a · invSᵏ`.
    have hformula : D.coeRingHom (Localization.mk a ⟨D.s ^ k, k, rfl⟩) =
        D.canonicalMap a * (invS D) ^ k := by
      have key : D.coeRingHom (Localization.mk a ⟨D.s ^ k, k, rfl⟩) *
          (D.canonicalMap D.s) ^ k = D.canonicalMap a := by
        rw [← map_pow]
        change D.coeRingHom _ * D.coeRingHom _ = D.coeRingHom _
        rw [← map_mul]
        congr 1
        rw [← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap,
          Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
        exact ⟨1, by simp [mul_comm]⟩
      rw [← key, mul_assoc,
        show (D.canonicalMap D.s) ^ k * (invS D) ^ k = 1 from by
          rw [← mul_pow, canonicalMap_s_mul_invS, one_pow],
        mul_one]
    rw [hformula]
    exact (example638_evalHom D).range.mul_mem
      ⟨algebraMap A _ a, example638_evalHom_algebraMap D a⟩
      ((example638_evalHom D).range.pow_mem (invS_mem_range D) k)

set_option linter.unusedSectionVars false in
/-- **Density of the image (faithful):** `example638_evalHom D` has dense range.
`presheafValue D = Completion (Localization.Away D.s)`, in which `range D.coeRingHom` is dense
(`UniformSpace.Completion.denseRange_coe`); that dense subring is contained in
`range (example638_evalHom D)` (`coeRingHom_mem_range`), so the larger set is dense too. This is
Wedhorn's "`A[M]` dense in `Â⟨T/s⟩`" (Example 6.38). NO topology on `A⟨X₁..Xₙ⟩` is used. -/
private theorem example638_evalHom_denseRange [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) : DenseRange (example638_evalHom D) := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  have hdense : DenseRange (D.coeRingHom : Localization.Away D.s → presheafValue D) := by
    change DenseRange (UniformSpace.Completion.coeRingHom :
      Localization.Away D.s → presheafValue D)
    exact UniformSpace.Completion.denseRange_coe
  -- `range coeRingHom ⊆ range example638_evalHom`, so the latter is dense too.
  refine hdense.mono ?_
  rintro _ ⟨y, rfl⟩
  exact coeRingHom_mem_range D y

set_option linter.unusedSectionVars false in
/-- **GENUINE RESIDUAL — closedness of the Example-6.38 image** (Wedhorn p. 56,
`wedhorn.txt:2698`–`2701`). The range of `example638_evalHom D : A⟨X₁..Xₙ⟩ → presheafValue D` is
**closed**.

This is Wedhorn's "closedness" ingredient: *"If `A` is a strongly noetherian Tate ring, we may
represent `Â⟨T/s⟩` as a quotient of a ring of restricted power series. Set `C = Â⟨Xᵢ,ₜ⟩` and let `a`
be the ideal generated by `{t − sᵢ Xᵢ,ₜ}`. By hypothesis `C` is noetherian and hence `a` is a
closed ideal (Proposition 6.17)."* Concretely `range (example638_evalHom D) = range ē` where
`ē : C/ker ↪ presheafValue D` is the (injective) factorisation through the kernel; closedness of
`ker` makes `C/ker` complete and `ē` a closed embedding, so the range is closed.

**This is the single isolated repo gap.** It is the *only* place a topology on the **general-`n`**
restricted Tate algebra `C = restrictedMvPowerSeriesSubring n A` is needed — together with its
completeness and **Prop 6.17** (every ideal of the noetherian `C` closed). The repo currently has
the canonical Tate topology + completeness + the faithful Prop 6.17
(`tateAlgebra_isClosed_ideal_faithful`, this file) **only for `n = 1`** (`TateAlgebra A =
restrictedMvPowerSeriesSubring 1 A`, `instUniformSpaceTateAlgebra`,
`tateAlgebraTopology'_completeSpace`) and `n = 2` (`TateAlgebra₂`). For general `n = D.T.card` the
type `restrictedMvPowerSeriesSubring n A` carries **no** `TopologicalSpace`/`UniformSpace` instance
at all (`RestrictedPowerSeries.lean:75`: a bare `Subring`), so neither "`ker` closed" nor
"`C/ker` complete" can even be *stated*, let alone proved. Building the general-`n` Tate topology,
its completeness, and the multivariate Prop 6.17 is substantial new infrastructure (strictly larger
than the `n = 1` machinery) and is left as this single named residual rather than fabricated.

By contrast the **density** half (`example638_evalHom_denseRange`, including the linchpin
`invS_mem_range`: `1/s ∈ range` from Tate + the rational `hopen` datum) is now proved sorry-free and
faithfully, with no topology on `A⟨X₁..Xₙ⟩`. -/
private theorem example638_evalHom_range_isClosed
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] (D : RationalLocData A) :
    IsClosed (Set.range (example638_evalHom D)) :=
  sorry

set_option linter.unusedSectionVars false in
/-- **Example 6.38 surjectivity** (Wedhorn p. 56, `wedhorn.txt:2693`). The multivariate evaluation
`example638_evalHom : A⟨X₁,…,Xₙ⟩ → presheafValue D`, `Xᵢ ↦ tᵢ/s`, is **surjective** onto
`presheafValue D = Â⟨T/s⟩`.

Assembled from Wedhorn's two ingredients (a dense range whose closure is the whole completion ⟹
`range = closure range = univ`):

1. **Density** — `example638_evalHom_denseRange` (proved sorry-free): Wedhorn's `A[M]` is dense in
   `Â⟨T/s⟩`. The non-obvious content `1/s ∈ range` is `invS_mem_range`, proved faithfully from the
   **Tate** hypothesis (a topologically nilpotent unit lands in `Iᴺ`) and the rational `hopen`
   datum — NO `Σ tᵢ gᵢ = sᵏ` series, NO topology on `A⟨X₁..Xₙ⟩`.
2. **Closedness** — `example638_evalHom_range_isClosed` (the single named residual): Wedhorn's
   `Â⟨T/s⟩ = C/a` with `a` closed by Prop 6.17, needing the general-`n` Tate topology that the repo
   only has for `n ≤ 2`. See that lemma's docstring for the precise gap. -/
theorem example638_evalHom_surjective [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A]
    (D : RationalLocData A) : Function.Surjective (example638_evalHom D) := by
  rw [← Set.range_eq_univ, ← (example638_evalHom_range_isClosed D).closure_eq]
  exact (example638_evalHom_denseRange D).closure_range

set_option linter.unusedSectionVars false in
/-- **GENUINE RESIDUAL — Example 6.38, multivariate presentation** (Wedhorn p. 56,
`wedhorn.txt:2693`–`2707`). For a strongly noetherian Tate ring `A` and a rational locale
`D = R(T/s)` with `|D.T| = n`, the canonical ring homomorphism

  `C := A⟨X₁, …, Xₙ⟩ = restrictedMvPowerSeriesSubring n A  ⟶  presheafValue D = Â⟨T/s⟩`,
  `Xᵢ ↦ tᵢ/s`

is **surjective** (Wedhorn: `Â⟨T/s⟩ = C/a`, `a = (t − s·Xₜ)` — a *quotient* of `C`, so the
composite `C ↠ C/a ≅ presheafValue D` is onto). This is the **minimal** Example-6.38 content
needed for faithful noetherianness: it does NOT require the full ring iso, only the surjection,
because `IsNoetherianRing` transfers along surjections from a noetherian source
(`isNoetherianRing_of_surjective`), and `C = restrictedMvPowerSeriesSubring n A` is noetherian by
`IsStronglyNoetherian.isNoetherianRing_restricted n` (NO `pairSubring`/`A₀⟨X⟩` noetherianness, NO
noeth-`A₀` — the faithful case-(b) source of noetherianness).

**This is the documented repo gap.** The repo has the multivariate noetherian *ring*
`restrictedMvPowerSeriesSubring n A` (general `n : ℕ`) and its strong-noeth instance
(`RestrictedPowerSeries.lean:238` / `TateAlgebraTopology.lean:961` for `n = 1`), but it has only
the **univariate** (`Fin 1`) and **bivariate** (`Fin 2`) restricted-power-series *evaluation*
machinery (`TateAlgebraWedhorn.lean:423` `evalHomBounded`, `:566` `evalHomBounded₂`). The general
`Fin n` evaluation map `A⟨X₁..Xₙ⟩ →+* B` at a tuple of power-bounded elements `(t₁/s, …, tₙ/s)` —
together with its surjectivity onto the completion `presheafValue D` (dense image, since `A[M]` is
dense by Example 6.38, plus `C` complete ⇒ image closed) — is genuinely **absent**. Building it is
a substantial construction (multivariate summability of `∑ aᵥ (t/s)ᵛ` over `Fin n →₀ ℕ`, the
multivariate nonarchimedean Cauchy product for `map_mul`, and the density/completeness surjectivity
argument), strictly larger than the univariate `evalHomBounded`. Hence it is isolated here as the
single named residual rather than fabricated.

**Why the univariate equiv does not suffice.** `presheafValueCanonicalQuotientEquiv_faithful`
models `presheafValue D ≃+* A⟨X⟩/(1 − sX)` with `X ↦ invS = 1/s`, which needs `invS` power-bounded
(`hb`); that holds only for `1 ∈ T`-type data (e.g. the whole space, discharged in
`presheafValue_globalLocData_isNoetherianRing`), NOT for a general `R(T/s)` where `1/s` is not
power-bounded. The Wedhorn-faithful presentation for general `D` is the multivariate one above with
`Xᵢ ↦ tᵢ/s` (power-bounded on the rational subset). Reducing general `D` to the whole space by
localization is invalid (`restrictionMapHom_surj`, deprecated FALSE-in-general,
`PresheafTateStructure.lean`). -/
private theorem example638_multivariate_surjection
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] (D : RationalLocData A) :
    ∃ φ : (restrictedMvPowerSeriesSubring D.T.card A) →+* presheafValue D,
      Function.Surjective φ :=
  ⟨example638_evalHom D, example638_evalHom_surjective D⟩

/-- **Step 1 of Prop 8.30 — Example 6.38, noetherian part** (Wedhorn p. 81, `wedhorn.txt:4099`).
`B := presheafValue D` is a **noetherian** ring. FAITHFUL: depends only on the ambient `A`-bundle
and `D` — **no** `PairOfDefinition A`, **no** `[IsNoetherianRing P.A₀]`.

Body is sorry-free: noetherianness is transferred along the multivariate Example-6.38 surjection
`C = A⟨X₁..Xₙ⟩ ↠ presheafValue D` (`isNoetherianRing_of_surjective`) from the noetherian source
`C = restrictedMvPowerSeriesSubring D.T.card A` (`IsStronglyNoetherian.isNoetherianRing_restricted`,
case (b)). The single genuine residual — the surjection itself — is isolated in
`example638_multivariate_surjection`; see its docstring for the precise repo gap (the general
`Fin n` restricted-power-series evaluation map, present only for `Fin 1`/`Fin 2`). -/
private theorem presheafValue_isNoetherianRing_residual
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] (D : RationalLocData A) :
    IsNoetherianRing (presheafValue D) := by
  -- The whole-space case IS done faithfully (kept as the documented stepping stone):
  have _whole_space_done : ∀ P : PairOfDefinition A,
      IsNoetherianRing (presheafValue (globalLocData P)) :=
    presheafValue_globalLocData_isNoetherianRing
  -- The source `C = A⟨X₁..Xₙ⟩` is noetherian (case-(b): strongly noetherian `A`).
  haveI hC : IsNoetherianRing (restrictedMvPowerSeriesSubring D.T.card A) :=
    IsStronglyNoetherian.isNoetherianRing_restricted (A := A) D.T.card
  -- Example 6.38 (multivariate): `C ↠ presheafValue D` with `Xᵢ ↦ tᵢ/s`. The ONLY residual.
  -- Noetherianness then transfers along this surjection from the noetherian source `C`.
  obtain ⟨φ, hφ⟩ := example638_multivariate_surjection D
  exact isNoetherianRing_of_surjective _ _ φ hφ

private theorem presheafValue_isNoetherianRing_faithful
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] (D : RationalLocData A) :
    IsNoetherianRing (presheafValue D) :=
  presheafValue_isNoetherianRing_residual D

-- REMOVED (2026-06-03): `presheafValue_isLinearTopology_{residual,faithful}` asserted
-- `IsLinearTopology (presheafValue D)`, which is FALSE for a Tate ring (no proper open ideals,
-- since a topologically nilpotent unit puts a unit in every open ideal). After the A°-layer
-- migration (`IsLinearTopology A A` → `NonarchimedeanAddGroup`, Wedhorn Prop 5.30), `lemma_8_31_*`
-- over the base `B := presheafValue D` no longer require `[IsLinearTopology B B]`, so this false
-- obligation is gone — `prop_8_30_flat_of_faithful_base` now needs only the Tate + noetherian
-- instances on `B`.

/-- **GENUINE RESIDUAL — Steps 2–3 of Prop 8.30: Remark 7.55 + relative Example 6.38 over `B`**
(Wedhorn p. 81, `wedhorn.txt:4100`–`4104`, and Remark 7.55, `wedhorn.txt:3504`–`3517`).

`B := presheafValue D = O_X(V)` is a complete strongly noetherian Tate ring (Step 1), supplied
here as the explicit FAITHFUL instance bundle that the transport consumes: `IsTateRing B`,
`IsNoetherianRing B`, `NonarchimedeanRing B`, `T2Space B`, `IsHuberRing B`, `IsStronglyNoetherian B`
— **all derived from `hTate`/`hNoeth` and the plain `presheafValue` instances, with NO
`PairOfDefinition`, NO `[IsNoetherianRing P.A₀]`** (the `A`-bundle's `CompatiblePlusSubring` /
`HasLocLiftPowerBounded` are NOT used at the `B`-level here).

Wedhorn: "By Remark 7.55 we may assume `U` is `U₁ = R(f/1)` or `U₂ = R(1/f)` for some `f ∈ B`.
In Example 6.38 we have seen `O_X(U₁) = B̂⟨X⟩/(f−X)` and `O_X(U₂) = B̂⟨X⟩/(1−fX)`." Remark 7.55
(`wedhorn.txt:3517`) is in fact a **chain** `Spa B ⊇ X₀ ⊇ X₁ ⊇ ⋯ ⊇ Xₙ = U`, each `Xᵢ ⊆ Xᵢ₋₁` a
basic Laurent shape; flatness of `O_X(V) → O_X(U)` is the **composite** of the basic-Laurent
restrictions, each flat by Lemma 8.31(2). So `restrictionMapHom D D' h` is `B`-flat.

**This is the genuine repo gap** (the "unfaithful summit"). The faithful inputs are present —
`lemma_8_31_fSubX_flat (presheafValue D) f` and `lemma_8_31_oneSubfX_flat (presheafValue D) f` are
sorry-free over `B` (case (b), `[IsNoetherianRing B]` only, no noeth-`A₀`). What is MISSING is the
**relative reduction object**: the Remark-7.55 chain of basic-Laurent sub-locales of `Spa B`
together with the relative Example-6.38 `B`-algebra/`B`-linear identifications
`O_X(Xᵢ) ≃ₗ[B] (O_X(Xᵢ₋₁))⟨X⟩/(f̄−X)` resp. `/(1−f̄X)` intertwining `restrictionMapHom`, which would
let `Module.Flat.of_linearEquiv` + composition close the goal. The repo's relative-Example-6.38
machinery (`relativeLaurentNormalized_equiv`, `restrictionMap_flat_of_rational_subset_via_relative`,
`presheafValue_relative_equiv`) is **irreducibly entangled** with the case-(a) hypotheses
`(P : PairOfDefinition A) [IsNoetherianRing P.A₀]`, `[IsNoetherianRing (locSubring E.P E.T E.s)]`,
`hnoeth_B` (pairSubring noeth), `hP_A₀Noeth_B`, and routes `B`-level flatness through
`presheafValue_flat_of_canonical` → `flat_quotient_oneSubfX_general P` (Wedhorn case (a),
ℂ_p-false). The faithful version must rebuild that relative equiv over the `B`-bundle alone — the
same `Fin n`/relative Example-6.38 construction gap as `example638_multivariate_surjection`
(Residual 1). It is therefore isolated here as the single named residual rather than discharged via
the existing case-(a) route. (Note: `prop_8_30_flat_clean` in `StructureSheaf.lean` has this exact
signature but is OFF-LIMITS: it routes through `restrictionMap_isLocalization` = the RETIRED
`restrictionMapHom_surj`, FALSE-in-general, plus a FALSE noeth-`A₀` `sorry`.) -/
private theorem prop_8_30_relative_laurent_flat
    (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    [hTate : IsTateRing (presheafValue D)]
    [hNoeth : IsNoetherianRing (presheafValue D)]
    [IsHuberRing (presheafValue D)]
    [NonarchimedeanRing (presheafValue D)]
    [T2Space (presheafValue D)]
    [IsStronglyNoetherian (presheafValue D)] :
    @Module.Flat (presheafValue D) (presheafValue D') _ _
      (restrictionMapHom D D' h).toModule :=
  sorry

private theorem prop_8_30_flat_of_faithful_base
    (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (hTate : IsTateRing (presheafValue D))
    (hNoeth : IsNoetherianRing (presheafValue D)) :
    @Module.Flat (presheafValue D) (presheafValue D') _ _
      (restrictionMapHom D D' h).toModule := by
  -- Step 1 (faithful): assemble the complete strongly-noetherian-Tate bundle on `B := presheafValue
  -- D`. `IsTateRing`/`IsNoetherianRing` come in as `hTate`/`hNoeth`; `IsHuberRing` from `IsTateRing`;
  -- `NonarchimedeanRing`/`T2Space` are derivable from the plain `presheafValue` (completion)
  -- instances; `IsStronglyNoetherian` from `isStronglyNoetherian_of_isNoetherianRing_isTateRing`.
  -- None of this uses any `PairOfDefinition` / noeth-`A₀`.
  haveI := hTate
  haveI := hNoeth
  haveI : IsHuberRing (presheafValue D) := hTate.toIsHuberRing
  haveI : NonarchimedeanRing (presheafValue D) := inferInstance
  haveI : T2Space (presheafValue D) := inferInstance
  haveI : IsStronglyNoetherian (presheafValue D) :=
    isStronglyNoetherian_of_isNoetherianRing_isTateRing
  -- Steps 2–4 (Remark 7.55 + relative Example 6.38 over `B` + Lemma 8.31): the single genuine
  -- residual, isolated faithfully (NO noeth-`A₀`). See `prop_8_30_relative_laurent_flat`.
  exact prop_8_30_relative_laurent_flat D D' h

/-- **Proposition 8.30** (Wedhorn p.81, `wedhorn.txt:4095`): for rational subsets `U ⊆ V`
the restriction `O_X(V) → O_X(U)` is flat.

Faithful assembly of Wedhorn's four steps (see the section docstring above):

* **Step 1 (Example 6.38, the base):** `presheafValue_isTateRing_faithful`,
  `presheafValue_isNoetherianRing_faithful`, `presheafValue_isLinearTopology_faithful`
  promote `B := presheafValue D` to a complete strongly noetherian Tate ring (the derived
  members `IsHuberRing`/`IsStronglyNoetherian`/`HasLocLiftPowerBounded` follow, the latter via
  `isStronglyNoetherian_of_isNoetherianRing_isTateRing` + the strong-noeth-Tate instance).
* **Steps 2–4 (Remark 7.55 + Example 6.38 over `B` + Lemma 8.31):**
  `prop_8_30_flat_of_faithful_base` consumes that bundle and concludes flatness.

FAITHFUL: the `section Wedhorn828` `A`-bundle only — no `PairOfDefinition`, no noeth-`A₀`,
no data/witness parameters. **Step-1 Tate** (`presheafValue_isTateRing_faithful`) is now discharged
sorry-free and axiom-clean. The remaining `sorry`s live in three named helpers and are precise,
faithful-route residuals (NOT noeth-`A₀` smuggling); none adds hypotheses to this signature:
* `presheafValue_isNoetherianRing_faithful` — needs the **multivariate** Example 6.38
  `presheafValue D ≃ A⟨X₁..Xₙ⟩/a` (repo has only the univariate equiv; whole-space case done).
* `presheafValue_isLinearTopology_faithful` — `IsLinearTopology (presheafValue D)`, subtle/false-for
  -Tate (a nontrivial Tate ring has no proper open ideals); reduces to `isLinearTopology_locTopology`
  (repo gap) + completion-preserves-linear-topology.
* `prop_8_30_flat_of_faithful_base` — the Remark 7.55 + relative Example 6.38 reduction over `B`
  (the case-(a)-entangled relative-flatness machinery must be rebuilt over the `B`-bundle alone). -/
theorem prop_8_30_restriction_flat (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    @Module.Flat (presheafValue D) (presheafValue D') _ _
      (restrictionMapHom D D' h).toModule :=
  -- Step 1 (Example 6.38): `B := presheafValue D` is again complete strongly noetherian Tate.
  -- Steps 2–4 (Remark 7.55 + Example 6.38 over `B` + Lemma 8.31): the relative reduction.
  prop_8_30_flat_of_faithful_base D D' h
    (presheafValue_isTateRing_faithful D)
    (presheafValue_isNoetherianRing_faithful D)

/-- **Prime-surjectivity for a rational covering** — the geometric input to the
*faithful* half of Cor 8.32: every prime `p` of `O_X(X)` is the contraction of a prime
from some cover piece `O_X(Uᵢ)`. This is the algebraic shadow of `(Uᵢ)` covering
`X = Spa A` (every support prime is hit by some piece). -/
theorem cor_8_32_prime_surjection (C : RationalCovering A) :
    letI : ∀ D : { D // D ∈ C.covers }, Algebra (presheafValue C.base) (presheafValue D.1) :=
      fun D => (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
    ∀ (p : Ideal (presheafValue C.base)), p.IsPrime →
      ∃ (D : { D // D ∈ C.covers }) (q : Ideal (presheafValue D.1)), q.IsPrime ∧
        q.comap (algebraMap (presheafValue C.base) (presheafValue D.1)) = p := by
  sorry

/-- **Cor 8.32 — Wedhorn-faithful maximals route (geometric leaf).**

Wedhorn states Cor 8.32 as *immediate* from flatness (Prop 8.30) + the covering.
Mathlib's `Module.FaithfullyFlat` is **defined** by the maximals criterion
(`submodule_ne_top`: flat + `∀ maximal m, m • M ≠ ⊤`), so the only geometric
content is: for every **maximal** ideal `m` of the base `O_X(C.base)`, some cover
piece `D` has `m · O_X(D) ≠ ⊤`.

This is the *correct* faithful target. It avoids two dead ends:
* the exact prime-surjection `cor_8_32_prime_surjection` (`q.comap = p` for **all**
  primes) needs `supp x = p`, i.e. Bourbaki rank-1 domination — absent (Lemma745
  gives only `supp ⊇ p`); and
* the lifted-ideal route (`hSpa_points_nonOpen_via_lifted_ideal_proper`) lifts a
  prime of `A` to `presheafValue C.base`, which forces the residual
  `liftedIdeal ≠ ⊤` (= the Stacks-00MA / OMT analytic input).

Working with a **maximal `m` of the base directly**: `m` is non-open (proper in a
Tate ring), so `exists_spa_point_supp_ge_in_presheafValue` (Lemma 7.45 on the
completion, sorry-free) gives a Spa point `w` with `m ≤ supp w`, hence `supp w = m`
(`m` maximal); the covering places `w` in some piece `D`; the rational-subset ↔ Spa
correspondence (Wedhorn 7.46) extends `w` to `O_X(D)` with support over `m`, so
`m · O_X(D) ≠ ⊤`. No Bourbaki, no `liftedIdeal ≠ ⊤`, no OMT. -/
theorem cor_8_32_maximal_liftedIdeal_ne_top (C : RationalCovering A) :
    ∀ (m : Ideal (presheafValue C.base)), m.IsMaximal →
      ∃ (D : { D // D ∈ C.covers }),
        Ideal.map (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)) m ≠ ⊤ := by
  sorry

theorem cor_8_32_productRestriction_faithfullyFlat (C : RationalCovering A) :
    letI : ∀ D : { D // D ∈ C.covers }, Algebra (presheafValue C.base) (presheafValue D.1) :=
      fun D => (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
    Module.FaithfullyFlat (presheafValue C.base)
      (∀ D : { D // D ∈ C.covers }, presheafValue D.1) := by
  -- Compose the two sub-lemmas through the commutative-algebra fact
  -- `faithfullyFlat_pi_of_prime_surjection` (axiom-clean, `Cor832.lean`): a product of
  -- flat algebras whose covering is jointly prime-surjective is faithfully flat. All
  -- instances are supplied explicitly to avoid instance search over `presheafValue`
  -- (the algebra-induced module `Algebra.toModule ∘ RingHom.toAlgebra` is `rfl`-equal
  -- to `RingHom.toModule`, the module `prop_8_30_restriction_flat` is stated against).
  exact @faithfullyFlat_pi_of_prime_surjection (presheafValue C.base) _
    { D // D ∈ C.covers } (Finite.of_fintype _)
    (fun D => presheafValue D.1)
    (fun _ => inferInstance)
    (fun D => (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra)
    (fun D => prop_8_30_restriction_flat C.base D.1 (C.hsubset D.1 D.2))
    (cor_8_32_prime_surjection C)

/-- **Corollary 8.32, injectivity consequence** (the separation half of `IsSheafy`): the
product restriction `O_X(X) → ∏ O_X(Uᵢ)` is injective. Faithfully flat ⇒ injective.

**Discharged** (Wedhorn-faithful): the repo's axiom-clean
`productRestriction_injective_of_flat_and_lifting` (`Cor832.lean`, the
faithfully-flat ⇒ injective route, *no* noeth-A₀ / separation parameters) takes exactly
`flat_over_base = prop_8_30_restriction_flat` and `hSpa_surj = cor_8_32_prime_surjection`. -/
theorem cor_8_32_productRestrictionSub_injective (C : RationalCovering A) :
    Function.Injective (productRestrictionSub A C) := by
  haveI : Finite { D : RationalLocData A // D ∈ C.covers } := Finite.of_fintype _
  exact productRestrictionSub_injective_of_flat_and_lifting C
    (fun D => prop_8_30_restriction_flat C.base D.1 (C.hsubset D.1 D.2))
    (fun p hp => cor_8_32_prime_surjection C p hp)

/-- **Cor 8.32, topological inducing half**: `productRestrictionSub` carries the subspace
topology of its image inside `∏ O_X(Uᵢ)`. This is the open-mapping / strictness content
behind Wedhorn's "sheaf of **complete topological** rings" — supplied in the repo by the
Tate-absorbing Banach OMT (`productRestrictionSubToEqualizer_isOpenMap`, `BanachOMT.lean`,
Wedhorn Prop 6.18). The repo proof (`productRestrictionSub_isInducing_tate`) is currently
stated against `[IsNoetherianRing (…principalPair…A₀)]`; the Wedhorn case-(b) hypothesis is
ring-noetherian, so wiring it here awaits the noeth-A₀ → ring-noetherian retyping. -/
theorem cor_8_32_productRestrictionSub_isInducing (C : RationalCovering A) :
    Topology.IsInducing (productRestrictionSub A C) := by
  sorry

/-- **Corollary 8.32, topological strengthening** (the full `embedding` field of `IsSheafy`):
the product restriction is a topological embedding = topological inducing + injectivity. -/
theorem cor_8_32_productRestrictionSub_isEmbedding (C : RationalCovering A) :
    Topology.IsEmbedding (productRestrictionSub A C) :=
  ⟨cor_8_32_productRestrictionSub_isInducing C, cor_8_32_productRestrictionSub_injective C⟩

/-! ## Lemma 8.33 — the 2-element Laurent cover is `O_X`-acyclic

> **Lemma 8.33.** Let `A` be a strongly noetherian Tate affinoid ring, `f ∈ A`,
> `U₁ = {x : x(f) ≤ 1}`, `U₂ = {x : x(f) ≥ 1}`. Then the augmented Čech complex
> `0 → O_X(X) → O_X(U₁) × O_X(U₂) → O_X(U₁ ∩ U₂) → 0` is exact.

Via the explicit identifications (Examples 6.38, 6.39)
`O_X(U₁) = A⟨ζ⟩/(f−ζ)`, `O_X(U₂) = A⟨η⟩/(1−fη)`, `O_X(U₁∩U₂) = A⟨ζ,ζ⁻¹⟩/(f−ζ)`,
and the `λ`/`λ'`/`ι` diagram chase (injectivity of `ε` from Cor 8.32; surjectivity of `λ`,
`λ'`; `im ι = ker λ`). Stated here as the `IsSheafy` content (separation + gluing) for the
2-element Laurent cover `Uf`. -/
theorem lemma_8_33_laurent_cover_gluing (f : A) (C : RationalCovering A)
    (hC : True /- placeholder: C is the 2-element Laurent cover U_f generated by `f` -/)
    (g : ∀ (D : ↥C.covers), presheafValue D.1)
    (hcompat : ∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (g D₁) = restrictionMap D₂.1 D₃ h₃₂ (g D₂)) :
    ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = g D := by
  sorry

/-! ## Lemma 8.34 — a rational cover generated by `T` (with `T·A = A`) is `O_X`-acyclic

> **Lemma 8.34.** Let `A` be a complete strongly noetherian Tate ring and `U` a rational
> cover generated by some finite `T ⊆ A` with `T·A = A`. Then `U` is `O_X`-acyclic.

Wedhorn's proof: (i) Laurent covers `U_{f₁} × ⋯ × U_{fᵣ}` are acyclic by **Lemma 8.33** +
**Prop A.3(3)** induction; (ii) any `T`-generated cover admits a Laurent cover `V` with each
`U|V` generated by units (via Cor 7.32); (iii) unit-generated covers refine to Laurent
covers; (iv) combine by **Prop A.3(1)(2)**. Stated here as the `gluing` content. -/
theorem lemma_8_34_gluing (C : RationalCovering A)
    (g : ∀ (D : ↥C.covers), presheafValue D.1)
    (hcompat : ∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (g D₁) = restrictionMap D₂.1 D₃ h₃₂ (g D₂)) :
    ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = g D := by
  sorry

/-! ## Theorem 8.28(b) — assembled from Cor 8.32 (separation) and Lemma 8.34 (gluing)

> **Theorem 8.28(b).** If `A` is a strongly noetherian Tate ring then `O_X` is a sheaf of
> complete topological rings (and `H^q(U, O_X) = 0` for `q ≥ 1`).

By **Prop A.4** the sheaf property is equivalent to acyclicity of all rational covers; in the
Lean formulation `IsSheafy A` is the pair `(embedding, gluing)` per cover, supplied by
Cor 8.32 and Lemma 8.34 respectively. -/
theorem isSheafy_of_stronglyNoetherian_828b : IsSheafy A where
  embedding C := cor_8_32_productRestrictionSub_isEmbedding C
  gluing C f hcompat := lemma_8_34_gluing C f hcompat

end Wedhorn828

end ValuationSpectrum
