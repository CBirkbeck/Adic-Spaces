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
  [NonarchimedeanRing A] [CompatiblePlusSubring A] [IsLinearTopology A A]
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

Faithful: `[CompleteSpace A]`, `[IsNoetherianRing A]`, `[IsTateRing A]`, `[IsLinearTopology A A]`
only — no ring of definition `A₀`. -/
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
/-- **Proposition 8.30** (Wedhorn p.81): for rational subsets `U ⊆ V` the restriction
`O_X(V) → O_X(U)` is flat.

Wedhorn's proof: by **Example 6.38** `O_X(V)` is again a strongly noetherian Tate ring,
so WLOG `V = X` and `A` complete; by **Remark 7.55** WLOG `U = U₁ = R(f/1)` or
`U₂ = R(1/f)`; **Example 6.38** identifies `O_X(U₁) = A⟨X⟩/(f − X)` and
`O_X(U₂) = A⟨X⟩/(1 − fX)`, at which point flatness is exactly **Lemma 8.31(2)**
(`lemma_8_31_fSubX_flat` / `lemma_8_31_oneSubfX_flat`, filled above). -/
theorem prop_8_30_restriction_flat (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    @Module.Flat (presheafValue D) (presheafValue D') _ _
      (restrictionMapHom D D' h).toModule := by
  sorry

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
