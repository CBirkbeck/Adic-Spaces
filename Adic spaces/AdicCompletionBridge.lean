/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.Topology.UniformSpace.AbstractCompletion
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Bridge between UniformSpace.Completion and AdicCompletion

For a commutative ring `R` with an ideal `I` such that the topology on `R`
is the `I`-adic topology (`IsAdic I`), we construct a ring isomorphism:

  `UniformSpace.Completion R ≃+* AdicCompletion I R`

## Strategy

`AdicCompletion I R` is a subtype of `∀ n, R ⧸ (I^n • ⊤)`. We put the
discrete uniformity on each quotient and the product uniformity on the Pi
type. `AdicCompletion` inherits the subtype uniformity. Then:

1. The product of discrete spaces is T₂ and complete.
2. `AdicCompletion` is a closed subtype → T₂ and complete.
3. `AdicCompletion.of I R` is uniform inducing with dense range.
4. Package as `AbstractCompletion`, use `compareEquiv`.
5. Multiplicativity by density + T₂.
-/

universe u

open scoped Topology Uniformity

open Filter Set Function

namespace AdicCompletionBridge

variable {R : Type u} [CommRing R] (I : Ideal R)

/-! ### The key submodule identity -/

/-- For a ring `R` as a module over itself: `I^n • ⊤ = I^n`. -/
theorem ideal_smul_top_eq_self (n : ℕ) :
    (I ^ n • (⊤ : Submodule R R) : Submodule R R) = ↑(I ^ n) := by
  ext x
  constructor
  · intro hx
    exact Submodule.smul_induction_on hx (fun a ha r _ => Ideal.mul_mem_right r _ ha)
      fun _ _ h1 h2 => (I ^ n).add_mem h1 h2
  · intro hx
    have : x * 1 ∈ (I ^ n • (⊤ : Submodule R R) : Submodule R R) :=
      Submodule.smul_mem_smul hx Submodule.mem_top
    rwa [mul_one] at this

/-! ### Discrete topology on quotients -/

/-- Discrete topology on `R ⧸ (I^n • ⊤)`. -/
noncomputable instance quotientDiscreteTopology (n : ℕ) :
    TopologicalSpace (R ⧸ (I ^ n • (⊤ : Submodule R R))) := ⊥

noncomputable instance quotientDiscreteUniformSpace (n : ℕ) :
    UniformSpace (R ⧸ (I ^ n • (⊤ : Submodule R R))) := ⊥

instance quotientDiscrete (n : ℕ) :
    DiscreteTopology (R ⧸ (I ^ n • (⊤ : Submodule R R))) := ⟨rfl⟩

instance quotientDiscreteUnif (n : ℕ) :
    DiscreteUniformity (R ⧸ (I ^ n • (⊤ : Submodule R R))) := ⟨rfl⟩

/-! ### Helper: coordinate entourages -/

/-- `{(f,g) | f n = g n}` is a Pi-uniformity entourage (discrete factors). -/
private theorem pi_coord_mem_uniformity (n : ℕ) :
    {p : (∀ k, R ⧸ (I ^ k • (⊤ : Submodule R R))) ×
         (∀ k, R ⧸ (I ^ k • (⊤ : Submodule R R))) |
      p.1 n = p.2 n} ∈
      𝓤 (∀ k, R ⧸ (I ^ k • (⊤ : Submodule R R))) := by
  rw [Pi.uniformity]
  apply Filter.mem_iInf_of_mem n
  rw [Filter.mem_comap]
  exact ⟨{p | p.1 = p.2}, Filter.mem_principal_self _, fun ⟨_, _⟩ h => h⟩

/-- `{(x,y) | eval n x = eval n y}` is in the subtype uniformity of AdicCompletion. -/
private theorem eval_entourage_mem [UniformSpace R] (n : ℕ) :
    {p : AdicCompletion I R × AdicCompletion I R |
      AdicCompletion.eval I R n p.1 =
        AdicCompletion.eval I R n p.2} ∈
      @uniformity (AdicCompletion I R) instUniformSpaceSubtype := by
  apply Filter.mem_comap.mpr
  exact ⟨{p | p.1 n = p.2 n}, pi_coord_mem_uniformity I n,
    fun ⟨_, _⟩ h => h⟩

/-! ### Topology and uniformity on AdicCompletion via subtype of product -/

section Instances

variable [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]

/-- The uniform structure on `AdicCompletion I R`: the subtype uniformity
from the product `∀ n, R ⧸ (I^n • ⊤)` with discrete factors. -/
noncomputable instance adicCompletionUniformSpace :
    UniformSpace (AdicCompletion I R) :=
  instUniformSpaceSubtype

/-- `AdicCompletion I R` is T₀ because elements agreeing at all levels are equal. -/
instance adicCompletionT0 : @T0Space (AdicCompletion I R)
    (adicCompletionUniformSpace I).toTopologicalSpace := by
  constructor
  intro ⟨f, hf⟩ ⟨g, hg⟩ hinsep
  ext n
  have hpi : @Inseparable _ Pi.topologicalSpace
      (⟨f, hf⟩ : AdicCompletion I R).val (⟨g, hg⟩ : AdicCompletion I R).val :=
    Inseparable.map hinsep continuous_subtype_val
  rw [@inseparable_pi] at hpi
  exact (hpi n).eq

/-- The set underlying `AdicCompletion I R` inside the product type. -/
private def adicCompletionSet :
    Set (∀ k, R ⧸ (I ^ k • (⊤ : Submodule R R))) :=
  {f | ∀ {m n : ℕ} (hmn : m ≤ n),
    (AdicCompletion.transitionMap I R hmn) (f n) = f m}

omit [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R] in
private theorem adicCompletionSet_isClosed : IsClosed (adicCompletionSet I) := by
  unfold adicCompletionSet
  have : {g : ∀ k, R ⧸ (I ^ k • (⊤ : Submodule R R)) |
      ∀ {m n : ℕ} (hmn : m ≤ n),
        (AdicCompletion.transitionMap I R hmn) (g n) = g m} =
    ⋂ (p : ℕ × ℕ) (_ : p.1 ≤ p.2),
      {g | (AdicCompletion.transitionMap I R ‹p.1 ≤ p.2›) (g p.2) = g p.1} := by
    ext g; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact ⟨fun h p hp => h hp, fun h m n hmn => h ⟨m, n⟩ hmn⟩
  rw [this]
  exact isClosed_iInter fun ⟨m, n⟩ => isClosed_iInter fun hmn =>
    isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply n))
      (continuous_apply m)

/-- `AdicCompletion I R` is complete: it's a closed subtype of the complete
product `∀ n, R ⧸ (I^n • ⊤)` (product of discrete = complete). -/
instance adicCompletionComplete : @CompleteSpace (AdicCompletion I R)
    (adicCompletionUniformSpace I) :=
  (adicCompletionSet_isClosed I).completeSpace_coe

end Instances

section Bridge

variable [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]

omit [IsTopologicalRing R] in
/-- `AdicCompletion.of I R` is uniform inducing for the I-adic uniformity
on `R` and the subtype uniformity on `AdicCompletion I R`. -/
theorem of_isUniformInducing (hadic : IsAdic I) :
    @IsUniformInducing R (AdicCompletion I R) _ (adicCompletionUniformSpace I)
      (AdicCompletion.of I R) := by
  constructor
  have hbasis_nhds : (𝓝 (0 : R)).HasBasis (fun (_ : ℕ) => True)
      (fun n => ((I ^ n : Ideal R) : Set R)) := by
    have h : @nhds R _ 0 = @nhds R I.adicTopology 0 := by rw [hadic]
    rw [h]; convert Ideal.hasBasis_nhds_adic I (0 : R) using 1
    funext n; simp [zero_add, Set.image_id']
  have hbasis_unif := hbasis_nhds.uniformity_of_nhds_zero
  have hbasis_comap : (Filter.comap (fun x =>
      ((AdicCompletion.of I R) x.1, (AdicCompletion.of I R) x.2))
      (𝓤 (AdicCompletion I R))).HasBasis (fun (_ : ℕ) => True)
      (fun n => {x : R × R | x.2 - x.1 ∈ (I ^ n : Ideal R)}) := by
    constructor; intro U; constructor
    · intro hU
      obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
      obtain ⟨W, hW, hWV⟩ := Filter.mem_comap.mp hV
      rw [Pi.uniformity, Filter.mem_iInf] at hW
      obtain ⟨S, hSfin, V_fn, hV_mem, hW_eq⟩ := hW
      refine ⟨hSfin.toFinset.sup id, trivial, ?_⟩
      intro ⟨a, b⟩ (hab : b - a ∈ (I ^ hSfin.toFinset.sup id : Ideal R))
      apply hVU; apply hWV; rw [hW_eq]
      apply Set.mem_iInter.mpr; intro ⟨i, hi⟩
      obtain ⟨D_i, hD_i, hD_V⟩ := Filter.mem_comap.mp (hV_mem ⟨i, hi⟩)
      apply hD_V
      have hle : i ≤ hSfin.toFinset.sup id :=
        Finset.le_sup (f := id) (hSfin.mem_toFinset.mpr hi)
      have hsub : b - a ∈ (I ^ i : Ideal R) := Ideal.pow_le_pow_right hle hab
      have heval_eq : (AdicCompletion.of I R a).val i =
          (AdicCompletion.of I R b).val i := by
        change AdicCompletion.eval I R i (AdicCompletion.of I R a) =
          AdicCompletion.eval I R i (AdicCompletion.of I R b)
        rw [AdicCompletion.eval_of, AdicCompletion.eval_of, ← sub_eq_zero, ← map_sub]
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        rw [ideal_smul_top_eq_self]
        exact (I ^ i).neg_mem_iff.mp (by rwa [neg_sub])
      change ((AdicCompletion.of I R a).val i, (AdicCompletion.of I R b).val i) ∈ D_i
      rw [heval_eq]; exact refl_mem_uniformity hD_i
    · rintro ⟨n, -, hn⟩
      apply Filter.mem_comap.mpr
      refine ⟨{p | AdicCompletion.eval I R n p.1 =
        AdicCompletion.eval I R n p.2}, eval_entourage_mem I n, ?_⟩
      intro ⟨a, b⟩ hab
      apply hn; change b - a ∈ (I ^ n : Ideal R)
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hab
      rw [AdicCompletion.eval_of, AdicCompletion.eval_of] at hab
      have hmem := (Submodule.Quotient.eq (I ^ n • ⊤)).mp hab
      rw [ideal_smul_top_eq_self] at hmem
      exact (I ^ n).neg_mem_iff.mp (by rwa [neg_sub])
  exact hbasis_unif.eq_of_same_basis hbasis_comap |>.symm

omit [IsUniformAddGroup R] [IsTopologicalRing R] in
/-- `AdicCompletion.of I R` has dense range in the subtype topology. -/
theorem of_denseRange (_hadic : IsAdic I) :
    @DenseRange (AdicCompletion I R) (adicCompletionUniformSpace I).toTopologicalSpace
      R (AdicCompletion.of I R) := by
  intro x
  choose r hr using fun n => Submodule.Quotient.mk_surjective (I ^ n • ⊤) (x.val n)
  have htendsto : Filter.Tendsto (fun n => AdicCompletion.of I R (r n))
      Filter.atTop (@nhds _ (adicCompletionUniformSpace I).toTopologicalSpace x) := by
    rw [Filter.Tendsto, Filter.map_le_iff_le_comap, Filter.le_def]
    intro U hU
    rw [Filter.mem_comap] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    rw [@nhds_eq_comap_uniformity _ (adicCompletionUniformSpace I)] at hV
    obtain ⟨E, hE, hEV⟩ := Filter.mem_comap.mp hV
    obtain ⟨W, hW, hWE⟩ := Filter.mem_comap.mp hE
    rw [Pi.uniformity] at hW
    obtain ⟨S, hSfin, V_fn, hV_fn, hW_eq⟩ := (Filter.mem_iInf).mp hW
    apply Filter.mem_atTop_sets.mpr
    refine ⟨hSfin.toFinset.sup id, fun m hm => hVU ?_⟩
    apply hEV; apply hWE; rw [hW_eq]; apply Set.mem_iInter.mpr
    intro ⟨i, hi⟩
    obtain ⟨D_i, hD_i, hD_V⟩ := Filter.mem_comap.mp (hV_fn ⟨i, hi⟩)
    apply hD_V
    change (x.val i, (AdicCompletion.of I R (r m)).val i) ∈ D_i
    have hle : i ≤ hSfin.toFinset.sup id :=
      Finset.le_sup (f := id) (hSfin.mem_toFinset.mpr hi)
    have hle_m : i ≤ m := le_trans hle hm
    have heval : (AdicCompletion.of I R (r m)).val i = x.val i := by
      have h1 := (AdicCompletion.of I R (r m)).property hle_m
      have h2 := x.property hle_m
      change AdicCompletion.eval I R i (AdicCompletion.of I R (r m)) = x.val i
      rw [show AdicCompletion.eval I R i (AdicCompletion.of I R (r m)) =
        (AdicCompletion.transitionMap I R hle_m)
          (AdicCompletion.eval I R m (AdicCompletion.of I R (r m))) from h1.symm,
        AdicCompletion.eval_of]
      change (AdicCompletion.transitionMap I R hle_m) (Submodule.Quotient.mk (r m)) = x.val i
      rw [hr m, h2]
    rw [heval]; exact refl_mem_uniformity hD_i
  exact mem_closure_of_tendsto htendsto
    (Filter.Eventually.of_forall fun n => Set.mem_range.mpr ⟨r n, rfl⟩)

/-- `AdicCompletion I R` with subtype uniformity as an `AbstractCompletion`. -/
noncomputable def adicAbstractCompletion (hadic : IsAdic I) : AbstractCompletion R where
  space := AdicCompletion I R
  coe := AdicCompletion.of I R
  uniformStruct := adicCompletionUniformSpace I
  complete := adicCompletionComplete I
  separation := adicCompletionT0 I
  isUniformInducing := of_isUniformInducing I hadic
  dense := of_denseRange I hadic

/-- Forward comparison: `Completion R → AdicCompletion I R`. -/
noncomputable def adicCompletionEquiv (hadic : IsAdic I) :
    UniformSpace.Completion R → AdicCompletion I R :=
  (UniformSpace.Completion.cPkg (α := R)).compare (adicAbstractCompletion I hadic)

/-- Backward comparison: `AdicCompletion I R → Completion R`. -/
noncomputable def adicCompletionEquivInv (hadic : IsAdic I) :
    AdicCompletion I R → UniformSpace.Completion R :=
  (adicAbstractCompletion I hadic).compare (UniformSpace.Completion.cPkg (α := R))

/-- The ring isomorphism `Completion R ≃+* AdicCompletion I R`. -/
noncomputable def adicCompletionRingEquiv (hadic : IsAdic I) :
    UniformSpace.Completion R ≃+* AdicCompletion I R := by
  let e := adicCompletionEquiv I hadic
  let e_inv := adicCompletionEquivInv I hadic
  haveI : T2Space (AdicCompletion I R) := inferInstance
  haveI : CompleteSpace (AdicCompletion I R) := adicCompletionComplete I
  haveI : ContinuousMul (AdicCompletion I R) := ⟨by
    apply Continuous.subtype_mk; apply continuous_pi; intro n
    change Continuous fun p : AdicCompletion I R × AdicCompletion I R =>
      p.1.val n * p.2.val n
    exact ((continuous_apply n).comp (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_apply n).comp (continuous_subtype_val.comp continuous_snd))⟩
  haveI : ContinuousAdd (AdicCompletion I R) := ⟨by
    apply Continuous.subtype_mk; apply continuous_pi; intro n
    change Continuous fun p : AdicCompletion I R × AdicCompletion I R =>
      p.1.val n + p.2.val n
    exact ((continuous_apply n).comp (continuous_subtype_val.comp continuous_fst)).add
      ((continuous_apply n).comp (continuous_subtype_val.comp continuous_snd))⟩
  have he_cont : Continuous e := @UniformSpace.Completion.continuous_extension
    R _ (AdicCompletion I R) (adicCompletionUniformSpace I)
    (f := AdicCompletion.of I R) (adicCompletionComplete I)
  have he_coe : ∀ a : R, e (↑a) = AdicCompletion.of I R a := fun a =>
    AbstractCompletion.compare_coe
      UniformSpace.Completion.cPkg (adicAbstractCompletion I hadic) a
  exact {
    toFun := e
    invFun := e_inv
    left_inv := fun x => congr_fun (AbstractCompletion.inverse_compare
      (adicAbstractCompletion I hadic) UniformSpace.Completion.cPkg) x
    right_inv := fun x => congr_fun (AbstractCompletion.inverse_compare
      UniformSpace.Completion.cPkg (adicAbstractCompletion I hadic)) x
    map_mul' := fun x y => by
      refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
      · exact isClosed_eq (he_cont.comp continuous_mul)
          ((he_cont.comp continuous_fst).mul (he_cont.comp continuous_snd))
      · intro a b
        rw [← UniformSpace.Completion.coe_mul, he_coe, he_coe, he_coe]
        exact map_mul (algebraMap R (AdicCompletion I R)) a b
    map_add' := fun x y => by
      refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
      · exact isClosed_eq (he_cont.comp continuous_add)
          ((he_cont.comp continuous_fst).add (he_cont.comp continuous_snd))
      · intro a b
        rw [show (↑a : UniformSpace.Completion R) + ↑b = ↑(a + b) from
          (map_add UniformSpace.Completion.coeRingHom a b).symm,
          he_coe, he_coe, he_coe, map_add (AdicCompletion.of I R)]
  }

end Bridge

/-! ### Ring equivalence for abstract completions -/

/-- A complete T₂ commutative ring S with a dense uniform-inducing ring hom
from R is ring-isomorphic to `Completion R`. The forward map is `extensionHom g`
(a ring hom by construction); the inverse is the AbstractCompletion comparison.
Bijectivity follows from the comparison being a two-sided inverse. -/
noncomputable def completionRingEquiv
    {R : Type*} [CommRing R] [UniformSpace R] [IsTopologicalRing R]
    [IsUniformAddGroup R]
    {S : Type*} [CommRing S] [UniformSpace S] [IsTopologicalRing S]
    [IsUniformAddGroup S] [T2Space S] [CompleteSpace S]
    (g : R →+* S) (hg_cont : Continuous g) (hg_ui : IsUniformInducing g)
    (hg_dense : DenseRange g) : UniformSpace.Completion R ≃+* S := by
  let f := UniformSpace.Completion.extensionHom g hg_cont
  let pkg : AbstractCompletion R :=
    ⟨S, g, inferInstance, inferInstance, inferInstance, hg_ui, hg_dense⟩
  letI := (@UniformSpace.Completion.cPkg R _).uniformStruct
  haveI := (@UniformSpace.Completion.cPkg R _).complete
  haveI := (@UniformSpace.Completion.cPkg R _).separation
  let f_inv : S → UniformSpace.Completion R :=
    pkg.compare UniformSpace.Completion.cPkg
  have hf_inv_coe : ∀ a : R, f_inv (g a) = (↑a : UniformSpace.Completion R) :=
    AbstractCompletion.compare_coe pkg UniformSpace.Completion.cPkg
  have hf_coe : ∀ a : R, f (↑a) = g a :=
    UniformSpace.Completion.extensionHom_coe _ _
  have hf_cont : Continuous f := UniformSpace.Completion.continuous_extension
  have hf_inv_cont : Continuous f_inv :=
    (AbstractCompletion.uniformContinuous_compare pkg
      UniformSpace.Completion.cPkg).continuous
  exact {
    f with
    invFun := f_inv
    left_inv := fun x => by
      change f_inv (f x) = x
      refine UniformSpace.Completion.induction_on x ?_ ?_
      · exact isClosed_eq (hf_inv_cont.comp hf_cont) continuous_id
      · intro a; rw [hf_coe, hf_inv_coe]
    right_inv := congr_fun (hg_dense.equalizer (hf_cont.comp hf_inv_cont)
      continuous_id (funext fun a => by
        simp [Function.comp, hf_inv_coe, hf_coe]))
  }

/-! ### Kernel identity for evalₐ -/

/-- In the adic completion of a Noetherian ring, the kernel of the evaluation
at level `n` equals the ideal generated by the image of `I^n`. -/
theorem ker_evalₐ_eq {R : Type*} [CommRing R] (I : Ideal R)
    [IsNoetherianRing R] (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n) =
    Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ n) := by
  apply le_antisymm
  · intro x hx; rw [RingHom.mem_ker] at hx
    have hxn : x.val n = 0 := by
      unfold AdicCompletion.evalₐ at hx
      simp only [AlgHom.comp_apply, AlgHom.ofLinearMap_apply] at hx
      exact (Ideal.quotientEquivAlgOfEq R (ideal_smul_top_eq_self I n)).injective
        (hx.trans (map_zero _).symm)
    have hmkQ : AdicCompletion.map I (I ^ n • ⊤ : Submodule R R).mkQ x = 0 := by
      apply AdicCompletion.ext; intro m
      change (I ^ n • ⊤ : Submodule R R).mkQ.reduceModIdeal (I ^ m) (x.val m) = 0
      by_cases hmn : m ≤ n
      · rw [show x.val m = AdicCompletion.transitionMap I R hmn (x.val n) from
          (x.property hmn).symm, hxn, map_zero, map_zero]
      · push_neg at hmn
        obtain ⟨r, hr_eq⟩ := Submodule.Quotient.mk_surjective _ (x.val m)
        have hr_mem : r ∈ (I ^ n • ⊤ : Submodule R R) := by
          rw [← Submodule.Quotient.mk_eq_zero]
          have : AdicCompletion.transitionMap I R (le_of_lt hmn) (x.val m) = 0 := by
            rw [x.property (le_of_lt hmn)]; exact hxn
          rw [← hr_eq] at this; convert this using 1
        have h1 : (I ^ n • ⊤ : Submodule R R).mkQ r = 0 :=
          (Submodule.Quotient.mk_eq_zero _).mpr hr_mem
        rw [show x.val m = Submodule.Quotient.mk r from hr_eq.symm]
        change Submodule.Quotient.mk ((I ^ n • ⊤ : Submodule R R).mkQ r) = 0
        rw [h1]; rfl
    obtain ⟨z, rfl⟩ : x ∈ Set.range
        (AdicCompletion.map I (I ^ n • ⊤ : Submodule R R).subtype) := by
      rwa [← AdicCompletion.map_exact (I := I) Subtype.val_injective
        (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)]
    obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I _ z
    refine TensorProduct.induction_on t ?_ ?_ ?_
    · simp [map_zero]
    · intro c a
      rw [AdicCompletion.ofTensorProduct_tmul, map_smul, AdicCompletion.map_of]
      have ha_mem : (a : R) ∈ (I ^ n : Ideal R) := by
        have h := a.2; change (a : R) ∈ (I ^ n • ⊤ : Submodule R R) at h
        simp only [ideal_smul_top_eq_self] at h; exact h
      exact Ideal.mul_mem_left _ c (Ideal.mem_map_of_mem _ ha_mem)
    · intro _ _ h1 h2; simp only [map_add]; exact Ideal.add_mem _ h1 h2
  · rw [Ideal.map_le_iff_le_comap]; intro a ha
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    change (AdicCompletion.evalₐ I n) (AdicCompletion.of I R a) = 0
    rw [AdicCompletion.evalₐ_of]; exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

end AdicCompletionBridge
