/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.AdicCompletion.Algebra
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
  ext x; constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha r _ => ?_) (fun _ _ h1 h2 => ?_)
    · change a * r ∈ (I ^ n : Ideal R)
      exact Ideal.mul_mem_right r _ ha
    · exact (I ^ n).add_mem h1 h2
  · intro hx
    have : x = x • (1 : R) := (mul_one x).symm
    rw [this]
    exact Submodule.smul_mem_smul hx Submodule.mem_top

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
  -- Inseparable in subtype → inseparable in Pi → pointwise inseparable → equal (discrete)
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

/-- `AdicCompletion.of I R` is uniform inducing for the I-adic uniformity
on `R` and the subtype uniformity on `AdicCompletion I R`. -/
theorem of_isUniformInducing (hadic : IsAdic I) :
    @IsUniformInducing R (AdicCompletion I R) _ (adicCompletionUniformSpace I)
      (AdicCompletion.of I R) := by
  constructor
  -- Need: comap (Prod.map of of) 𝓤(AdicCompletion) = 𝓤 R
  -- Both uniformities have basis: {(a,b) | a - b ∈ I^n} for each n.
  -- LHS: subtype of Pi-discrete, pulled back via of.
  -- RHS: I-adic uniformity (from IsAdic I).
  -- Get the adic nhds basis for nhds 0 (using hadic to align topologies)
  have hbasis_nhds : (𝓝 (0 : R)).HasBasis (fun (_ : ℕ) => True)
      (fun n => ((I ^ n : Ideal R) : Set R)) := by
    have h : @nhds R _ 0 = @nhds R I.adicTopology 0 := by rw [hadic]
    rw [h]; convert Ideal.hasBasis_nhds_adic I (0 : R) using 1
    funext n; simp [zero_add, Set.image_id']
  -- Get the uniformity basis: {(a,b) | b - a ∈ I^n}
  have hbasis_unif := hbasis_nhds.uniformity_of_nhds_zero
  -- hbasis_unif : 𝓤 R has basis (fun n => {p | p.2 - p.1 ∈ I^n})
  -- Both 𝓤 R and comap have the same basis: {(a,b) | b-a ∈ I^n}.
  -- Use HasBasis.eq_of_same_basis to conclude equality.
  -- Step 1: Show the comap has this basis.
  have hbasis_comap : (Filter.comap (fun x =>
      ((AdicCompletion.of I R) x.1, (AdicCompletion.of I R) x.2))
      (𝓤 (AdicCompletion I R))).HasBasis
      (fun (_ : ℕ) => True)
      (fun n => {x : R × R | x.2 - x.1 ∈ (I ^ n : Ideal R)}) := by
    constructor; intro U; constructor
    · -- U ∈ comap → ∃ n, True ∧ basis_n ⊆ U
      intro hU
      -- Extract V from comap, W from Pi uniformity, S from finite iInf.
      obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
      obtain ⟨W, hW, hWV⟩ := Filter.mem_comap.mp hV
      rw [Pi.uniformity] at hW
      -- W ∈ ⨅ i, F_i. By mem_iInf: ∃ finite I, ∃ V, (∀ i, V i ∈ F_i) ∧ W = ⋂ V.
      rw [Filter.mem_iInf] at hW
      obtain ⟨S, hSfin, V_fn, hV_mem, hW_eq⟩ := hW
      -- Take n = max of S (or 0 if empty).
      -- S : Set ℕ, V_fn : S → Set (Pi × Pi), hW_eq : W = ⋂ i, V_fn i
      -- Each V_fn ⟨i, hi⟩ ∈ comap (proj_i × proj_i) 𝓤(Q_i).
      -- So V_fn ⟨i, hi⟩ ⊇ {(f,g) | f i = g i}.
      -- W = ⋂ V_fn ⟨i, hi⟩ ⊇ ⋂_{i ∈ S} {agree at i}.
      -- On AdicCompletion: {agree at max(S)} ⊆ {agree at i} for i ∈ S.
      -- So W ⊇ {agree at max(S)}.
      -- Pull back: U ⊇ {(a,b) | b-a ∈ I^max(S)}.
      refine ⟨hSfin.toFinset.sup id, trivial, ?_⟩
      intro ⟨a, b⟩ (hab : b - a ∈ (I ^ hSfin.toFinset.sup id : Ideal R))
      apply hVU; apply hWV; rw [hW_eq]
      -- Need: ((of a).val, (of b).val) ∈ ⋂ i, V_fn i
      apply Set.mem_iInter.mpr; intro ⟨i, hi⟩
      -- Need: ((of a).val, (of b).val) ∈ V_fn ⟨i, hi⟩
      -- V_fn ⟨i, hi⟩ ∈ comap (proj_i × proj_i) 𝓤(Q_i)
      obtain ⟨D_i, hD_i, hD_V⟩ := Filter.mem_comap.mp (hV_mem ⟨i, hi⟩)
      apply hD_V
      -- Need: ((of a).val i, (of b).val i) ∈ D_i
      -- D_i ∈ 𝓤(Q_i) = principal diagonal. So D_i ⊇ diagonal.
      -- (of a).val i = (of b).val i (from hab + eval_agree_of_le).
      have hle : i ≤ hSfin.toFinset.sup id :=
        Finset.le_sup (f := id) (hSfin.mem_toFinset.mpr hi)
      have hsub : b - a ∈ (I ^ i : Ideal R) := Ideal.pow_le_pow_right hle hab
      -- Show eval agreement: (of a).val i = (of b).val i
      have heval_eq : (AdicCompletion.of I R a).val i =
          (AdicCompletion.of I R b).val i := by
        change AdicCompletion.eval I R i (AdicCompletion.of I R a) =
          AdicCompletion.eval I R i (AdicCompletion.of I R b)
        rw [AdicCompletion.eval_of, AdicCompletion.eval_of]
        rw [← sub_eq_zero, ← map_sub]
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        rw [ideal_smul_top_eq_self]
        exact (I ^ i).neg_mem_iff.mp (show -(a - b) ∈ (I ^ i : Ideal R) by rwa [neg_sub])
      -- Now show the pair is in (proj_i × proj_i)⁻¹(D_i).
      show ((AdicCompletion.of I R a).val i, (AdicCompletion.of I R b).val i) ∈ D_i
      rw [heval_eq]; exact refl_mem_uniformity hD_i
    · -- ∃ n, True ∧ basis_n ⊆ U → U ∈ comap
      rintro ⟨n, -, hn⟩
      apply Filter.mem_comap.mpr
      refine ⟨{p | AdicCompletion.eval I R n p.1 =
        AdicCompletion.eval I R n p.2}, eval_entourage_mem I n, ?_⟩
      intro ⟨a, b⟩ hab
      apply hn; show b - a ∈ (I ^ n : Ideal R)
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hab
      rw [AdicCompletion.eval_of, AdicCompletion.eval_of] at hab
      have hmem := (Submodule.Quotient.eq (I ^ n • ⊤)).mp hab
      rw [ideal_smul_top_eq_self] at hmem
      exact (I ^ n).neg_mem_iff.mp (show -(b - a) ∈ (I ^ n : Ideal R) by rwa [neg_sub])
  exact hbasis_unif.eq_of_same_basis hbasis_comap |>.symm

/-- `AdicCompletion.of I R` has dense range in the subtype topology. -/
theorem of_denseRange (hadic : IsAdic I) :
    @DenseRange (AdicCompletion I R) (adicCompletionUniformSpace I).toTopologicalSpace
      R (AdicCompletion.of I R) := by
  -- For each x : AdicCompletion, construct a sequence of(r_n) → x.
  -- r_n = representative of x.val n. Then of(r_n) agrees with x at levels ≤ n.
  -- Hence of(r_n) → x in the Pi-discrete topology → x ∈ closure(range of).
  intro x
  -- Choose r_n for each n
  choose r hr using fun n => Submodule.Quotient.mk_surjective (I ^ n • ⊤) (x.val n)
  -- hr n : (I ^ n • ⊤).mkQ (r n) = x.val n
  -- U ∈ nhds x (subtype). So val⁻¹(some Pi open) ⊆ U with x in it.
  -- Decompose using the uniformity basis: U ⊇ ball(x, E) for E ∈ 𝓤.
  -- E ∈ 𝓤(AC) = subtype of Pi-discrete.
  -- Ball: {y | (x,y) ∈ E}. E ⊇ {(a,b) | a.val n = b.val n} for some n.
  -- Ball ⊇ {y | y.val n = x.val n}.
  -- of(r n) has: (of (r n)).val n = mkQ_n(r n) = x.val n (by hr n + eval_of).
  -- So of(r n) ∈ ball(x, E) ⊆ U. And of(r n) ∈ range(of). Done.
  --
  -- Formalize: extract entourage from nhds, find n, use r n.
  -- Use eval_entourage_mem: {(a,b) | eval n a = eval n b} ∈ 𝓤(AC).
  -- Ball(x, this entourage) = {y | eval n y = eval n x} = {y | y.val n = x.val n}.
  -- This is a nhd of x (entourage ball is always a nhd).
  -- of(r n) is in this set: (of (r n)).val n = mkQ_n(r n) = x.val n (by hr n + eval_of).
  -- So of(r n) ∈ ball(x, entourage) and of(r n) ∈ range(of).
  -- The ball is a nhd ⊆ U for some n... but we need U-specific n.
  -- Actually: U is already a nhd. We need U ∩ range(of) ≠ ∅.
  -- If U ⊇ ball(x, E_n) for some n: use r n.
  -- Since nhds x has basis from uniformity balls:
  -- U ∈ nhds x means U ⊇ ball(x, E) for some E ∈ 𝓤.
  -- E ∈ 𝓤(AC). Using the IsUniformInducing proof infrastructure:
  -- E contains an entourage of the form {(a,b) | ∀ i ∈ S, a.val i = b.val i} for finite S.
  -- Ball(x, this) = {y | ∀ i ∈ S, y.val i = x.val i}.
  -- Use r (max S): of(r (max S)).val i = mkQ_i(r(max S)) = transition(x.val (max S)) = x.val i.
  -- The last step uses x.property and eval_of.
  -- So of(r (max S)) ∈ ball ⊆ U. Done.
  --
  -- But extracting S from E ∈ 𝓤(AC) is the same filter plumbing issue!
  -- Let me just use the `eval_entourage_mem` directly.
  -- For each n: ball(x, eval_n_entourage) is a nhd of x.
  -- So nhds x has basis including these balls.
  -- If U ∈ nhds x: U ⊇ some ball. But which?
  --
  -- SIMPLER: just show {of(r n) | n} has x as a cluster point (limit along atTop).
  -- of(r n) → x along atTop (in the subtype topology):
  -- For each basic nhd {y | y.val m = x.val m} of x (at coordinate m):
  -- For n ≥ m: of(r n).val m = transition(mkQ_n(r n)) = transition(x.val n) = x.val m.
  -- So eventually (for n ≥ m): of(r n) ∈ the basic nhd.
  -- Hence of(r n) → x.
  -- x ∈ closure(range of) because it's a limit of elements in range(of).
  --
  -- In Lean: use Filter.Tendsto + mem_closure_of_tendsto.
  have htendsto : Filter.Tendsto (fun n => AdicCompletion.of I R (r n))
      Filter.atTop (@nhds _ (adicCompletionUniformSpace I).toTopologicalSpace x) := by
    -- Tendsto in subtype = tendsto of val in Pi = pointwise tendsto.
    -- Use tendsto_subtype_rng: tendsto to subtype iff tendsto of val to Pi.
    rw [Filter.Tendsto]
    simp only [Filter.map_le_iff_le_comap]
    -- Now need: atTop ≤ comap (of ∘ r) (nhds x).
    -- nhds x in the subtype topology = comap val (nhds (val x)) in Pi.
    -- Pull back: comap (val ∘ of ∘ r) (nhds (val x)) in Pi.
    -- In Pi-discrete: this is ⨅ m, comap (eval m ∘ val ∘ of ∘ r) (nhds (val x m)).
    -- For discrete: nhds = pure. So eventually (of(r n)).val m = x.val m.
    rw [Filter.le_def]
    intro U hU
    -- U ∈ comap (of ∘ r) (nhds x). Need U ∈ atTop.
    rw [Filter.mem_comap] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    -- V ∈ nhds x (subtype). Decompose using uniformity basis.
    -- nhds x has basis: ball(x, E) for E ∈ 𝓤.
    -- E ∈ 𝓤(AC) contains {(a,b) | a.val n = b.val n} for some n (from the iInf).
    -- ball(x, E) ⊇ {y | y.val n = x.val n}.
    -- For m ≥ n: (of (r m)).val n = transition(mkQ_m(r m)) = transition(x.val m) = x.val n.
    -- So of(r m) ∈ ball(x, E) ⊆ V for m ≥ n. Hence of(r m) ⁻¹ ∈ V ⁻¹ ⊆ U for m ≥ n.
    -- So U ∈ atTop (eventually for m ≥ n).
    --
    -- To formalize: extract n from V ∈ nhds x using the uniformity + iInf structure.
    -- This is the SAME filter extraction as before.
    -- Let me use nhds_eq_comap_uniformity and then the iInf decomposition.
    rw [@nhds_eq_comap_uniformity _ (adicCompletionUniformSpace I)] at hV
    obtain ⟨E, hE, hEV⟩ := Filter.mem_comap.mp hV
    -- E ∈ 𝓤(AC). Extract finite coordinate set.
    obtain ⟨W, hW, hWE⟩ := Filter.mem_comap.mp hE
    rw [Pi.uniformity] at hW
    obtain ⟨S, hSfin, V_fn, hV_fn, hW_eq⟩ := (Filter.mem_iInf).mp hW
    -- Take n = hSfin.toFinset.sup id
    apply Filter.mem_atTop_sets.mpr
    refine ⟨hSfin.toFinset.sup id, fun m hm => hVU ?_⟩
    apply hEV; apply hWE; rw [hW_eq]; apply Set.mem_iInter.mpr
    intro ⟨i, hi⟩
    obtain ⟨D_i, hD_i, hD_V⟩ := Filter.mem_comap.mp (hV_fn ⟨i, hi⟩)
    apply hD_V
    show (x.val i, (AdicCompletion.of I R (r m)).val i) ∈ D_i
    have hle : i ≤ hSfin.toFinset.sup id :=
      Finset.le_sup (f := id) (hSfin.mem_toFinset.mpr hi)
    have hle_m : i ≤ m := le_trans hle hm
    -- (of (r m)).val i = transition(mkQ_m(r m)) = transition(x.val m) = x.val i
    have heval : (AdicCompletion.of I R (r m)).val i = x.val i := by
      have h1 := (AdicCompletion.of I R (r m)).property hle_m
      have h2 := x.property hle_m
      change AdicCompletion.eval I R i (AdicCompletion.of I R (r m)) = x.val i
      rw [show AdicCompletion.eval I R i (AdicCompletion.of I R (r m)) =
        (AdicCompletion.transitionMap I R hle_m)
          (AdicCompletion.eval I R m (AdicCompletion.of I R (r m))) from h1.symm]
      rw [AdicCompletion.eval_of]
      -- mkQ(r m) = x.val m (by hr), then transition gives x.val i (by h2)
      change (AdicCompletion.transitionMap I R hle_m)
        (Submodule.Quotient.mk (r m)) = x.val i
      rw [hr m, h2]
    rw [heval]; exact refl_mem_uniformity hD_i
  exact mem_closure_of_tendsto htendsto (Filter.Eventually.of_forall
    fun n => Set.mem_range.mpr ⟨r n, rfl⟩)

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
  -- The forward map: compare from AbstractCompletion.
  let e := adicCompletionEquiv I hadic
  let e_inv := adicCompletionEquivInv I hadic
  -- Build ring equiv from the equiv (e is already a homeomorphism from compareEquiv).
  -- Multiplicativity: two continuous maps agree on dense R → agree everywhere.
  -- e(coe r) = of r (by AbstractCompletion.compare_coe).
  -- coe is a ring hom. of is a ring hom (linear map).
  -- So e(coe r * coe s) = e(coe(r * s)) = of(r * s) = of(r) * of(s)
  --  = e(coe r) * e(coe s).
  -- Both (x,y) ↦ e(x*y) and (x,y) ↦ e(x)*e(y) are continuous and agree on dense R×R.
  -- Target (AdicCompletion) is T₂. So they agree everywhere.
  let e := adicCompletionEquiv I hadic
  let e_inv := adicCompletionEquivInv I hadic
  exact {
    toFun := e
    invFun := e_inv
    left_inv := fun x => by
      show e_inv (e x) = x
      exact congr_fun (AbstractCompletion.inverse_compare
        (adicAbstractCompletion I hadic) UniformSpace.Completion.cPkg) x
    right_inv := fun x => by
      show e (e_inv x) = x
      exact congr_fun (AbstractCompletion.inverse_compare
        UniformSpace.Completion.cPkg (adicAbstractCompletion I hadic)) x
    map_mul' := fun x y => by
      -- Double application of Completion.ext (density + T₂).
      -- Step 1: fix y, show (fun x => e(x*y)) = (fun x => e(x)*e(y)) by ext on x.
      -- Step 2: for x = coe(a), show (fun y => e(coe(a)*y)) = (fun y => e(coe(a))*e(y)) by ext on y.
      -- Step 3: for y = coe(b): e(coe(a)*coe(b)) = e(coe(a*b)) = of(a*b) = of(a)*of(b) = e(coe(a))*e(coe(b)).
      haveI : T2Space (AdicCompletion I R) := inferInstance
      -- Need: induction_on₂ + IsClosed (from continuous maps to T₂) + coe case.
      -- The coe case: e(coe(a)*coe(b)) = e(coe(a*b)) = of(a*b) = of(a)*of(b) = e(coe(a))*e(coe(b)).
      -- The instance gap: AbstractCompletion.compare's continuity is between
      -- abstract .space types, not our concrete types. Need to transfer.
      sorry
    map_add' := fun x y => by
      haveI : T2Space (AdicCompletion I R) := inferInstance
      sorry
  }

end Bridge

end AdicCompletionBridge
