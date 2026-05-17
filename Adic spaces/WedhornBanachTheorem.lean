/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».BanachOMT
import «Adic spaces».HuberRings
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Wedhorn §6.3 — Banach's theorem for Tate rings

This file ports the three results in Wedhorn §6.3 (arXiv:1910.05934, pp. 49-50)
that Wedhorn marks "Proof. Missing", referring out to Huber [Hu3] Lemma 2.4 and
BGR §3.7. Specifically:

* **Wedhorn 6.16** — Banach's open mapping for topological A-modules over a
  Tate-like ring (= Huber [Hu3] Lemma 2.4(i) = direct corollary of
  `AddMonoidHom.isOpenMap_of_completeSpace_of_countablyGenerated`).
* **Wedhorn 6.17** — noetherian ⇔ every submodule (resp. ideal) is closed
  (= BGR §3.7.2/2, applied via Wedhorn 6.16).
* **Wedhorn 6.18** — for a complete noetherian Tate ring `A`, every finitely
  generated `A`-module has a unique complete countably-generated `A`-module
  topology; A-linear maps between such modules are continuous and open onto
  image (= BGR §3.7.3/2 + 3.7.3/3 + Corollary 5).

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934, §6.3 "Banach's theorem for Tate
  rings", pp. 49-50 (statements; proofs marked "Missing").
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*,
  Math. Z. 217 (1994), Lemma 2.4 (p. 16).
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis* (Springer 1984),
  §3.7.2/2 (p. 164), §3.7.3/2 + §3.7.3/3 (p. 164), §3.7.3/Cor 5 (p. 165).

## Roadmap

See `docs/plans/2026-05-17-wedhorn-618-roadmap.md` for the full layered plan,
source quotes, and Lean ↔ source match analysis.
-/

namespace ValuationSpectrum

universe u

/-- **Wedhorn 6.16** = Huber [Hu3] Lemma 2.4(i). Banach's open mapping theorem
applied to topological A-modules over a Tate-like ring.

Let `A` be a topological ring containing a sequence converging to 0 consisting
of units (in particular, any Tate ring). Let `M, N` be Hausdorff topological
`A`-modules with countably-generated uniformities, both complete. Then every
continuous surjective `A`-linear map `f : M →ₗ[A] N` is open.

This is the direct corollary of the underlying group-level
`AddMonoidHom.isOpenMap_of_completeSpace_of_countablyGenerated`: an A-linear
map is in particular an additive group homomorphism, and the group-level
result depends only on the group structure (the A-module structure is
inessential — Huber notes this explicitly).

**Source** (Wedhorn 6.16, p. 49):
> "Let `A` be a topological ring that has a sequence converging to 0
> consisting of units of `A` (e.g., if `A` is a Tate ring). Let `M` and `N`
> be Hausdorff topological `A`-modules that have countable fundamental systems
> of open neighborhoods of 0. Assume that `M` is complete. Let `u : M → N` be
> an `A`-linear map. Consider the following properties: (a) `N` is complete;
> (b) `u` is surjective; (c) `u` is open. Then any two of these properties
> imply the third." -/
theorem wedhorn_6_16
    {A : Type u} [Ring A]
    {M : Type*} [AddCommGroup M] [Module A M]
      [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated]
    {N : Type*} [AddCommGroup N] [Module A N]
      [UniformSpace N] [IsUniformAddGroup N]
      [CompleteSpace N] [(uniformity N).IsCountablyGenerated] [T2Space N]
    (f : M →ₗ[A] N) (hf : Continuous f) (hsurj : Function.Surjective f) :
    IsOpenMap f :=
  -- Apply the group-level Banach OMT to f.toAddMonoidHom.
  -- The A-linearity is not needed for openness (only the group hom structure).
  sorry

/-! ## Wedhorn 6.17 (= BGR §3.7.2/2) — noetherian iff every (sub)module closed

For a complete Tate-like ring `A` and a complete topological `A`-module `M`
with countably-generated uniformity: `M` is noetherian iff every `A`-submodule
of `M` is closed. In particular, `A` itself is noetherian iff every ideal is closed.

**Source** (Wedhorn 6.17, p. 49):
> "Let `A` be a complete Tate ring, and let `M` be a complete topological
> `A`-module that has a countable fundamental system of open neighborhoods
> of 0. Then `M` is noetherian if and only if every submodule of `M` is
> closed. In particular `A` is noetherian if and only if every ideal is
> closed."

**Proof outline** (BGR 3.7.2/2):
* (→) Noetherian ⇒ every submodule fg ⇒ closed: this is BGR 3.7.2/1 + observation.
* (←) Every submodule closed ⇒ ascending chain `M_1 ⊆ M_2 ⊆ …` has closed
  union `M' = ⋃ M_i`. `M'` is a Baire space; by Baire some `M_i` has nonempty
  interior in `M'`, hence equals `M'`.

### Layer 3 sub-lemmas (L3.1a, L3.1b, L3.2) -/

/-- **Sub-lemma L3.1a — BGR §3.7.2/1: completion of fg normed module is module itself**.

**Source** (BGR §3.7.2/1, p. 163, verbatim):
> "Proposition 1. Let A be a k-Banach algebra and let M be a normed A-module
> such that the completion M̂ of M is a finite A-module. Then M is complete.
> Proof. There are elements x_1, ..., x_n ∈ M̂ such that the homomorphism
> π : A^n → M̂ defined by π(a_1, ..., a_n) := Σᵢ aᵢxᵢ is surjective. By
> BANACH's Theorem, π is open, and therefore Σᵢ Ãx_i = π(Ãⁿ) is a neighborhood
> of 0 in M̂. Since M is dense in M̂, we have x_v ∈ M + Σᵤ Ãx_μ for v = 1, ..., n.
> Now NAKAYAMA's Lemma 1.2.4/6 yields M = M̂."

**Lean statement**: A normed A-module M whose completion `M̂` is finite as A-module
is itself complete (= already equals its completion).

**Discharge route**: `wedhorn_6_16` (Banach OMT for A-modules, Layer 2) +
Nakayama's lemma (mathlib: `Submodule.eq_of_le_of_finrank_eq` style; or direct
via `Module.eq_top_iff` + finiteness).

**Difficulty**: MEDIUM. ~50 lines. The Banach OMT input is the substantive part. -/
theorem _sub_lemma_L3_1a_completion_fg_complete
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated]
    {M : Type*} [AddCommGroup M] [Module A M]
      [UniformSpace M] [IsUniformAddGroup M]
      [(uniformity M).IsCountablyGenerated] [T2Space M]
    (hM_fg : Module.Finite A M) :
    CompleteSpace M :=
  sorry

/-- **Sub-lemma L3.1b — fg submodule of complete noeth module is closed**.

Direct corollary of L3.1a applied to the submodule N ⊆ M (with N inheriting
the subspace uniformity from M). The completion `N̂` is fg (= `Module.Finite A N`
when A noeth + N fg over A, by Hilbert), so N is complete, so N is closed in M.

**Discharge**: L3.1a + `IsClosed.of_completeSpace` (for closed subset of T2 space,
complete subspace is closed).

**Difficulty**: EASY. ~25 lines. -/
theorem _sub_lemma_L3_1b_fg_submodule_closed
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M]
      [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated] [T2Space M]
    (N : Submodule A M) (hN_fg : N.FG) :
    IsClosed (N : Set M) := by
  -- ↥N inherits subspace uniform structure from M.
  haveI : IsUniformAddGroup ↥N :=
    show IsUniformAddGroup ↥N.toAddSubgroup from inferInstance
  haveI : (uniformity ↥N).IsCountablyGenerated := Filter.comap.isCountablyGenerated _ _
  haveI : Module.Finite A ↥N := (Module.Finite.iff_fg (N := N)).mpr hN_fg
  -- L3.1a gives CompleteSpace ↥N for the fg subspace.
  haveI : CompleteSpace ↥N := _sub_lemma_L3_1a_completion_fg_complete (A := A) (M := ↥N)
    inferInstance
  -- Complete subset of T2 ambient ⇒ closed.
  exact (completeSpace_coe_iff_isComplete.mp ‹CompleteSpace ↥N›).isClosed

/-- **Sub-lemma L3.2 — Baire chain stationary**.

**Source** (BGR §3.7.2/2 proof, p. 164, verbatim):
> "We only have to show that M is Noetherian if all submodules are closed. Let
> M_1 ⊂ M_2 ⊂ … be an ascending chain of submodules. Let M' := ⋃_{i=1}^∞ M_i.
> Then M' being a closed submodule of the complete module M is a Baire space.
> Since all M_i are closed, we have by BAIRE's Theorem (cf. BOURBAKI [6], Ch 9,
> §5, Théorème 1) the existence of an index i such that M_i contains a
> neighborhood of 0 in M'. This implies M_i = M'; hence the chain becomes
> stationary."

**Lean statement**: in a complete metric topological add group where every
additive subgroup is closed, every ascending chain of subgroups is stationary.

**Discharge route**: `nonempty_interior_of_iUnion_of_closed` (mathlib Baire) +
`AddSubgroup.isOpen_of_zero_mem_interior` (open subgroup = whole closed thing).

**Difficulty**: MEDIUM. ~50 lines. -/
theorem _sub_lemma_L3_2_baire_chain
    {M : Type*} [AddCommGroup M]
      [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated] [T2Space M]
    (h_all_closed : ∀ N : AddSubgroup M, IsClosed (N : Set M))
    (chain : ℕ → AddSubgroup M) (hchain : Monotone chain) :
    ∃ N : ℕ, ∀ n ≥ N, chain n = chain N :=
  sorry

theorem wedhorn_6_17
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M]
      [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated] [T2Space M] :
    IsNoetherian A M ↔ ∀ N : Submodule A M, IsClosed (N : Set M) := by
  constructor
  · -- Forward: every submodule fg + L3.1b ⇒ every submodule closed.
    intro hM N
    have hN_fg : N.FG := IsNoetherian.noetherian (R := A) N
    exact _sub_lemma_L3_1b_fg_submodule_closed N hN_fg
  · -- Reverse: every submodule closed ⇒ chain stationary ⇒ noeth.
    -- Requires a Submodule version of L3.2 (Baire chain stationary). The current
    -- L3.2 is at AddSubgroup level; lifting it to Submodule requires showing
    -- that every Submodule's underlying AddSubgroup is closed — which holds
    -- (hypothesis), but the chain's AddSubgroup may not faithfully recover
    -- the original Submodule chain without extra scalar-mult structure on the
    -- ambient AddSubgroup. Left sorried pending Submodule-level L3.2 variant.
    sorry

/-- **Wedhorn 6.17 specialised to A itself** — A complete Tate-like noetherian
ring has all ideals closed (and conversely). -/
theorem wedhorn_6_17_ideal
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated] [T2Space A] :
    IsNoetherianRing A ↔ ∀ I : Ideal A, IsClosed (I : Set A) := by
  -- Specialise wedhorn_6_17 to M = A. Need [IsNoetherianRing A] for forward
  -- direction, but here it appears as iff LHS. Split into two directions.
  constructor
  · intro hA
    -- Forward: derive [IsNoetherianRing A] as instance, then cite wedhorn_6_17.
    haveI : IsNoetherianRing A := hA
    exact (wedhorn_6_17 (A := A) (M := A)).mp hA
  · intro h_all
    -- Reverse: use wedhorn_6_17's reverse direction. But it requires
    -- [IsNoetherianRing A] as instance to invoke — circular for reverse.
    -- Instead, use the underlying L3.2 directly; left sorried alongside L3.2.
    sorry

/-! ## Wedhorn 6.18 (= BGR §3.7.3) — unique fg-module topology + maps strict

For a complete noetherian Tate ring `A`, every finitely generated `A`-module
has a unique complete countably-generated A-module topology; A-linear maps
between such modules are continuous and open onto image.

**Source** (Wedhorn 6.18, p. 50):
> "Every finitely generated `A`-module has a unique `A`-module topology that
> is complete and that has a countable fundamental system of open
> neighborhoods of 0. Let `f : M → N` be an `A`-linear map of finitely
> generated modules that are endowed with the topology from (1). Then `f`
> is continuous and the map `f : M → f(M)` is open."

**Decomposition into sub-lemmas L4.1–L4.4**: see below.

### Layer 4 sub-lemmas (Wedhorn 6.18 — BGR §3.7.3) -/

/-- **Sub-lemma L4.1 — Quotient of complete countably-generated is complete countably-generated**.

For a closed subgroup K ⊆ M with M complete + countably-generated uniformity,
the quotient M/K (with quotient topology) is also complete + countably-generated.

**Source**: standard topological group fact. Mathlib has
`AddSubgroup.QuotientAddGroup.CompleteSpace`-style instances.

**Mathlib search**:
- `Quotient.completeSpace` for quotients of complete uniform spaces.
- `Quotient.uniformContinuous_mk` for quotient map continuity.

**Difficulty**: EASY-MEDIUM. ~30 lines. Mostly assembling existing instances. -/
theorem _sub_lemma_L4_1_quotient_complete
    {A : Type u} [Ring A]
    {M : Type*} [AddCommGroup M] [Module A M]
      [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated] [T2Space M]
    (K : Submodule A M) (_hK_closed : IsClosed (K : Set M)) :
    -- Existential: there exists a uniformity on M ⧸ K making the quotient
    -- map continuous + the quotient complete + countably-generated.
    -- (The canonical quotient uniformity from K.toAddSubgroup; existence stated
    -- here, instance derivation done at use site.)
    ∃ (τ : UniformSpace (M ⧸ K)),
      @IsUniformAddGroup _ τ _ ∧
      @CompleteSpace _ τ ∧
      (@uniformity _ τ).IsCountablyGenerated := by
  -- M is first-countable from countably-generated uniformity (mathlib instance)
  haveI : FirstCountableTopology M := UniformSpace.firstCountableTopology M
  -- Quotient is first-countable (mathlib instance, needs explicit subgroup arg)
  haveI : FirstCountableTopology (M ⧸ K) :=
    QuotientAddGroup.instFirstCountableTopology K.toAddSubgroup
  -- Take τ := canonical right uniform space from the topological additive group structure.
  letI τ : UniformSpace (M ⧸ K) := IsTopologicalAddGroup.rightUniformSpace (M ⧸ K)
  refine ⟨τ, ?_, ?_, ?_⟩
  · -- IsUniformAddGroup via abelian-group lemma
    exact isUniformAddGroup_of_addCommGroup
  · -- CompleteSpace: use mathlib's QuotientAddGroup.completeSpace_right instance.
    -- With τ in scope as the default UniformSpace, inferInstance finds it.
    exact QuotientAddGroup.completeSpace_right M K.toAddSubgroup
  · -- IsCountablyGenerated via IsUniformAddGroup.uniformity_countably_generated;
    -- needs IsUniformAddGroup w.r.t. our chosen τ + IsCountablyGenerated (𝓝 0).
    haveI : @IsUniformAddGroup (M ⧸ K) τ _ := isUniformAddGroup_of_addCommGroup
    exact IsUniformAddGroup.uniformity_countably_generated

/-- **Sub-lemma L4.2 — A-linear map between fg modules is continuous**.

**Source** (BGR §3.7.3/2, p. 164, verbatim):
> "Proposition 2. If M, M' are objects of 𝔐_A, each A-linear map φ : M → M' is
> continuous. Proof. Choose an epimorphism π : A^n ↠ M for a suitable n ∈ ℕ.
> Define φ' : A^n → M' by φ' := φ ∘ π. Since addition and scalar multiplication
> are continuous operations in normed modules, both maps π and φ' are continuous.
> Furthermore π is open (by BANACH's Theorem). Hence φ is continuous."

**Lean statement**: identical to `wedhorn_6_18_continuous` below.

**Discharge route**:
- Choose surjection π : A^n ↠ M (via `Module.Finite`).
- π is continuous (sum of coordinate projections × x_i, all continuous in normed
  modules — uses `IsUniformAddGroup` continuity of add + smul).
- π is open by `wedhorn_6_16` (Layer 2).
- φ ∘ π is continuous (composition).
- φ = (φ ∘ π) ∘ π⁻¹ where π⁻¹ is the quotient map (well-defined via open π).

**Difficulty**: MEDIUM. ~60 lines. -/
theorem _sub_lemma_L4_2_continuous_via_OMT
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated] [T2Space A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
      [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
      [UniformSpace N] [IsUniformAddGroup N]
      [CompleteSpace N] [(uniformity N).IsCountablyGenerated] [T2Space N]
    (f : M →ₗ[A] N) :
    Continuous f :=
  sorry

/-- **Sub-lemma L4.3 — A-linear map is open onto image (strict)**.

**Source** (BGR §3.7.3/Proposition 4, p. 165, verbatim):
> "Proposition 4. A continuous k-linear map φ : X → Y between k-Banach spaces is
> strict if and only if φ(X) is closed in Y. From this we immediately conclude
> Corollary 5. Each A-module homomorphism φ : M → M', where M, M' ∈ 𝔐_A, is strict."

**Lean statement**: the rangeFactorization of f is open.

**Discharge route**:
- f continuous by L4.2.
- Image f(M) is fg submodule of N (since M fg + linear map), hence closed by
  Wedhorn 6.17 forward direction (or directly L3.1b).
- Image with subspace topology = quotient topology by Banach OMT (Layer 2,
  applied to the rangeFactorization which is surjective onto its image).

**Difficulty**: MEDIUM. ~50 lines. -/
theorem _sub_lemma_L4_3_strict_via_closed_image
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated] [T2Space A]
      [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
      [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
      [UniformSpace N] [IsUniformAddGroup N]
      [CompleteSpace N] [(uniformity N).IsCountablyGenerated] [T2Space N]
    (f : M →ₗ[A] N) :
    IsOpenMap (Set.rangeFactorization f) :=
  sorry

/-- **Sub-lemma L4.4 — Uniqueness of complete countably-generated A-module topology**.

If τ₁ and τ₂ are two uniform structures on M (both making M into a complete
countably-generated A-module), then they induce the SAME topology.

**Discharge route**: apply L4.2 (continuity of A-linear maps) to id_M in
both directions:
- id : (M, τ₁) → (M, τ₂) is A-linear (trivially) ⇒ continuous by L4.2 ⇒ τ₂ ≤ τ₁.
- id : (M, τ₂) → (M, τ₁) similarly ⇒ τ₁ ≤ τ₂.
- Hence τ₁ = τ₂.

**Difficulty**: EASY. ~25 lines. -/
theorem _sub_lemma_L4_4_unique_topology
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated] [T2Space A]
      [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (τ₁ τ₂ : UniformSpace M)
    (h_top1 : @IsUniformAddGroup M τ₁ _)
    (h_complete1 : @CompleteSpace M τ₁)
    (h_cg1 : (@uniformity M τ₁).IsCountablyGenerated)
    (h_t2_1 : @T2Space M τ₁.toTopologicalSpace)
    (h_top2 : @IsUniformAddGroup M τ₂ _)
    (h_complete2 : @CompleteSpace M τ₂)
    (h_cg2 : (@uniformity M τ₂).IsCountablyGenerated)
    (h_t2_2 : @T2Space M τ₂.toTopologicalSpace) :
    τ₁.toTopologicalSpace = τ₂.toTopologicalSpace := by
  -- Apply L4.2 twice with the identity map in each direction.
  -- id : (M, τ₁) → (M, τ₂) is A-linear and continuous (by L4.2 with codomain τ₂),
  -- giving τ₂.top ≤ τ₁.top. Symmetric for the reverse.
  have h12 : @Continuous M M τ₁.toTopologicalSpace τ₂.toTopologicalSpace id :=
    @_sub_lemma_L4_2_continuous_via_OMT _ _ _ _ _ _ _
      M _ _ _ τ₁ h_top1 h_complete1 h_cg1
      M _ _ _ τ₂ h_top2 h_complete2 h_cg2 h_t2_2 (LinearMap.id (R := A) (M := M))
  have h21 : @Continuous M M τ₂.toTopologicalSpace τ₁.toTopologicalSpace id :=
    @_sub_lemma_L4_2_continuous_via_OMT _ _ _ _ _ _ _
      M _ _ _ τ₂ h_top2 h_complete2 h_cg2
      M _ _ _ τ₁ h_top1 h_complete1 h_cg1 h_t2_1 (LinearMap.id (R := A) (M := M))
  -- Two-sided continuity of id is equivalent to topology equality.
  exact le_antisymm (continuous_id_iff_le.mp h12) (continuous_id_iff_le.mp h21)

theorem wedhorn_6_18_unique
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated] [T2Space A]
      [IsNoetherianRing A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ (τ : UniformSpace M),
      @IsUniformAddGroup M τ _ ∧
      @CompleteSpace M τ ∧
      (uniformity M).IsCountablyGenerated ∧
      ∀ (τ' : UniformSpace M),
        @IsUniformAddGroup M τ' _ →
        @CompleteSpace M τ' →
        (@uniformity M τ').IsCountablyGenerated →
        τ.toTopologicalSpace = τ'.toTopologicalSpace :=
  sorry

/-- **Wedhorn 6.18(2) — continuity part** = BGR §3.7.3/2. For a complete
noetherian Tate ring `A` and two finitely generated `A`-modules `M, N`
equipped with their (unique by 6.18(1)) complete countably-generated
topologies, every `A`-linear map `f : M → N` is continuous.

**Source** (Wedhorn 6.18(2), p. 50, first half):
> "Let `f : M → N` be an `A`-linear map of finitely generated modules that
> are endowed with the topology from (1). Then `f` is continuous..."

**Proof outline** (BGR 3.7.3/2):
* Choose epi `π : Aⁿ ↠ M`. The composite `f ∘ π : Aⁿ → N` is `A`-linear
  hence continuous (sum of coordinate projections, each multiplied by the
  image vectors `f(eᵢ)`).
* By Wedhorn 6.16, `π` is open (continuous surjective between complete
  metric A-modules). Hence `f = (f ∘ π) ∘ π⁻¹` is continuous (where `π⁻¹`
  uses the quotient topology). -/
theorem wedhorn_6_18_continuous
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated] [T2Space A]
      [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
      [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
      [UniformSpace N] [IsUniformAddGroup N]
      [CompleteSpace N] [(uniformity N).IsCountablyGenerated] [T2Space N]
    (f : M →ₗ[A] N) :
    Continuous f :=
  -- Direct citation of L4.2 (same statement).
  _sub_lemma_L4_2_continuous_via_OMT f

/-- **Wedhorn 6.18(2) — open onto image part** = BGR §3.7.3/Corollary 5.
For a complete noetherian Tate ring `A` and two finitely generated `A`-modules
`M, N` equipped with their topologies from 6.18(1), every `A`-linear
`f : M → N` is **strict** (= the image with subspace topology equals the
quotient topology), equivalently, `f : M → f(M)` is open.

**Source** (Wedhorn 6.18(2), p. 50, second half):
> "...and the map `f : M → f(M)` is open."

**Proof outline** (BGR 3.7.3/Cor 5 via Prop 4):
* `f` is continuous by `wedhorn_6_18_continuous`.
* Image `f(M)` is a finitely generated submodule of `N`, hence closed by
  Wedhorn 6.17.
* A continuous A-linear map between complete metric A-modules is strict iff
  its image is closed (BGR 3.7.3/Prop 4, via Banach OMT).
* Hence `f` is strict; equivalently, `f : M → f(M)` is open. -/
theorem wedhorn_6_18_open_onto_image
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated] [T2Space A]
      [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
      [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
      [UniformSpace N] [IsUniformAddGroup N]
      [CompleteSpace N] [(uniformity N).IsCountablyGenerated] [T2Space N]
    (f : M →ₗ[A] N) :
    IsOpenMap (Set.rangeFactorization f) :=
  -- Direct citation of L4.3 (same statement).
  _sub_lemma_L4_3_strict_via_closed_image f

end ValuationSpectrum
