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
  AddMonoidHom.isOpenMap_of_completeSpace_of_countablyGenerated f.toAddMonoidHom hf hsurj

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
    CompleteSpace M := by
  -- BGR §3.7.2/1 strategy (completion-embedding):
  -- 1. M ⊆ M̂ := UniformSpace.Completion M, where M̂ is complete + cg + T2.
  -- 2. M̂ inherits Module A structure via UniformSpace.Completion.Module instance.
  -- 3. The image of the n generators in M̂ spans a dense subspace which IS the
  --    image of M in M̂ (since span A {generators} = M algebraically).
  -- 4. Apply wedhorn_6_16 to the canonical A-linear ν̂ : Aⁿ → M̂ (which is
  --    surjective: image is dense + closed since fg + ContinuousSMul on M̂).
  --    For ν̂ surjective we need M̂ to be fg over A — not automatic from
  --    Module.Finite A M; requires Nakayama-style argument that the closure
  --    of finite-span-in-M̂ is finite-span-in-M̂ (i.e., span A {m_i} = M̂ in M̂).
  -- 5. Open ν̂ ⇒ image is open in M̂ ⇒ M open + dense + (M̂ T2) ⇒ M = M̂.
  -- 6. Hence M is complete.
  --
  -- Requires:
  -- - [ContinuousSMul A M] (per BINDING-RULE (b); not yet in hypothesis bundle).
  -- - UniformSpace.Completion M's Module A structure (mathlib instance).
  -- - The closure-span = span argument (Nakayama for fg M̂).
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

/-- **Sub-lemma L3.2-Submodule — Baire chain stationary for Submodules**.

Variant of L3.2 for `Submodule A M` (not `AddSubgroup M`), needed for the
reverse direction of `wedhorn_6_17`. The argument is the same Baire +
absorbing structure but uses the *A-module* scalar action for the
absorbing step: given a chain k₀ with nonempty interior in M_∞ := ⨆ chain
and any m ∈ M_∞, a topologically nilpotent unit π ∈ A satisfies
π^n • m → 0; eventually π^n • m ∈ chain k₀; then m = π^(-n) • (π^n • m) ∈
chain k₀ since chain k₀ is A-stable and π^n is a unit.

Per BINDING-RULE (b): the absorbing argument requires `[IsTateRing A]`
(for topologically nilpotent units) and `[ContinuousSMul A M]` (for
π^n • m → 0). Without these, the conclusion is false (exotic topologies
on M can have all-submodules-closed without M noeth). -/
theorem _sub_lemma_L3_2_baire_chain_submodule
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsTateRing A]
    {M : Type*} [AddCommGroup M] [Module A M]
      [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated] [T2Space M]
      [ContinuousSMul A M]
    (h_all_closed : ∀ N : Submodule A M, IsClosed (N : Set M))
    (chain : ℕ → Submodule A M) (hchain : Monotone chain) :
    ∃ N : ℕ, ∀ n ≥ N, chain n = chain N := by
  -- M_∞ = union of chain (= iSup since monotone).
  set M_inf : Submodule A M := iSup chain with hM_inf_def
  have hk_le_inf : ∀ k, chain k ≤ M_inf := fun k => le_iSup chain k
  -- M_inf is closed (by hypothesis).
  have hM_inf_closed : IsClosed (M_inf : Set M) := h_all_closed M_inf
  -- ↥M_inf inherits subspace structure.
  haveI : IsUniformAddGroup ↥M_inf :=
    show IsUniformAddGroup ↥M_inf.toAddSubgroup from inferInstance
  haveI : (uniformity ↥M_inf).IsCountablyGenerated := Filter.comap.isCountablyGenerated _ _
  haveI : CompleteSpace ↥M_inf := hM_inf_closed.completeSpace_coe
  haveI : T2Space ↥M_inf := inferInstance
  -- Each chain k is closed in M (hypothesis), hence closed in ↥M_inf via preimage.
  have hk_closed_in_inf : ∀ k, IsClosed
      ((Subtype.val : ↥M_inf → M) ⁻¹' (chain k : Set M)) := fun k =>
    (h_all_closed (chain k)).preimage continuous_subtype_val
  -- M_inf = ⋃ k, chain k as Sets of M, via directed iSup (monotone ⇒ directed).
  have h_inf_union : (M_inf : Set M) = ⋃ k, (chain k : Set M) :=
    Submodule.coe_iSup_of_directed _ hchain.directed_le
  -- Lift to ↥M_inf: univ = ⋃ k, (preimage of chain k via Subtype.val).
  have h_subtype_univ :
      ⋃ k, ((Subtype.val : ↥M_inf → M) ⁻¹' (chain k : Set M)) = Set.univ := by
    ext ⟨x, hx⟩
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_univ, iff_true]
    have : x ∈ (M_inf : Set M) := hx
    rw [h_inf_union, Set.mem_iUnion] at this
    exact this
  -- Nonempty witness for C.2.
  haveI : Nonempty ↥M_inf := ⟨⟨0, M_inf.zero_mem⟩⟩
  -- Apply C.2 (Baire): some chain k₀ has nonempty interior in ↥M_inf.
  obtain ⟨k₀, hk₀_int⟩ := AddMonoidHom._sub_sub_lemma_C_2_baire_nonempty_interior
    (fun k => (Subtype.val : ↥M_inf → M) ⁻¹' (chain k : Set M))
    hk_closed_in_inf h_subtype_univ
  -- Extract nbhd of 0 in ↥M_inf inside chain k₀'s preimage via translation.
  obtain ⟨y, hy_int⟩ := hk₀_int
  rw [mem_interior] at hy_int
  obtain ⟨V, hV_sub, hV_open, hy_V⟩ := hy_int
  set V₀ : Set ↥M_inf := (· - y) '' V with hV₀_def
  have hV₀_open : IsOpen V₀ := (Homeomorph.subRight y).isOpenMap _ hV_open
  have h0_V₀ : (0 : ↥M_inf) ∈ V₀ := ⟨y, hy_V, sub_self y⟩
  have hV₀_nhds : V₀ ∈ nhds (0 : ↥M_inf) := hV₀_open.mem_nhds h0_V₀
  -- V₀ ⊆ chain k₀'s preimage (chain k₀ is subgroup-closed).
  have hV₀_sub : V₀ ⊆ (Subtype.val : ↥M_inf → M) ⁻¹' (chain k₀ : Set M) := by
    rintro z ⟨w, hwV, rfl⟩
    show ((w - y : ↥M_inf) : M) ∈ chain k₀
    have hwk : (w : M) ∈ chain k₀ := hV_sub hwV
    have hyk : (y : M) ∈ chain k₀ := hV_sub hy_V
    push_cast
    exact (chain k₀).sub_mem hwk hyk
  -- Establish ContinuousSMul A ↥M_inf via the subspace IsInducing.
  haveI : ContinuousSMul A ↥M_inf := ⟨by
    refine Topology.IsInducing.subtypeVal.continuous_iff.mpr ?_
    exact continuous_smul.comp
      ((continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))⟩
  -- Get topologically nilpotent unit π from IsTateRing.
  obtain ⟨π, hπ_nil⟩ := ‹IsTateRing A›.exists_topologicallyNilpotent_unit
  -- Show M_inf ⊆ chain k₀ via absorption.
  have h_inf_sub : M_inf ≤ chain k₀ := by
    intro m hm
    -- Lift m to ↥M_inf.
    let m_lift : ↥M_inf := ⟨m, hm⟩
    -- π^n • m_lift → 0 in ↥M_inf via ContinuousSMul + π^n → 0.
    have h_pow_tend : Filter.Tendsto (fun n : ℕ => (π : A) ^ n) Filter.atTop (nhds 0) :=
      hπ_nil
    have h_smul_tend :
        Filter.Tendsto (fun n : ℕ => (π : A) ^ n • m_lift) Filter.atTop (nhds 0) := by
      have h0 : (0 : A) • m_lift = 0 := zero_smul A m_lift
      exact h0 ▸ Filter.Tendsto.smul h_pow_tend tendsto_const_nhds
    -- Eventually π^n • m_lift ∈ V₀.
    obtain ⟨N, hN⟩ := (h_smul_tend.eventually hV₀_nhds).exists
    -- π^N • m_lift ∈ V₀ ⊆ chain k₀ preimage.
    have h_lift_in : ((π : A) ^ N • m_lift : ↥M_inf) ∈
        (Subtype.val : ↥M_inf → M) ⁻¹' (chain k₀ : Set M) := hV₀_sub hN
    -- Equivalently π^N • m ∈ chain k₀.
    have h_pi_m_in : (π : A) ^ N • m ∈ chain k₀ := h_lift_in
    -- m = (π^N)⁻¹ • (π^N • m), and chain k₀ is A-stable.
    have hπN_val : ((π ^ N : Aˣ) : A) = (π : A) ^ N := by
      push_cast; rfl
    have hmem : (((π ^ N : Aˣ)⁻¹ : Aˣ) : A) • ((π : A) ^ N • m) ∈ chain k₀ :=
      (chain k₀).smul_mem _ h_pi_m_in
    have h_eq : m = (((π ^ N : Aˣ)⁻¹ : Aˣ) : A) • ((π : A) ^ N • m) := by
      rw [← smul_assoc, smul_eq_mul, ← hπN_val, ← Units.val_mul]
      simp
    rw [h_eq]
    exact hmem
  -- M_inf = chain k₀ (both directions: ⊆ from h_inf_sub, ⊇ from hk_le_inf).
  have h_inf_eq : M_inf = chain k₀ := le_antisymm h_inf_sub (hk_le_inf k₀)
  -- For n ≥ k₀: chain n ≤ M_inf = chain k₀, and chain k₀ ≤ chain n by monotone.
  refine ⟨k₀, fun n hn => le_antisymm ?_ (hchain hn)⟩
  rw [h_inf_eq] at hk_le_inf
  exact hk_le_inf n

theorem wedhorn_6_17
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated] [IsNoetherianRing A]
      [IsTopologicalRing A] [IsTateRing A]
    {M : Type*} [AddCommGroup M] [Module A M]
      [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated] [T2Space M]
      [ContinuousSMul A M] :
    IsNoetherian A M ↔ ∀ N : Submodule A M, IsClosed (N : Set M) := by
  constructor
  · -- Forward: every submodule fg + L3.1b ⇒ every submodule closed.
    intro hM N
    have hN_fg : N.FG := IsNoetherian.noetherian (R := A) N
    exact _sub_lemma_L3_1b_fg_submodule_closed N hN_fg
  · -- Reverse: chain stationary via L3.2 Submodule variant.
    intro h_all_closed
    rw [isNoetherian_iff', wellFoundedGT_iff_monotone_chain_condition]
    intro chain
    obtain ⟨N, hN⟩ := _sub_lemma_L3_2_baire_chain_submodule h_all_closed
      (fun n => chain n) chain.monotone
    exact ⟨N, fun m hm => (hN m hm).symm⟩

/-- **Wedhorn 6.17 specialised to A itself** — A complete Tate-like noetherian
ring has all ideals closed (and conversely). -/
theorem wedhorn_6_17_ideal
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated] [T2Space A]
      [IsTopologicalRing A] [IsTateRing A] :
    IsNoetherianRing A ↔ ∀ I : Ideal A, IsClosed (I : Set A) := by
  -- Specialise wedhorn_6_17 to M = A. Need [IsNoetherianRing A] for forward
  -- direction, but here it appears as iff LHS. Split into two directions.
  constructor
  · intro hA
    haveI : IsNoetherianRing A := hA
    exact (wedhorn_6_17 (A := A) (M := A)).mp hA
  · intro h_all
    -- Reverse: derive IsNoetherian A A from chain stationarity via L3.2 Submodule.
    show IsNoetherian A A
    rw [isNoetherian_iff', wellFoundedGT_iff_monotone_chain_condition]
    intro chain
    obtain ⟨N, hN⟩ := _sub_lemma_L3_2_baire_chain_submodule h_all
      (fun n => chain n) chain.monotone
    exact ⟨N, fun m hm => (hN m hm).symm⟩

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
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated] [T2Space M]
      [ContinuousSMul A M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
      [UniformSpace N] [IsUniformAddGroup N]
      [CompleteSpace N] [(uniformity N).IsCountablyGenerated] [T2Space N]
      [ContinuousSMul A N]
    (f : M →ₗ[A] N) :
    Continuous f := by
  -- BGR §3.7.3/2 proof.
  -- Pick a finite generating set s : Fin n → M.
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
  -- Define ν : (Fin n → A) →ₗ[A] M by ν a = ∑ i, a i • s i.
  let ν : (Fin n → A) →ₗ[A] M :=
    { toFun := fun a => ∑ i, a i • s i
      map_add' := fun x y => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun a x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum,
          smul_smul] }
  -- ν continuous via ContinuousSMul A M.
  have hν_cont : Continuous ν := by
    change Continuous fun a : (Fin n → A) => ∑ i, a i • s i
    refine continuous_finset_sum _ ?_
    intro i _
    exact (continuous_apply i).smul continuous_const
  -- ν surjective from hs.
  have hν_surj : Function.Surjective ν := by
    intro m
    have hm : m ∈ Submodule.span A (Set.range s) := hs ▸ Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hm
    obtain ⟨c, hc⟩ := hm
    exact ⟨c, hc⟩
  -- By wedhorn_6_16, ν is open. (Needs T2Space M on target — supplied.)
  have hν_open : IsOpenMap ν := wedhorn_6_16 ν hν_cont hν_surj
  -- ν is a quotient map.
  have hν_quot : Topology.IsQuotientMap ν := hν_open.isQuotientMap hν_cont hν_surj
  -- f ∘ ν continuous via ContinuousSMul A N.
  have hfν_cont : Continuous (f ∘ ν) := by
    change Continuous fun a : (Fin n → A) => f (∑ i, a i • s i)
    simp only [map_sum, map_smul]
    refine continuous_finset_sum _ ?_
    intro i _
    exact (continuous_apply i).smul continuous_const
  -- f continuous via quotient map.
  exact hν_quot.continuous_iff.mpr hfν_cont

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
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated] [T2Space M]
      [ContinuousSMul A M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
      [UniformSpace N] [IsUniformAddGroup N]
      [CompleteSpace N] [(uniformity N).IsCountablyGenerated] [T2Space N]
      [ContinuousSMul A N]
    (f : M →ₗ[A] N) :
    IsOpenMap (Set.rangeFactorization f) := by
  -- BGR §3.7.3/Cor 5: f.range is fg (image of fg under linear map), so closed in
  -- N by L3.1b. Then ↥(f.range) inherits a complete T2 cg uag subspace structure,
  -- and wedhorn_6_16 applied to f.rangeRestrict (= f viewed as map to its range)
  -- gives openness. Set.rangeFactorization = f.rangeRestrict up to type identity.
  --
  -- Step 1: f.range as Submodule A N is fg (image of ⊤ under f, which is fg).
  have htop_fg : (⊤ : Submodule A M).FG := Module.Finite.fg_top
  have hrange_fg : (LinearMap.range f).FG := by
    rw [LinearMap.range_eq_map]
    exact htop_fg.map f
  -- Step 2: f.range is closed via L3.1b.
  have hrange_closed : IsClosed (LinearMap.range f : Set N) :=
    _sub_lemma_L3_1b_fg_submodule_closed (LinearMap.range f) hrange_fg
  -- Step 3: subspace typeclass setup on ↥f.range.
  haveI : IsUniformAddGroup ↥(LinearMap.range f) :=
    show IsUniformAddGroup ↥(LinearMap.range f).toAddSubgroup from inferInstance
  haveI : (uniformity ↥(LinearMap.range f)).IsCountablyGenerated :=
    Filter.comap.isCountablyGenerated _ _
  haveI : CompleteSpace ↥(LinearMap.range f) :=
    hrange_closed.completeSpace_coe
  haveI : T2Space ↥(LinearMap.range f) :=
    inferInstance  -- Subtype T2 from T2 N
  haveI : Module.Finite A ↥(LinearMap.range f) :=
    (Module.Finite.iff_fg (N := LinearMap.range f)).mpr hrange_fg
  -- ContinuousSMul on subspace: A × ↥range → ↥range factors through
  -- A × N → N via Subtype.val on the codomain.
  haveI : ContinuousSMul A ↥(LinearMap.range f) := by
    refine ⟨?_⟩
    -- Continuous fun p : A × ↥(LinearMap.range f) => p.1 • p.2 : ↥(LinearMap.range f)
    -- Equivalently, Continuous of (a, x) ↦ ⟨a • x.1, ...⟩.
    -- Use IsInducing.continuous_iff: Subtype.val of the SMul output is the
    -- continuous SMul A × N → N restricted.
    rw [show (fun p : A × ↥(LinearMap.range f) => p.1 • p.2) =
        fun p => ⟨p.1 • (p.2 : N), Submodule.smul_mem _ p.1 p.2.2⟩ from rfl]
    refine Topology.IsInducing.subtypeVal.continuous_iff.mpr ?_
    exact continuous_smul.comp ((continuous_fst).prodMk
      ((continuous_subtype_val.comp continuous_snd)))
  -- Now apply wedhorn_6_16 to f.rangeRestrict.
  have hf_rangeRestrict_cont : Continuous (f.rangeRestrict : M →ₗ[A] LinearMap.range f) := by
    -- f.rangeRestrict composed with Subtype.val = f, so by inducing, f.rangeRestrict
    -- continuous iff f continuous.
    refine Topology.IsInducing.subtypeVal.continuous_iff.mpr ?_
    -- Subtype.val ∘ f.rangeRestrict = f (definitionally)
    exact _sub_lemma_L4_2_continuous_via_OMT f
  have hf_rangeRestrict_surj : Function.Surjective f.rangeRestrict :=
    LinearMap.surjective_rangeRestrict f
  -- wedhorn_6_16 gives IsOpenMap (f.rangeRestrict).
  have hf_rangeRestrict_open : IsOpenMap f.rangeRestrict :=
    wedhorn_6_16 f.rangeRestrict hf_rangeRestrict_cont hf_rangeRestrict_surj
  -- Convert: Set.rangeFactorization f and f.rangeRestrict are defeq as functions
  -- M → ↥(LinearMap.range f) (via Set.range f = LinearMap.range f as Set N).
  convert hf_rangeRestrict_open using 1

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
    (h_csmul_1 : @ContinuousSMul A M _ _ τ₁.toTopologicalSpace)
    (h_top2 : @IsUniformAddGroup M τ₂ _)
    (h_complete2 : @CompleteSpace M τ₂)
    (h_cg2 : (@uniformity M τ₂).IsCountablyGenerated)
    (h_t2_2 : @T2Space M τ₂.toTopologicalSpace)
    (h_csmul_2 : @ContinuousSMul A M _ _ τ₂.toTopologicalSpace) :
    τ₁.toTopologicalSpace = τ₂.toTopologicalSpace := by
  -- Apply L4.2 twice with the identity map in each direction.
  have h12 : @Continuous M M τ₁.toTopologicalSpace τ₂.toTopologicalSpace id :=
    @_sub_lemma_L4_2_continuous_via_OMT _ _ _ _ _ _ _
      M _ _ _ τ₁ h_top1 h_complete1 h_cg1 h_t2_1 h_csmul_1
      M _ _ _ τ₂ h_top2 h_complete2 h_cg2 h_t2_2 h_csmul_2 (LinearMap.id (R := A) (M := M))
  have h21 : @Continuous M M τ₂.toTopologicalSpace τ₁.toTopologicalSpace id :=
    @_sub_lemma_L4_2_continuous_via_OMT _ _ _ _ _ _ _
      M _ _ _ τ₂ h_top2 h_complete2 h_cg2 h_t2_2 h_csmul_2
      M _ _ _ τ₁ h_top1 h_complete1 h_cg1 h_t2_1 h_csmul_1 (LinearMap.id (R := A) (M := M))
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
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated] [T2Space M]
      [ContinuousSMul A M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
      [UniformSpace N] [IsUniformAddGroup N]
      [CompleteSpace N] [(uniformity N).IsCountablyGenerated] [T2Space N]
      [ContinuousSMul A N]
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
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated] [T2Space M]
      [ContinuousSMul A M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
      [UniformSpace N] [IsUniformAddGroup N]
      [CompleteSpace N] [(uniformity N).IsCountablyGenerated] [T2Space N]
      [ContinuousSMul A N]
    (f : M →ₗ[A] N) :
    IsOpenMap (Set.rangeFactorization f) :=
  -- Direct citation of L4.3 (same statement).
  _sub_lemma_L4_3_strict_via_closed_image f

end ValuationSpectrum
