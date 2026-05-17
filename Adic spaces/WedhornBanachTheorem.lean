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

/-- **Wedhorn 6.17** = BGR §3.7.2/2. For a complete Tate-like ring `A` and a
complete topological `A`-module `M` with countably-generated uniformity:
`M` is noetherian iff every `A`-submodule of `M` is closed.

In particular, `A` itself is noetherian iff every ideal of `A` is closed.

**Source** (Wedhorn 6.17, p. 49):
> "Let `A` be a complete Tate ring, and let `M` be a complete topological
> `A`-module that has a countable fundamental system of open neighborhoods
> of 0. Then `M` is noetherian if and only if every submodule of `M` is
> closed. In particular `A` is noetherian if and only if every ideal is
> closed."

**Proof outline** (BGR 3.7.2/2):
* (→) Noetherian ⇒ every submodule fg ⇒ closed via Banach OMT applied to a
  surjection from a finite free module (the image is closed because the
  domain is complete and the source surjects onto it through an open quotient).
* (←) Every submodule closed ⇒ ascending chain `M_1 ⊆ M_2 ⊆ …` has closed
  union `M' = ⋃ M_i`. `M'` is a Baire space (complete metrizable). Each `M_i`
  is closed in `M'`, and they cover `M'`, so by Baire some `M_i` has nonempty
  interior in `M'`, hence contains a neighborhood of 0, hence equals `M'`. -/
theorem wedhorn_6_17
    {A : Type u} [Ring A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated]
    {M : Type*} [AddCommGroup M] [Module A M]
      [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated] [T2Space M] :
    IsNoetherian A M ↔ ∀ N : Submodule A M, IsClosed (N : Set M) :=
  sorry

/-- **Wedhorn 6.17 specialised to A itself** — A complete Tate-like noetherian
ring has all ideals closed (and conversely). -/
theorem wedhorn_6_17_ideal
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated] [T2Space A] :
    IsNoetherianRing A ↔ ∀ I : Ideal A, IsClosed (I : Set A) :=
  sorry

/-- **Wedhorn 6.18(1)** = BGR §3.7.3/3. For a complete noetherian Tate ring
`A`, every finitely generated `A`-module `M` admits a complete countably-
generated `A`-module topology, and all such topologies are equivalent (i.e.,
give the same underlying topological space).

**Source** (Wedhorn 6.18(1), p. 50):
> "Every finitely generated `A`-module has a unique `A`-module topology that
> is complete and that has a countable fundamental system of open
> neighborhoods of 0."

**Proof outline** (BGR 3.7.3/3):
* Existence: choose a surjection `π : Aⁿ ↠ M`. The kernel `ker π` is closed
  in `Aⁿ` (by Wedhorn 6.17 applied to `Aⁿ` as `A`-module). The quotient
  topology on `M = Aⁿ / ker π` is then complete and countably-generated
  (quotient of complete by closed is complete; quotient of countably-
  generated uniformity is countably-generated).
* Uniqueness: any two such topologies `τ₁, τ₂` on `M`; the identity
  `id : (M, τ₁) → (M, τ₂)` is A-linear hence (by part (2) below) continuous
  + open ⇒ homeomorphism.

This is stated **non-constructively**: it asserts the existence of a unique
topology without naming it. The downstream consumers will use the
`presheafValue`-style canonical construction. -/
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
  sorry

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
  sorry

end ValuationSpectrum
