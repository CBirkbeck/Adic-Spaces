/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».ValuationSpectrumCompact
import «Adic spaces».AdicSpectrum

/-!
# Compactness of the Adic Spectrum `Spa(A, A⁺)`

We derive quasi-compactness of the adic spectrum `Spa(A, A⁺)` from the corresponding
statement for the full valuation spectrum `Spv A` (see
`ValuationSpectrum.instCompactSpace` in `ValuationSpectrumCompact.lean`).

## Route taken

Unlike `Spv A`, the set `Spa A A⁺ = Cont A ∩ ⋂_{a ∈ A⁺} {v | v.vle a 1}` is **not**
closed in `Spv A` in general: each `{v | v.vle a 1}` equals the **open** set
`basicOpen a 1` (since `¬ v.vle 1 0` always holds), and the continuity condition
`v.IsContinuous` is not in general a closed condition either. So the naive
"closed-in-compact" route does not work directly through the `Spv A` topology.

We therefore proceed through the Bool Huber embedding
`ιSpv_bool : Spv A → (A × A → Bool)`. In the discrete Bool product:

* each coordinate condition `{r | r(a, 1) = true}` is clopen;
* `range ιSpv_bool` is closed (from `ValuationSpectrumCompact`);
* under `[DiscreteTopology A]` the continuity condition `v ∈ Cont A` is
  automatic (`Cont A = univ`, `cont_eq_univ_of_discreteTopology`);

hence `ιSpv_bool '' Spa A A⁺ = range ιSpv_bool ∩ ⋂_{a ∈ A⁺} {r | r(a, 1) = true}`
is closed in the compact Hausdorff space `(A × A → Bool)`, so is compact. The
factorisation `ιSpv = (fun r p => boolToProp (r p)) ∘ ιSpv_bool` transfers this to
compactness of `ιSpv '' Spa A A⁺` (continuous image), and finally
`ιSpv_isEmbedding.isCompact_iff` yields `IsCompact (Spa A A⁺ : Set (Spv A))` and
the `CompactSpace ↥(Spa A A⁺)` instance.

## Main results

* `image_spa_ιSpv_bool` : Characterisation of `ιSpv_bool '' Spa A A⁺` in the
  discrete case as `range ιSpv_bool ∩ ⋂_{a ∈ A⁺} {r | r(a, 1) = true}`.
* `isClosed_image_spa_ιSpv_bool` : The above image is closed in the Bool product.
* `isCompact_spa` : `Spa A A⁺` is a compact subset of `Spv A` (discrete case).
* `instCompactSpace_spa` : `CompactSpace ↥(Spa A A⁺)` (discrete case).

## Scope: discrete topology only

The present file proves the compactness of `Spa(A, A⁺)` under the assumption
`[DiscreteTopology A]`, matching the "discrete case first" design decision for
this project. The general Huber/Tate version requires a closed-set description
of `Cont A` (or at least of `ιSpv_bool '' Cont A`) which is not yet available.
See Wedhorn Theorem 7.30 for the mathematical statement of the general case.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Theorem 7.30, Corollary 7.32.
* R. Huber, *Continuous valuations*, Math. Z. 212 (1993), 455–477.
-/

open Topology

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]

/-! ### Bool-embedding description of `Spa A A⁺` under `[DiscreteTopology A]` -/

/-- **Image of `Spa A A⁺` under `ιSpv_bool` (discrete case).**

Under `[DiscreteTopology A]`, the image of the adic spectrum under the Bool Huber
embedding is exactly the intersection of `range ιSpv_bool` with the coordinate
cylinders `{r | r (a, 1) = true}` for `a ∈ A⁺`. The continuity condition is
automatic in the discrete setting (`cont_eq_univ_of_discreteTopology`). -/
lemma image_spa_ιSpv_bool [DiscreteTopology A] :
    (ιSpv_bool : Spv A → (A × A → Bool)) '' (Spa A A⁺) =
      Set.range (ιSpv_bool : Spv A → (A × A → Bool)) ∩
        ⋂ (a : A) (_ : a ∈ A⁺), {r : A × A → Bool | r (a, 1) = true} := by
  ext r
  simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_iInter, Set.mem_range,
    Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨v, hv, rfl⟩
    refine ⟨⟨v, rfl⟩, fun a ha ↦ ?_⟩
    simp only [ιSpv_bool_apply, @decide_eq_true_iff _ (Classical.dec _)]
    exact ⟨hv.2 a ha, v.not_vle_one_zero⟩
  · rintro ⟨⟨v, rfl⟩, hr⟩
    refine ⟨v, ⟨fun _ ↦ isOpen_discrete _, fun a ha ↦ ?_⟩, rfl⟩
    have h := hr a ha
    simp only [ιSpv_bool_apply, @decide_eq_true_iff _ (Classical.dec _)] at h
    exact h.1

/-- **Closedness of `ιSpv_bool '' Spa A A⁺` (discrete case).**

In the discrete Bool product `A × A → Bool`, the image of `Spa A A⁺` under
`ιSpv_bool` is closed: it is the intersection of the closed range of
`ιSpv_bool` (from `ValuationSpectrumCompact`) with the coordinate conditions
`{r | r(a, 1) = true}`, each clopen in the discrete product. -/
lemma isClosed_image_spa_ιSpv_bool [DiscreteTopology A] :
    IsClosed ((ιSpv_bool : Spv A → (A × A → Bool)) '' (Spa A A⁺)) := by
  rw [image_spa_ιSpv_bool]
  exact isClosed_range_ιSpv_bool.inter
    (isClosed_iInter fun a ↦ isClosed_iInter fun _ ↦ isClosed_coord_true (a, 1))

/-! ### Quasi-compactness of `Spa A A⁺` in `Spv A` -/

/-- **T-NULL-0c (discrete case): `Spa(A, A⁺)` is quasi-compact in `Spv A`.**

We route compactness through the Sierpinski Huber embedding
`ιSpv : Spv A → (A × A → Prop)` (an embedding, see `ιSpv_isEmbedding`) and the
Bool embedding `ιSpv_bool` (with closed range). The factorisation
`ιSpv = (boolToProp ∘ ·) ∘ ιSpv_bool` lets us transfer compactness of
`ιSpv_bool '' Spa` — which is closed in the compact Bool product — into
compactness of `ιSpv '' Spa`, hence of `Spa` itself via the embedding.

**Hypothesis:** `[DiscreteTopology A]`. Under this, `Cont A = univ` and the
obstruction to closedness of `Cont` disappears. The general Huber/Tate version
(Wedhorn 7.30) is future work. -/
theorem isCompact_spa [DiscreteTopology A] :
    IsCompact ((Spa A A⁺) : Set (Spv A)) := by
  refine (ιSpv_isEmbedding.isCompact_iff (s := Spa A A⁺)).mpr ?_
  -- Factor `ιSpv '' Spa` as the continuous image under `boolToProp_pi` of
  -- `ιSpv_bool '' Spa`. The latter is closed in the compact Bool product,
  -- hence compact; continuous image of compact is compact.
  have hfactor :
      (ιSpv : Spv A → (A × A → Prop)) '' (Spa A A⁺) =
        (fun r : A × A → Bool => fun p => boolToProp (r p)) ''
          ((ιSpv_bool : Spv A → (A × A → Bool)) '' (Spa A A⁺)) := by
    ext s
    simp only [Set.mem_image]
    refine ⟨?_, ?_⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨ιSpv_bool v, ⟨v, hv, rfl⟩, (ιSpv_eq_boolToProp_comp_ιSpv_bool v).symm⟩
    · rintro ⟨r, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, ιSpv_eq_boolToProp_comp_ιSpv_bool v⟩
  rw [hfactor]
  exact isClosed_image_spa_ιSpv_bool.isCompact.image continuous_boolToProp_pi

/-- **T-NULL-0c capstone: `CompactSpace ↥(Spa(A, A⁺))` (discrete case).**

The adic spectrum `Spa(A, A⁺)` of a commutative ring `A` with the discrete
topology and a choice of integral subring `A⁺` is a compact topological space.

This is the discrete specialisation of Wedhorn Theorem 7.30. Together with
`ValuationSpectrum.instCompactSpace` (quasi-compactness of `Spv A`) it unblocks
the Nullstellensatz refinement / Cor 7.32 route to the dominating-unit lemma
(see `docs/plans/2026-04-16-s3-nullstellensatz-plan.md`, T-NULL-0c). -/
instance instCompactSpace_spa [DiscreteTopology A] :
    CompactSpace ↥(Spa A A⁺) :=
  isCompact_iff_compactSpace.mp isCompact_spa

end ValuationSpectrum
