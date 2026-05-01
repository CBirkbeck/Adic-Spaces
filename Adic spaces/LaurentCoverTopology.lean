/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».LaurentCoverExact
import «Adic spaces».TateAlgebraTopology

/-!
# Quotient topology API for the Laurent cover (T131)

For an `IsTateRing A`, the algebraic Laurent quotient objects defined
in `LaurentCoverExact.lean`,

* `B₁_gen f := TateAlgebra A ⧸ ⟨algebraMap f − X⟩`,
* `B₂_gen f := TateAlgebra A ⧸ ⟨1 − algebraMap f · X⟩`,
* `B₁₂_gen f := LaurentTateAlgebra A ⧸ ⟨algebraMap f − ζ⟩`,

inherit canonical quotient topologies from the canonical Tate-algebra
topologies on `TateAlgebra A` and `TateAlgebra₂ A` (via
`TateAlgebra.instTopologicalSpaceTateAlgebra` /
`TateAlgebra.instTopologicalSpaceTateAlgebra₂` in
`TateAlgebraTopology.lean`).

This module exposes those topologies as `noncomputable def`s plus the
matching `IsTopologicalRing` / `IsTopologicalAddGroup` instances.

For `B₁₂_gen` the topology is built in two stages: first a quotient
topology on `LaurentTateAlgebra A = TateAlgebra₂ A ⧸ laurentIdeal A`
(the "rank-2 Laurent" base), then a further quotient by
`laurentFSubZetaIdeal f`. The resulting topology coincides with the
canonical bivariate-overlap topology
(`TateAlgebra.quotientBivariateOverlapIdealTopology`) under the
identification of `B₁₂_gen f` with `TateAlgebra₂ A ⧸
bivariateOverlapIdeal f` (which holds because the two ideals
coincide as A-ideals via `1 − algebraMap f · Y = − Y · (algebraMap f
− X) − (X · Y − 1)`), but we keep the direct two-stage form here so
callers can use the `B₁₂_gen` type and the `quotLaurent` /
`posLift` / `negLift` of `LaurentCoverExact.lean` directly.

Together with the existing `epsilonHom_gen` / `deltaMap_gen` /
`posLift` / `negLift` declarations in `LaurentCoverExact.lean`, this
is the topology layer that the T130 strict-exactness/embedding
follow-up needs.

## Continuity of `deltaMap_gen` (next step, not landed here)

Continuity of `deltaMap_gen f : B₁_gen f × B₂_gen f → B₁₂_gen f` under
the topologies above reduces, by the universal property of the
quotient topology and the fact that `deltaMap_gen` factors as
`(b₁, b₂) ↦ posLift f b₁ − negLift f b₂`, to continuity of the two
ring homomorphisms

```
(quotLaurent f).comp posEmbHom : TateAlgebra A → B₁₂_gen f
(quotLaurent f).comp negEmbHom : TateAlgebra A → B₁₂_gen f
```

under the canonical topology on `TateAlgebra A` and the canonical
quotient topology `B₁₂_gen_topology f`. The inner `quotLaurent f` is
continuous (as a quotient projection); the outer composition reduces
to **continuity of the embeddings** `posEmbHom`, `negEmbHom`
(`TateAlgebra A →+* LaurentTateAlgebra A`) under the canonical Tate
topologies. Those embedding continuities are the canonical-topology
analogues of the existing T-topology embedding continuities and are
the **next reusable algebraic-topology step** — they are not
provable from this file's API alone (they require the canonical
topology on `posIncl` / `negIncl : TateAlgebra A → TateAlgebra₂ A`,
which is set up elsewhere).

This module deliberately stops at the topology + instance layer and
documents the embedding-continuity step as the next ticket.
-/

namespace LaurentCover

open TateAlgebra LaurentTateAlgebra

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

section TopologicalQuotients

variable [IsTateRing A] [IsNoetherianRing A] [IsDomain A]
variable (f : A)

/-! ### `B₁_gen`: `TateAlgebra A ⧸ ⟨algebraMap f − X⟩` -/

/-- Canonical quotient topology on `B₁_gen f`, induced from the
canonical Tate-algebra topology on `TateAlgebra A`. -/
@[reducible]
noncomputable def B₁_gen_topology : TopologicalSpace (B₁_gen f) :=
  @topologicalRingQuotientTopology _ instTopologicalSpaceTateAlgebra _
    (Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X})

/-- `B₁_gen f` is a topological ring under its canonical quotient topology. -/
noncomputable instance B₁_gen_isTopologicalRing :
    @IsTopologicalRing (B₁_gen f) (B₁_gen_topology f) _ :=
  @topologicalRing_quotient _ instTopologicalSpaceTateAlgebra _
    (Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X})
    instIsTopologicalRingTateAlgebra

/-- `B₁_gen f` is a topological additive group. -/
noncomputable instance B₁_gen_isTopologicalAddGroup :
    @IsTopologicalAddGroup (B₁_gen f) (B₁_gen_topology f) _ :=
  @IsTopologicalRing.to_topologicalAddGroup _ _
    (B₁_gen_topology f) (B₁_gen_isTopologicalRing f)

/-! ### `B₂_gen`: `TateAlgebra A ⧸ ⟨1 − algebraMap f · X⟩` -/

/-- Canonical quotient topology on `B₂_gen f`, induced from the
canonical Tate-algebra topology on `TateAlgebra A`. -/
@[reducible]
noncomputable def B₂_gen_topology : TopologicalSpace (B₂_gen f) :=
  @topologicalRingQuotientTopology _ instTopologicalSpaceTateAlgebra _
    (Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X})

/-- `B₂_gen f` is a topological ring under its canonical quotient topology. -/
noncomputable instance B₂_gen_isTopologicalRing :
    @IsTopologicalRing (B₂_gen f) (B₂_gen_topology f) _ :=
  @topologicalRing_quotient _ instTopologicalSpaceTateAlgebra _
    (Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X})
    instIsTopologicalRingTateAlgebra

/-- `B₂_gen f` is a topological additive group. -/
noncomputable instance B₂_gen_isTopologicalAddGroup :
    @IsTopologicalAddGroup (B₂_gen f) (B₂_gen_topology f) _ :=
  @IsTopologicalRing.to_topologicalAddGroup _ _
    (B₂_gen_topology f) (B₂_gen_isTopologicalRing f)

/-! ### `LaurentTateAlgebra`: `TateAlgebra₂ A ⧸ laurentIdeal A` -/

/-- Canonical quotient topology on `LaurentTateAlgebra A`, induced
from the canonical Tate-algebra-of-2-variables topology on
`TateAlgebra₂ A`. -/
@[reducible]
noncomputable def laurentTateAlgebra_topology :
    TopologicalSpace (LaurentTateAlgebra A) :=
  @topologicalRingQuotientTopology _ instTopologicalSpaceTateAlgebra₂ _
    (laurentIdeal A)

/-- `LaurentTateAlgebra A` is a topological ring under its canonical
quotient topology. -/
noncomputable instance laurentTateAlgebra_isTopologicalRing :
    @IsTopologicalRing (LaurentTateAlgebra A)
      laurentTateAlgebra_topology _ :=
  @topologicalRing_quotient _ instTopologicalSpaceTateAlgebra₂ _
    (laurentIdeal A) instIsTopologicalRingTateAlgebra₂

/-- `LaurentTateAlgebra A` is a topological additive group. -/
noncomputable instance laurentTateAlgebra_isTopologicalAddGroup :
    @IsTopologicalAddGroup (LaurentTateAlgebra A)
      laurentTateAlgebra_topology _ :=
  @IsTopologicalRing.to_topologicalAddGroup _ _
    laurentTateAlgebra_topology laurentTateAlgebra_isTopologicalRing

/-! ### `B₁₂_gen`: `LaurentTateAlgebra A ⧸ ⟨algebraMap f − ζ⟩` -/

/-- Canonical quotient topology on `B₁₂_gen f`, built as the further
quotient of the canonical topology on `LaurentTateAlgebra A` by
`laurentFSubZetaIdeal f`. -/
@[reducible]
noncomputable def B₁₂_gen_topology : TopologicalSpace (B₁₂_gen f) :=
  @topologicalRingQuotientTopology _ laurentTateAlgebra_topology _
    (laurentFSubZetaIdeal f)

/-- `B₁₂_gen f` is a topological ring under its canonical quotient topology. -/
noncomputable instance B₁₂_gen_isTopologicalRing :
    @IsTopologicalRing (B₁₂_gen f) (B₁₂_gen_topology f) _ :=
  @topologicalRing_quotient _ laurentTateAlgebra_topology _
    (laurentFSubZetaIdeal f) laurentTateAlgebra_isTopologicalRing

/-- `B₁₂_gen f` is a topological additive group. -/
noncomputable instance B₁₂_gen_isTopologicalAddGroup :
    @IsTopologicalAddGroup (B₁₂_gen f) (B₁₂_gen_topology f) _ :=
  @IsTopologicalRing.to_topologicalAddGroup _ _
    (B₁₂_gen_topology f) (B₁₂_gen_isTopologicalRing f)

/-! ### Quotient projection continuity -/

omit [IsNoetherianRing A] [IsDomain A] in
/-- The quotient map `LaurentTateAlgebra A → B₁₂_gen f` is continuous
under the canonical topologies. -/
theorem quotLaurent_continuous :
    @Continuous _ _ laurentTateAlgebra_topology (B₁₂_gen_topology f)
      (quotLaurent f) :=
  @continuous_quot_mk _ laurentTateAlgebra_topology _

end TopologicalQuotients

end LaurentCover
