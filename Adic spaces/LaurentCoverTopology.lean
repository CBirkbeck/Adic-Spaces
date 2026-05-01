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

## Continuity of `deltaMap_gen` (T132)

Section `EmbeddingContinuity` proves canonical-topology continuity of
`posIncl`, `negIncl`, `mkHom`, `posEmbHom`, `negEmbHom`. Section
`LiftContinuity` proves continuity of `posLift`, `negLift`, and the
final `deltaMap_gen f : B₁_gen f × B₂_gen f → B₁₂_gen f` under the T131
quotient topologies. The proofs use the basic-neighborhood basis
`tateAlgBasis'` / `tateAlgBasis'₂` from `TateAlgebraTopology.lean`
together with the existing coefficient bridges
`tateAlgNhd_coeff_mem` and `tateAlgNhd₂_of_coeff_mem_principal`.
-/

namespace LaurentCover

open TateAlgebra LaurentTateAlgebra Topology

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

section TopologicalQuotients

variable [IsTateRing A] [IsNoetherianRing A] [IsDomain A]
variable (f : A)

/-! ### `B₁_gen`: `TateAlgebra A ⧸ ⟨algebraMap f − X⟩` -/

/-- Canonical quotient topology on `B₁_gen f`, induced from the
canonical Tate-algebra topology on `TateAlgebra A`. -/
@[reducible]
noncomputable instance B₁_gen_topology : TopologicalSpace (B₁_gen f) :=
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
noncomputable instance B₂_gen_topology : TopologicalSpace (B₂_gen f) :=
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
noncomputable instance laurentTateAlgebra_topology :
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
noncomputable instance B₁₂_gen_topology : TopologicalSpace (B₁₂_gen f) :=
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

/-! ### Canonical-topology continuity of the Laurent embeddings (T132)

The key inputs are:

* `tateAlgBasis'.hasBasis_nhds_zero` and `tateAlgBasis'₂.hasBasis_nhds_zero`,
  giving the basic-neighborhood bases at `0` for the canonical Tate-algebra
  topologies (subgroups `tateAlgNhd P n` and `tateAlgNhd₂ P n` indexed by `n`).
* `tateAlgNhd_coeff_mem` (univariate) and `tateAlgNhd₂_of_coeff_mem_principal`
  (bivariate), giving the coefficient bridge between the two bases.
* `continuous_of_continuousAt_zero` for additive group homs.

`varInclHom j` (for `j : Fin 2`) acts on a univariate restricted power
series by reindexing to a single variable in the bivariate ring; its
coefficients are either `0` or copy a univariate coefficient. So if every
coefficient of `y` lies in `image P.I^n`, the same holds for every
coefficient of the bivariate lift, giving the basic-neighborhood
preimage containment that controls continuity. -/

section EmbeddingContinuity

variable [IsTateRing A]

/-- Local helper for `posIncl_continuous` and `negIncl_continuous`: any
ring homomorphism `φ : TateAlgebra A →+* TateAlgebra₂ A` whose underlying
function factors as the variable-`j` inclusion `varInclHom j` on the
underlying multivariate power series is continuous under the canonical
Tate topologies. -/
private theorem varIncl_continuous_aux (j : Fin 2)
    (φ : ↥(TateAlgebra A) →+* ↥(TateAlgebra₂ A))
    (hφ : ∀ y : ↥(TateAlgebra A), (φ y).val = varInclHom j y.val) :
    @Continuous _ _ instTopologicalSpaceTateAlgebra
      instTopologicalSpaceTateAlgebra₂ φ := by
  letI τ₁ : TopologicalSpace ↥(TateAlgebra A) := tateAlgebraTopology'
  letI τ₂ : TopologicalSpace ↥(TateAlgebra₂ A) := tateAlgebra₂Topology'
  haveI hr1 : IsTopologicalRing ↥(TateAlgebra A) :=
    tateAlgebraTopology'_isTopologicalRing
  haveI hr2 : IsTopologicalRing ↥(TateAlgebra₂ A) :=
    tateAlgebra₂Topology'_isTopologicalRing
  haveI hag1 : IsTopologicalAddGroup ↥(TateAlgebra A) :=
    hr1.to_topologicalAddGroup
  haveI hag2 : IsTopologicalAddGroup ↥(TateAlgebra₂ A) :=
    hr2.to_topologicalAddGroup
  let pp := IsTateRing.principalPair A
  let P := pp.toPairOfDefinition
  have hπ_gen : P.I = Ideal.span {pp.π} := pp.I_eq_span
  have hπ_unit : IsUnit ((pp.π : A)) := pp.π_isUnit
  apply continuous_of_continuousAt_zero φ
  rw [ContinuousAt, map_zero]
  rw [tateAlgBasis'.hasBasis_nhds_zero.tendsto_iff
    tateAlgBasis'₂.hasBasis_nhds_zero]
  intro n _
  refine ⟨n, trivial, ?_⟩
  intro y hy
  apply tateAlgNhd₂_of_coeff_mem_principal P n pp.π hπ_gen hπ_unit
  · -- φ y ∈ pairSubring₂ P
    intro l
    rw [hφ y]
    change varInclFun j y.val l ∈ P.A₀
    rw [varInclFun_apply]
    split_ifs
    · obtain ⟨b, _, hb_eq⟩ :=
        tateAlgNhd_coeff_mem P n hy (Finsupp.single 0 (l j))
      rw [← hb_eq]; exact b.property
    · exact P.A₀.zero_mem
  · -- coefficients of (φ y) all lie in image of P.I^n
    intro l
    rw [hφ y]
    change ∃ b : P.A₀, b ∈ P.I ^ n ∧ (b : A) = varInclFun j y.val l
    rw [varInclFun_apply]
    split_ifs
    · exact tateAlgNhd_coeff_mem P n hy (Finsupp.single 0 (l j))
    · exact ⟨0, (P.I ^ n).zero_mem, by simp⟩

/-- The positive variable inclusion `posIncl : A⟨X⟩ →+* A⟨X, Y⟩` is continuous
under the canonical Tate-algebra topologies. -/
theorem posIncl_continuous :
    @Continuous _ _ instTopologicalSpaceTateAlgebra
      instTopologicalSpaceTateAlgebra₂
      (LaurentTateAlgebra.posIncl : ↥(TateAlgebra A) →+* ↥(TateAlgebra₂ A)) :=
  varIncl_continuous_aux 0 _ (fun _ => rfl)

/-- The negative variable inclusion `negIncl : A⟨X⟩ →+* A⟨X, Y⟩` is continuous
under the canonical Tate-algebra topologies. -/
theorem negIncl_continuous :
    @Continuous _ _ instTopologicalSpaceTateAlgebra
      instTopologicalSpaceTateAlgebra₂
      (LaurentTateAlgebra.negIncl : ↥(TateAlgebra A) →+* ↥(TateAlgebra₂ A)) :=
  varIncl_continuous_aux 1 _ (fun _ => rfl)

/-- The Laurent quotient projection `mkHom : A⟨X, Y⟩ →+* A⟨ζ, ζ⁻¹⟩` is
continuous from the canonical bivariate Tate topology to the canonical
Laurent quotient topology. -/
theorem mkHom_continuous :
    @Continuous _ _ instTopologicalSpaceTateAlgebra₂ laurentTateAlgebra_topology
      (LaurentTateAlgebra.mkHom : ↥(TateAlgebra₂ A) →+* LaurentTateAlgebra A) :=
  @continuous_quot_mk _ instTopologicalSpaceTateAlgebra₂ _

/-- The positive Laurent embedding `posEmbHom : A⟨X⟩ →+* A⟨ζ, ζ⁻¹⟩`
(`X ↦ ζ`) is continuous under the canonical Tate topologies. -/
theorem posEmbHom_continuous :
    @Continuous _ _ instTopologicalSpaceTateAlgebra laurentTateAlgebra_topology
      (LaurentTateAlgebra.posEmbHom : ↥(TateAlgebra A) →+* LaurentTateAlgebra A) :=
  mkHom_continuous.comp posIncl_continuous

/-- The negative Laurent embedding `negEmbHom : A⟨X⟩ →+* A⟨ζ, ζ⁻¹⟩`
(`X ↦ ζ⁻¹`) is continuous under the canonical Tate topologies. -/
theorem negEmbHom_continuous :
    @Continuous _ _ instTopologicalSpaceTateAlgebra laurentTateAlgebra_topology
      (LaurentTateAlgebra.negEmbHom : ↥(TateAlgebra A) →+* LaurentTateAlgebra A) :=
  mkHom_continuous.comp negIncl_continuous

end EmbeddingContinuity

/-! ### Continuity of the lifts and `deltaMap_gen` -/

section LiftContinuity

variable [IsTateRing A] [IsNoetherianRing A] [IsDomain A] (f : A)

omit [IsNoetherianRing A] [IsDomain A] in
/-- The composition `(quotLaurent f).comp posEmbHom : A⟨X⟩ → B₁₂_gen f` is
continuous under the canonical topologies. -/
theorem quotLaurent_comp_posEmbHom_continuous :
    @Continuous _ _ instTopologicalSpaceTateAlgebra (B₁₂_gen_topology f)
      ((quotLaurent f).comp LaurentTateAlgebra.posEmbHom) :=
  (quotLaurent_continuous f).comp posEmbHom_continuous

omit [IsNoetherianRing A] [IsDomain A] in
/-- The composition `(quotLaurent f).comp negEmbHom : A⟨X⟩ → B₁₂_gen f` is
continuous under the canonical topologies. -/
theorem quotLaurent_comp_negEmbHom_continuous :
    @Continuous _ _ instTopologicalSpaceTateAlgebra (B₁₂_gen_topology f)
      ((quotLaurent f).comp LaurentTateAlgebra.negEmbHom) :=
  (quotLaurent_continuous f).comp negEmbHom_continuous

omit [IsNoetherianRing A] [IsDomain A] in
/-- The positive Laurent lift `posLift f : B₁_gen f →+* B₁₂_gen f` is
continuous under the canonical quotient topologies. -/
theorem posLift_continuous :
    @Continuous _ _ (B₁_gen_topology f) (B₁₂_gen_topology f) (posLift f) := by
  letI tA : TopologicalSpace ↥(TateAlgebra A) := instTopologicalSpaceTateAlgebra
  letI hringA : IsTopologicalRing ↥(TateAlgebra A) := instIsTopologicalRingTateAlgebra
  letI tB1 : TopologicalSpace (B₁_gen f) := B₁_gen_topology f
  letI tB12 : TopologicalSpace (B₁₂_gen f) := B₁₂_gen_topology f
  haveI hringB1 : IsTopologicalRing (B₁_gen f) := B₁_gen_isTopologicalRing f
  have hQM : IsQuotientMap (Ideal.Quotient.mk
      (Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X})) :=
    (QuotientRing.isOpenQuotientMap_mk _).isQuotientMap
  exact hQM.continuous_iff.mpr (quotLaurent_comp_posEmbHom_continuous f)

omit [IsNoetherianRing A] [IsDomain A] in
/-- The negative Laurent lift `negLift f : B₂_gen f →+* B₁₂_gen f` is
continuous under the canonical quotient topologies. -/
theorem negLift_continuous :
    @Continuous _ _ (B₂_gen_topology f) (B₁₂_gen_topology f) (negLift f) := by
  letI tA : TopologicalSpace ↥(TateAlgebra A) := instTopologicalSpaceTateAlgebra
  letI hringA : IsTopologicalRing ↥(TateAlgebra A) := instIsTopologicalRingTateAlgebra
  letI tB2 : TopologicalSpace (B₂_gen f) := B₂_gen_topology f
  letI tB12 : TopologicalSpace (B₁₂_gen f) := B₁₂_gen_topology f
  haveI hringB2 : IsTopologicalRing (B₂_gen f) := B₂_gen_isTopologicalRing f
  have hQM : IsQuotientMap (Ideal.Quotient.mk
      (Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X})) :=
    (QuotientRing.isOpenQuotientMap_mk _).isQuotientMap
  exact hQM.continuous_iff.mpr (quotLaurent_comp_negEmbHom_continuous f)

omit [IsNoetherianRing A] [IsDomain A] in
/-- The Laurent delta map `deltaMap_gen f : B₁_gen f × B₂_gen f → B₁₂_gen f`,
defined by `(b₁, b₂) ↦ posLift f b₁ − negLift f b₂`, is continuous under
the canonical product / quotient topologies. -/
theorem deltaMap_gen_continuous :
    @Continuous _ _
      (@instTopologicalSpaceProd _ _ (B₁_gen_topology f) (B₂_gen_topology f))
      (B₁₂_gen_topology f) (deltaMap_gen f) := by
  letI tB1 : TopologicalSpace (B₁_gen f) := B₁_gen_topology f
  letI tB2 : TopologicalSpace (B₂_gen f) := B₂_gen_topology f
  letI tB12 : TopologicalSpace (B₁₂_gen f) := B₁₂_gen_topology f
  haveI hringB12 : IsTopologicalRing (B₁₂_gen f) := B₁₂_gen_isTopologicalRing f
  haveI hagB12 : IsTopologicalAddGroup (B₁₂_gen f) := B₁₂_gen_isTopologicalAddGroup f
  have h1 : Continuous (fun p : B₁_gen f × B₂_gen f => posLift f p.1) :=
    (posLift_continuous f).comp continuous_fst
  have h2 : Continuous (fun p : B₁_gen f × B₂_gen f => negLift f p.2) :=
    (negLift_continuous f).comp continuous_snd
  exact h1.sub h2

end LiftContinuity

end LaurentCover
