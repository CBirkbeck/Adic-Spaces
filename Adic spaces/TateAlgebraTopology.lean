/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.MvPowerSeries.PiTopology
import «Adic spaces».TateAlgebra
import «Adic spaces».HuberRings

/-!
# Topology on the Tate Algebra A⟨X⟩

The Tate algebra `A⟨X⟩` inherits the **product topology** from `MvPowerSeries (Fin 1) A`,
where we view power series as functions `(Fin 1 →₀ ℕ) → A` and equip the codomain with
the topology of `A`. The subring `TateAlgebra A ⊂ MvPowerSeries (Fin 1) A` gets the
induced (subspace) topology.

This topology makes `A⟨X⟩` a topological ring (via `Subring.instIsTopologicalRing`)
and is the topology of coefficient-wise convergence: a net of restricted power series
converges iff each coefficient converges in `A`.

## I-adic topology and Huber ring structure

Given a pair of definition `(A₀, I)` for `A`, we construct:

* `TateAlgebra.pairSubring P` : The subring `A₀⟨X⟩ ⊆ A⟨X⟩` of restricted power series
  with coefficients in `A₀`.
* `TateAlgebra.pairConstantHom P` : The constant series embedding `A₀ →+* A₀⟨X⟩`.
* `TateAlgebra.pairIdeal P` : The ideal `I · A₀⟨X⟩` inside `A₀⟨X⟩`.
* `TateAlgebra.pairIdeal_fg P` : Finite generation of `I · A₀⟨X⟩`.
* `TateAlgebra.pairSubring_isHuberRing P` : `A₀⟨X⟩` with the `(I · A₀⟨X⟩)`-adic
  topology is a Huber ring.

The Huber ring structure on `A₀⟨X⟩` uses the pair `(⊤, idealToTop (pairIdeal P))`
where the ring of definition is the whole ring `A₀⟨X⟩` itself, equipped with the
`(pairIdeal P)`-adic topology.

## General results

* `idealToTop I` : Transfer an ideal from `R` to `↥(⊤ : Subring R)`.
* `isAdic_idealToTop I` : The subspace topology on `↥⊤` from the `I`-adic topology
  on `R` is `(idealToTop I)`-adic.
* `pairOfDefinition_ofAdic I hI` : Any ring with finitely generated `I`-adic topology
  admits a pair of definition `(⊤, idealToTop I)`.
* `isHuberRing_ofAdic I hI` : A ring with finitely generated `I`-adic topology is Huber.

## Main results (product topology)

* `TateAlgebra.continuous_coeff` : Each coefficient function `coeff n` is continuous.
* `TateAlgebra.continuous_evalZeroHom` : The evaluation-at-zero map is continuous.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §6, §8
-/

open MvPowerSeries.WithPiTopology Filter Topology Pointwise

namespace TateAlgebra

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-! ### Topology instances -/

/-- The topology on `A⟨X⟩` is the subspace topology from `MvPowerSeries (Fin 1) A`
with the product topology. This makes coefficient extraction continuous. -/
example : TopologicalSpace ↥(TateAlgebra A) := inferInstance

/-- `A⟨X⟩` is a topological ring with the subspace topology. -/
example : IsTopologicalRing ↥(TateAlgebra A) := inferInstance

/-! ### Continuity of coefficient extraction -/

/-- The `n`-th coefficient function `coeff n : A⟨X⟩ → A` is continuous
(it's the composition of the continuous embedding into `MvPowerSeries` and
the continuous coefficient projection). -/
theorem continuous_coeff (n : ℕ) :
    Continuous (fun f : ↥(TateAlgebra A) => coeff n f) := by
  apply Continuous.comp
  · exact MvPowerSeries.WithPiTopology.continuous_coeff A (toIndex n)
  · exact continuous_subtype_val

/-- `evalZeroHom` is continuous (it extracts the 0-th coefficient). -/
theorem continuous_evalZeroHom :
    Continuous (evalZeroHom : ↥(TateAlgebra A) → A) := by
  exact continuous_coeff 0

end TateAlgebra

/-! ### Transfer ideals to ↥⊤ and adic pair of definition

These results show that any commutative ring equipped with a finitely generated
`I`-adic topology admits a canonical pair of definition `(⊤, idealToTop I)`,
making it a Huber ring. This is used to construct the Huber ring structure
on `A₀⟨X⟩`.
-/

section IdealTopTransfer

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- Transfer an ideal `I` of `R` to an ideal of `↥(⊤ : Subring R)` via the
inverse of `Subring.topEquiv`. This allows us to work with `PairOfDefinition`,
which requires an ideal of a subring. -/
noncomputable def idealToTop : Ideal ↥(⊤ : Subring R) :=
  I.map (Subring.topEquiv (R := R)).symm.toRingHom

/-- Powers of the transferred ideal equal preimages of the original
powers under `Subtype.val`. -/
theorem idealToTop_pow_eq_preimage (n : ℕ) :
    ((idealToTop I ^ n : Ideal ↥(⊤ : Subring R)) :
      Set ↥(⊤ : Subring R)) =
    Subtype.val ⁻¹' ((I ^ n : Ideal R) : Set R) := by
  unfold idealToTop
  rw [← Ideal.map_pow,
    show (I ^ n).map (Subring.topEquiv (R := R)).symm.toRingHom =
      (I ^ n).map (Subring.topEquiv (R := R)).symm from rfl,
    ← Ideal.comap_symm]
  ext x
  simp only [RingEquiv.symm_symm, Ideal.mem_comap,
    SetLike.mem_coe, Set.mem_preimage]
  rfl

/-- The transferred ideal is finitely generated when the original is. -/
theorem idealToTop_fg (hI : I.FG) : (idealToTop I).FG :=
  hI.map _

/-- When `R` carries the `I`-adic topology, the subspace topology on
`↥(⊤ : Subring R)` is `(idealToTop I)`-adic. This is the key topological
result: the subspace topology on the whole ring (viewed as ↥⊤) correctly
inherits the adic structure. -/
theorem isAdic_idealToTop :
    @IsAdic ↥(⊤ : Subring R) _
      (@instTopologicalSpaceSubtype R (· ∈ (⊤ : Subring R))
        I.adicTopology)
      (idealToTop I) := by
  letI : TopologicalSpace R := I.adicTopology
  letI : IsTopologicalRing R :=
    I.ringFilterBasis.isTopologicalRing
  have hadic : @IsAdic R _ I.adicTopology I := rfl
  rw [@isAdic_iff _ _ _
    (Subring.instIsTopologicalRing (⊤ : Subring R))]
  exact ⟨fun n => by
      rw [idealToTop_pow_eq_preimage I n]
      exact (isAdic_iff.mp hadic).1 n |>.preimage
        continuous_subtype_val,
    fun s hs => by
      rw [nhds_subtype_eq_comap] at hs
      obtain ⟨U, hU, hsU⟩ := Filter.mem_comap.mp hs
      rw [show (0 : ↥(⊤ : Subring R)).val = (0 : R)
        from rfl] at hU
      obtain ⟨n, -, hn⟩ :=
        hadic.hasBasis_nhds_zero.mem_iff.mp hU
      exact ⟨n, (idealToTop_pow_eq_preimage I n ▸
        Set.preimage_mono hn).trans hsU⟩⟩

/-- For a ring `R` with the `I`-adic topology (where `I` is finitely generated),
the pair `(⊤, idealToTop I)` is a pair of definition. -/
noncomputable def pairOfDefinition_ofAdic (hI : I.FG) :
    @PairOfDefinition R _ I.adicTopology := by
  letI : TopologicalSpace R := I.adicTopology
  exact
    { A₀ := ⊤
      I := idealToTop I
      isOpen := isOpen_univ
      fg := idealToTop_fg I hI
      isAdic := isAdic_idealToTop I }

/-- A ring with a finitely generated `I`-adic topology is a Huber ring.
The pair of definition is `(⊤, idealToTop I)`. -/
theorem isHuberRing_ofAdic (hI : I.FG) :
    @IsHuberRing R _ I.adicTopology := by
  letI : TopologicalSpace R := I.adicTopology
  exact ⟨⟨pairOfDefinition_ofAdic I hI⟩⟩

end IdealTopTransfer

/-! ### Ring of definition and ideal for A₀⟨X⟩

Given a pair of definition `(A₀, I)` for a nonarchimedean topological ring `A`,
we construct the algebraic data needed for the Huber ring structure on `A₀⟨X⟩`:
the subring of restricted power series with coefficients in `A₀`, the ideal
generated by constant series from `I`, and finite generation.
-/

namespace TateAlgebra

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [NonarchimedeanRing A] [IsTopologicalRing A]

/-- The subring of `A⟨X⟩` consisting of restricted power series whose
coefficients all lie in `P.A₀`. This is the "ring of definition"
`A₀⟨X⟩` for the Tate algebra (Wedhorn, §8). -/
noncomputable def pairSubring (P : PairOfDefinition A) :
    Subring ↥(TateAlgebra A) where
  carrier := {f | ∀ s : Fin 1 →₀ ℕ,
    MvPowerSeries.coeff s f.val ∈ P.A₀}
  mul_mem' {f g} hf hg s := by
    simp only [Subring.coe_mul, MvPowerSeries.coeff_mul]
    exact P.A₀.toSubsemiring.sum_mem
      fun p _ => P.A₀.mul_mem (hf p.1) (hg p.2)
  one_mem' s := by
    simp only [OneMemClass.coe_one, MvPowerSeries.coeff_one]
    split
    · exact P.A₀.one_mem
    · exact P.A₀.zero_mem
  add_mem' {f g} hf hg s := by
    simp only [Subring.coe_add, map_add]
    exact P.A₀.add_mem (hf s) (hg s)
  zero_mem' s := by
    simp only [ZeroMemClass.coe_zero, map_zero]
    exact P.A₀.zero_mem
  neg_mem' {f} hf s := by
    simp only [NegMemClass.coe_neg, map_neg]
    exact P.A₀.neg_mem (hf s)

omit [IsTopologicalRing A] in
/-- Membership in `pairSubring P` means all coefficients lie in `P.A₀`. -/
theorem mem_pairSubring (P : PairOfDefinition A)
    (f : ↥(TateAlgebra A)) :
    f ∈ pairSubring P ↔
      ∀ s, MvPowerSeries.coeff s f.val ∈ P.A₀ :=
  Iff.rfl

/-- The constant power series embedding `P.A₀ →+* A₀⟨X⟩`.
Sends `a ∈ A₀` to the constant restricted power series `C(a)`. -/
noncomputable def pairConstantHom (P : PairOfDefinition A) :
    P.A₀ →+* pairSubring P where
  toFun a := ⟨⟨MvPowerSeries.C a.val,
      MvPowerSeries.IsRestricted_algebraMap a.val⟩, by
    intro s; classical
    simp only [MvPowerSeries.coeff_C]
    split
    · exact a.2
    · exact P.A₀.zero_mem⟩
  map_one' := Subtype.ext (Subtype.ext (map_one _))
  map_mul' x y :=
    Subtype.ext (Subtype.ext (by
      simp [Subring.coe_mul, map_mul]))
  map_zero' := Subtype.ext (Subtype.ext (map_zero _))
  map_add' x y :=
    Subtype.ext (Subtype.ext (by
      simp [Subring.coe_add, map_add]))

/-- The ideal `I · A₀⟨X⟩` inside `A₀⟨X⟩`, defined as the image of `P.I`
under the constant power series embedding. This is the ideal of
definition for `A₀⟨X⟩` (Wedhorn, §8). -/
noncomputable def pairIdeal (P : PairOfDefinition A) :
    Ideal (pairSubring P) :=
  Ideal.map (pairConstantHom P) P.I

omit [IsTopologicalRing A] in
/-- The ideal `I · A₀⟨X⟩` is finitely generated (because `I` is). -/
theorem pairIdeal_fg (P : PairOfDefinition A) :
    (pairIdeal P).FG :=
  P.fg.map _

/-! ### Huber ring structure on A₀⟨X⟩ -/

omit [IsTopologicalRing A] in
/-- The ring `A₀⟨X⟩ = pairSubring P`, equipped with the
`(I · A₀⟨X⟩)`-adic topology, is a Huber ring. The pair of definition
is `(⊤, idealToTop (pairIdeal P))`, i.e., the whole ring `A₀⟨X⟩` serves
as its own ring of definition with the ideal `I · A₀⟨X⟩` (Wedhorn, §8). -/
theorem pairSubring_isHuberRing (P : PairOfDefinition A) :
    @IsHuberRing ↥(pairSubring P) _
      (pairIdeal P).adicTopology :=
  isHuberRing_ofAdic _ (pairIdeal_fg P)

omit [IsTopologicalRing A] in
/-- The `(pairIdeal P)`-adic topology on `A₀⟨X⟩` is a ring topology. -/
theorem pairSubring_isTopologicalRing
    (P : PairOfDefinition A) :
    @IsTopologicalRing ↥(pairSubring P)
      (pairIdeal P).adicTopology _ :=
  (pairIdeal P).ringFilterBasis.isTopologicalRing

omit [IsTopologicalRing A] in
/-- The `(pairIdeal P)`-adic topology on `A₀⟨X⟩` is nonarchimedean. -/
theorem pairSubring_nonarchimedean
    (P : PairOfDefinition A) :
    @NonarchimedeanRing ↥(pairSubring P) _
      (pairIdeal P).adicTopology :=
  Ideal.nonarchimedean (pairIdeal P)

omit [IsTopologicalRing A] in
/-- The `pairIdeal P` is `I`-adic on `A₀⟨X⟩` by construction. -/
theorem pairIdeal_isAdic (P : PairOfDefinition A) :
    @IsAdic ↥(pairSubring P) _
      (pairIdeal P).adicTopology (pairIdeal P) :=
  rfl

/-! ### Natural Tate ring topology on `TateAlgebra A` (Phase 2.2)

We extend the Huber ring structure from `pairSubring P = A₀⟨X⟩` to the full
`TateAlgebra A = A⟨X⟩` by defining a `RingSubgroupsBasis` whose basic
neighborhoods of `0` are the SET-IMAGES of `(pairIdeal P)^n` in `TateAlgebra A`
under the subring inclusion.

The resulting topology makes `pairSubring P = A₀⟨X⟩` an open subring with its
existing `(pairIdeal P)`-adic topology, hence makes `(pairSubring P, pairIdeal P)`
a `PairOfDefinition` and `TateAlgebra A` a Huber ring (Wedhorn §6).

**Why we use `RingSubgroupsBasis` rather than `Ideal.adicTopology`:**
The ideal `pairIdealExt := Ideal.map subtype (pairIdeal P)` of `TateAlgebra A`
generated by the image is *strictly larger* than the set-image, because
multiplication by elements of `TateAlgebra A` outside `pairSubring P` (such as
`1/π`) escapes the subring. So `Ideal.adicTopology pairIdealExt` is the wrong
topology — it would give a `pairSubring P`-adic topology on the whole ring, but
we want only the set-image of `(pairIdeal P)^n` to be the basic neighborhoods.

The `RingSubgroupsBasis` approach uses additive subgroups (set-images), which is
exactly the right notion. The leftMul condition (`∀ x ∈ R, ∀ n, ∃ m, x · G_m ⊆ G_n`)
is the only non-trivial check — it requires the **boundedness** argument
characteristic of Tate rings (every element is `π^{-k}` times a "bounded" element,
and `π^{-k} · J^{n+k} ⊆ J^n` because `π ∈ J`).

**Status (Phase 2.2 session 1):**
- Definitions in place: `tateAlgNhd`, `tateAlgBasis` (RingSubgroupsBasis),
  `tateAlgebraTopology`.
- Filter (antitone) and mul-at-0 conditions: PROVED (easy, ideal multiplication).
- LeftMul condition: SORRY pending the boundedness argument.

**References:**
- Wedhorn lecture notes `1910.05934v1.pdf` §6, especially Definitions 6.1, 6.10.
- `docs/plans/2026-04-08-wedhorn-vs-zavyalov.md` Phase 2.2.
-/

section TateAlgebraNaturalTopology

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [NonarchimedeanRing A]

/-- The `n`-th basic neighborhood of `0` in `TateAlgebra A`: the set-image of
`(pairIdeal P)^n` under the inclusion `pairSubring P ↪ TateAlgebra A`,
viewed as an additive subgroup. -/
noncomputable def tateAlgNhd (P : PairOfDefinition A) (n : ℕ) :
    AddSubgroup ↥(TateAlgebra A) :=
  ((pairIdeal P) ^ n).toAddSubgroup.map
    (pairSubring P).subtype.toAddMonoidHom

omit [IsTopologicalRing A] in
/-- The neighborhoods are antitone in `n`. -/
theorem tateAlgNhd_antitone (P : PairOfDefinition A) :
    Antitone (tateAlgNhd P) :=
  fun _ _ h ↦ AddSubgroup.map_mono
    (Submodule.toAddSubgroup_mono (Ideal.pow_le_pow_right h))

omit [IsTopologicalRing A] in
/-- `0 ∈ tateAlgNhd P n` for all `n`. -/
theorem zero_mem_tateAlgNhd (P : PairOfDefinition A) (n : ℕ) :
    (0 : ↥(TateAlgebra A)) ∈ tateAlgNhd P n :=
  ⟨0, ((pairIdeal P) ^ n).zero_mem, map_zero _⟩

/-! #### Sub-task A: coefficient extraction for `tateAlgNhd P n`

We prove that if `y ∈ tateAlgNhd P n`, then every coefficient of `y` (as an
element of `A`) lies in the image of `P.I^n` under `Subtype.val : P.A₀ → A`.

The proof defines an auxiliary ideal of `pairSubring P` — the elements whose
coefficients all lie in the image of a given ideal of `P.A₀` — and shows:
1. This is actually an ideal of `pairSubring P`.
2. It contains the generators of `pairIdeal P` (constant series from `P.I`).
3. Hence it contains `pairIdeal P` itself, and by multiplication properties,
   `(pairIdeal P)^n ⊆ {elements with coeffs in P.I^n}`. -/

/-- Auxiliary ideal: elements of `pairSubring P` all of whose coefficients lie
in the image of a given ideal `I : Ideal P.A₀` under the inclusion `P.A₀ ↪ A`. -/
noncomputable def coeffInIdealIdeal (P : PairOfDefinition A) (I : Ideal P.A₀) :
    Ideal ↥(pairSubring P) where
  carrier := {z | ∀ l, ∃ b : P.A₀, b ∈ I ∧ (b : A) = MvPowerSeries.coeff l z.val.val}
  zero_mem' l := ⟨0, I.zero_mem, by simp⟩
  add_mem' {z w} hz hw l := by
    obtain ⟨b_z, hb_z, heq_z⟩ := hz l
    obtain ⟨b_w, hb_w, heq_w⟩ := hw l
    refine ⟨b_z + b_w, I.add_mem hb_z hb_w, ?_⟩
    show ((b_z + b_w : P.A₀) : A) = MvPowerSeries.coeff l (z + w).val.val
    push_cast
    rw [heq_z, heq_w, ← map_add]
  smul_mem' r z hz l := by
    -- coeff l (r · z) = Σ_{l_1+l_2=l} (coeff l_1 r) · (coeff l_2 z)
    -- For each term: (coeff l_1 r) ∈ A₀, (coeff l_2 z) = (b_{l_2} : A) for b_{l_2} ∈ I.
    -- Product: (coeff l_1 r) · b_{l_2} ∈ I (ideal closure under P.A₀-mul).
    -- We need to assemble this into one element of I.
    classical
    have hr : ∀ l_1, MvPowerSeries.coeff l_1 r.val.val ∈ P.A₀ := r.property
    -- Build the sum witness
    let f : (Fin 1 →₀ ℕ) × (Fin 1 →₀ ℕ) → P.A₀ := fun p =>
      ⟨MvPowerSeries.coeff p.1 r.val.val, hr p.1⟩ *
        (hz p.2).choose
    refine ⟨∑ p ∈ Finset.antidiagonal l, f p, ?_, ?_⟩
    · -- Sum of elements in I is in I
      refine I.sum_mem fun p _ => ?_
      -- Each term is (r-coeff) · (z-coeff), and the z-coeff is in I
      exact I.mul_mem_left _ (hz p.2).choose_spec.1
    · -- The sum equals coeff l (r · z)
      show ((∑ p ∈ Finset.antidiagonal l, f p : P.A₀) : A) =
        MvPowerSeries.coeff l (r • z).val.val
      push_cast [f]
      show (∑ p ∈ Finset.antidiagonal l,
          MvPowerSeries.coeff p.1 r.val.val * ((hz p.2).choose : A)) =
        MvPowerSeries.coeff l (r • z).val.val
      rw [show (r • z).val.val = r.val.val * z.val.val from rfl]
      rw [MvPowerSeries.coeff_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [(hz p.2).choose_spec.2]

omit [IsTopologicalRing A] in
/-- Constant series from `P.I^n` have their unique nonzero coefficient in `P.I^n`. -/
private theorem pairConstantHom_mem_coeffInIdeal (P : PairOfDefinition A) {n : ℕ}
    (c : P.A₀) (hc : c ∈ P.I ^ n) :
    pairConstantHom P c ∈ coeffInIdealIdeal P (P.I ^ n) := by
  intro l
  classical
  by_cases hl : l = 0
  · refine ⟨c, hc, ?_⟩
    show (c : A) = MvPowerSeries.coeff l (pairConstantHom P c).val.val
    subst hl
    show (c : A) = MvPowerSeries.coeff 0 (MvPowerSeries.C (c : A))
    rw [MvPowerSeries.coeff_zero_C]
  · refine ⟨0, (P.I ^ n).zero_mem, ?_⟩
    show ((0 : P.A₀) : A) = MvPowerSeries.coeff l (pairConstantHom P c).val.val
    show (0 : A) = MvPowerSeries.coeff l (MvPowerSeries.C (c : A))
    rw [MvPowerSeries.coeff_C, if_neg hl]

omit [IsTopologicalRing A] in
/-- `pairIdeal P ⊆ coeffInIdealIdeal P P.I`: every element of `pairIdeal P`
has all coefficients in the image of `P.I` under `Subtype.val`. -/
theorem pairIdeal_le_coeffInIdeal (P : PairOfDefinition A) :
    pairIdeal P ≤ coeffInIdealIdeal P P.I := by
  -- pairIdeal P = Ideal.map (pairConstantHom P) P.I. Use `Ideal.map_le_iff_le_comap`
  -- to reduce to: every `c ∈ P.I` has `pairConstantHom c ∈ coeffInIdealIdeal P P.I`.
  unfold pairIdeal
  rw [Ideal.map_le_iff_le_comap]
  intro c hc
  show pairConstantHom P c ∈ coeffInIdealIdeal P P.I
  have h1 : c ∈ P.I ^ 1 := by rw [pow_one]; exact hc
  have := pairConstantHom_mem_coeffInIdeal P (n := 1) c h1
  convert this using 1
  rw [pow_one]

omit [IsTopologicalRing A] in
/-- The auxiliary ideal is compatible with ideal multiplication in `P.A₀`:
if `J_1 ⊆ coeffInIdealIdeal I_1` and `J_2 ⊆ coeffInIdealIdeal I_2`, then
`J_1 · J_2 ⊆ coeffInIdealIdeal (I_1 · I_2)`. -/
theorem coeffInIdealIdeal_mul_mono (P : PairOfDefinition A) {I₁ I₂ : Ideal P.A₀}
    {J₁ J₂ : Ideal ↥(pairSubring P)}
    (h₁ : J₁ ≤ coeffInIdealIdeal P I₁) (h₂ : J₂ ≤ coeffInIdealIdeal P I₂) :
    J₁ * J₂ ≤ coeffInIdealIdeal P (I₁ * I₂) := by
  intro z hz
  refine Submodule.mul_induction_on hz ?_ ?_
  · -- Case: product a * b with a ∈ J₁, b ∈ J₂
    intro a ha b hb l
    classical
    -- Use h₁ on a and h₂ on b to get coefficient witnesses
    have ha' : a ∈ coeffInIdealIdeal P I₁ := h₁ ha
    have hb' : b ∈ coeffInIdealIdeal P I₂ := h₂ hb
    -- Build the sum witness for coeff l (a * b)
    let f : (Fin 1 →₀ ℕ) × (Fin 1 →₀ ℕ) → P.A₀ := fun p =>
      (ha' p.1).choose * (hb' p.2).choose
    refine ⟨∑ p ∈ Finset.antidiagonal l, f p, ?_, ?_⟩
    · refine (I₁ * I₂).sum_mem fun p _ => ?_
      exact Ideal.mul_mem_mul (ha' p.1).choose_spec.1 (hb' p.2).choose_spec.1
    · show ((∑ p ∈ Finset.antidiagonal l, f p : P.A₀) : A) =
        MvPowerSeries.coeff l (a * b).val.val
      push_cast [f]
      show (∑ p ∈ Finset.antidiagonal l,
          ((ha' p.1).choose : A) * ((hb' p.2).choose : A)) =
        MvPowerSeries.coeff l (a * b).val.val
      rw [show (a * b).val.val = a.val.val * b.val.val from rfl]
      rw [MvPowerSeries.coeff_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [(ha' p.1).choose_spec.2, (hb' p.2).choose_spec.2]
  · -- Case: z₁ + z₂ both with the property
    intro z₁ z₂ h₁' h₂' l
    obtain ⟨b₁, hb₁, heq₁⟩ := h₁' l
    obtain ⟨b₂, hb₂, heq₂⟩ := h₂' l
    refine ⟨b₁ + b₂, (I₁ * I₂).add_mem hb₁ hb₂, ?_⟩
    show ((b₁ : A) + (b₂ : A)) = MvPowerSeries.coeff l (z₁ + z₂).val.val
    rw [show (z₁ + z₂).val.val = z₁.val.val + z₂.val.val from rfl, map_add,
      ← heq₁, ← heq₂]

omit [IsTopologicalRing A] in
/-- `(pairIdeal P)^n ⊆ coeffInIdealIdeal P (P.I^n)`: elements of `(pairIdeal P)^n`
have all coefficients in the image of `P.I^n` under `Subtype.val`. -/
theorem pairIdeal_pow_le_coeffInIdeal (P : PairOfDefinition A) (n : ℕ) :
    (pairIdeal P) ^ n ≤ coeffInIdealIdeal P (P.I ^ n) := by
  induction n with
  | zero =>
    -- (pairIdeal P)^0 = ⊤ and P.I^0 = ⊤.
    intro z _ l
    refine ⟨⟨MvPowerSeries.coeff l z.val.val, z.property l⟩, ?_, rfl⟩
    -- Goal: ⟨..., ...⟩ ∈ P.I ^ 0. Since P.I^0 = 1 = ⊤, this is trivial.
    simp only [pow_zero, Ideal.one_eq_top, Submodule.mem_top]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact coeffInIdealIdeal_mul_mono P ih (pairIdeal_le_coeffInIdeal P)

omit [IsTopologicalRing A] in
/-- **Sub-task A (main result):** if `y ∈ tateAlgNhd P n`, then every coefficient
of `y` (as an element of `A` via `MvPowerSeries.coeff`) lies in the image of
`P.I^n` under `Subtype.val`. -/
theorem tateAlgNhd_coeff_mem (P : PairOfDefinition A) (n : ℕ)
    {y : ↥(TateAlgebra A)} (hy : y ∈ tateAlgNhd P n) (l : Fin 1 →₀ ℕ) :
    ∃ b : P.A₀, b ∈ P.I ^ n ∧ (b : A) = MvPowerSeries.coeff l y.val := by
  obtain ⟨z, hz, rfl⟩ := hy
  -- y = ↑z, so y.val = z.val.val
  have := pairIdeal_pow_le_coeffInIdeal P n hz l
  show ∃ b, b ∈ P.I ^ n ∧ (b : A) =
    MvPowerSeries.coeff l ((pairSubring P).subtype.toAddMonoidHom z).val
  exact this

omit [IsTopologicalRing A] in
/-- The product `tateAlgNhd P n · tateAlgNhd P n ⊆ tateAlgNhd P n`, because
`(pairIdeal P)^n · (pairIdeal P)^n ⊆ (pairIdeal P)^(2n) ⊆ (pairIdeal P)^n`. -/
private theorem tateAlgNhd_mul (P : PairOfDefinition A) (i : ℕ) :
    ∃ j, (tateAlgNhd P j : Set ↥(TateAlgebra A)) *
      (tateAlgNhd P j : Set ↥(TateAlgebra A)) ⊆
        (tateAlgNhd P i : Set ↥(TateAlgebra A)) := by
  refine ⟨i, ?_⟩
  rintro _ ⟨_, ⟨d₁, hd₁, rfl⟩, _, ⟨d₂, hd₂, rfl⟩, rfl⟩
  refine ⟨d₁ * d₂, ?_, MulMemClass.coe_mul ..⟩
  exact Ideal.pow_le_pow_right (Nat.le_add_left i i)
    (pow_add (pairIdeal P) i i ▸ Ideal.mul_mem_mul hd₁ hd₂)

/-! #### Sub-tasks B and C: I-adic continuity + almost-all-coeffs -/

omit [NonarchimedeanRing A] in
/-- **Sub-task B:** For any `a ∈ A` and any `n : ℕ`, there exists `m : ℕ` such
that `a · b ∈ image of P.I^n` (under `Subtype.val`) whenever `b ∈ image of P.I^m`.

This is the continuity of left-multiplication by `a` at `0` in A's topology,
applied to the neighborhood `image of P.I^n`. -/
theorem exists_mul_pow_subset_pow (P : PairOfDefinition A) (a : A) (n : ℕ) :
    ∃ m : ℕ, ∀ b : P.A₀, b ∈ P.I ^ m →
      ∃ c : P.A₀, c ∈ P.I ^ n ∧ (c : A) = a * (b : A) := by
  -- The image of `P.I^n` under `Subtype.val : P.A₀ → A` is a nhd of 0 in A
  -- (by `P.hasBasis_nhds_zero`).
  have hU : (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀)) ∈ nhds (0 : A) :=
    P.hasBasis_nhds_zero.mem_of_mem trivial
  -- By continuity of `(a * ·)` at 0, the preimage is also a nhd of 0.
  have hcont : Continuous fun b : A => a * b := continuous_const.mul continuous_id
  have hV : (fun b : A => a * b) ⁻¹' (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀)) ∈
      nhds (0 : A) := by
    have h0 : (0 : A) ∈ (fun b : A => a * b) ⁻¹' (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀)) := by
      simp only [Set.mem_preimage, mul_zero]
      exact ⟨0, (P.I ^ n).zero_mem, rfl⟩
    exact hcont.continuousAt.preimage_mem_nhds (by
      rw [show (a * (0 : A)) = (0 : A) from mul_zero a]
      exact hU)
  -- Extract m from the basis.
  obtain ⟨m, -, hm⟩ := P.hasBasis_nhds_zero.mem_iff.mp hV
  refine ⟨m, fun b hb => ?_⟩
  -- b ∈ P.I^m, goal: ∃ c ∈ P.I^n, (c : A) = a * (b : A).
  have hbA : (b : A) ∈ (Subtype.val '' ((P.I ^ m : Ideal P.A₀) : Set P.A₀)) :=
    ⟨b, hb, rfl⟩
  have := hm hbA
  simp only [Set.mem_preimage, Set.mem_image] at this
  obtain ⟨c, hc, heq⟩ := this
  exact ⟨c, hc, heq⟩

/-- **Sub-task C:** For `x ∈ TateAlgebra A` and `n : ℕ`, eventually every
coefficient of `x` lies in `image of P.I^n` under `Subtype.val`. Equivalently,
`{l : Fin 1 →₀ ℕ | coeff l x ∉ image of P.I^n}` is cofinite.

This follows from `x` being a restricted power series (`coeff l x → 0` cofinitely
in A) and `image of P.I^n` being a neighborhood of `0` in A. -/
theorem tateAlgebra_coeff_eventually_in_pow (P : PairOfDefinition A)
    (x : ↥(TateAlgebra A)) (n : ℕ) :
    ∀ᶠ (l : Fin 1 →₀ ℕ) in Filter.cofinite,
      MvPowerSeries.coeff l x.val ∈
        (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀) : Set A) := by
  -- x is restricted, so its coefficients converge to 0 cofinitely.
  have hres : Filter.Tendsto
      (fun l : Fin 1 →₀ ℕ => MvPowerSeries.coeff l x.val)
      Filter.cofinite (nhds (0 : A)) := x.property
  -- The target set is a nhd of 0 in A.
  have hU : (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀) : Set A) ∈ nhds (0 : A) :=
    P.hasBasis_nhds_zero.mem_of_mem trivial
  exact hres hU

/-! #### Sub-task D: Reverse coefficient characterization (principal case)

For the principal case `P.I = (π : P.A₀)` with `π` a unit in `A`, we can
directly reconstruct membership in `(pairIdeal P)^n` from the coefficient
condition. The key observation: `y = π^n · g` where `g` is the "divided"
series `π^{-n} · y` (using the inverse of `π` in `A`).

The element `g` has coefficients in `P.A₀` (because each `y_l = a_l · π^n`
in `P.A₀`, and `π^{-n} · y_l = a_l ∈ P.A₀`). It's automatically restricted
because it's the product of `y` (a restricted series) with the constant
series `π^{-n}` in `TateAlgebra A`.
-/

omit [IsTopologicalRing A] in
/-- **Sub-task D (principal case):** if `P.I = (π)` for some `π ∈ P.A₀` that
is a unit in `A`, and `y ∈ pairSubring P` has all coefficients in the image
of `P.I^n`, then `y ∈ tateAlgNhd P n` (i.e., `⟨y, hy_pair⟩ ∈ (pairIdeal P)^n`).

The principal-pair hypothesis is needed to use `Ideal.mem_span_singleton` for
the decomposition `b_l = a_l * π^n`. The topologically-nilpotent-unit hypothesis
is needed for `π` to be invertible in `A` (so we can construct the "divided"
series `g = π^{-n} · y`). -/
theorem tateAlgNhd_of_coeff_mem_principal (P : PairOfDefinition A) (n : ℕ)
    (π : P.A₀) (hπ_gen : P.I = Ideal.span {π})
    (hπ_unit : IsUnit ((π : A)))
    {y : ↥(TateAlgebra A)} (hy_pair : y ∈ pairSubring P)
    (hy_coeff : ∀ l : Fin 1 →₀ ℕ, ∃ b : P.A₀, b ∈ P.I ^ n ∧
      (b : A) = MvPowerSeries.coeff l y.val) :
    y ∈ tateAlgNhd P n := by
  classical
  -- Step 1: Define πinv, the inverse of π in A.
  let πinv : A := ↑hπ_unit.unit⁻¹
  have hπinv_mul : (π : A) * πinv = 1 := hπ_unit.mul_val_inv
  have hπinv_pow : (π : A) ^ n * πinv ^ n = 1 := by
    rw [← mul_pow, hπinv_mul, one_pow]
  -- Step 2: P.I ^ n = span {π^n}
  have hpow : (P.I ^ n : Ideal P.A₀) = Ideal.span {π ^ n} := by
    rw [hπ_gen, Ideal.span_singleton_pow]
  -- Step 3: Define the "divided" series g = (C πinv^n) * y in TateAlgebra A.
  let g_val : ↥(TateAlgebra A) := algebraMap A ↥(TateAlgebra A) (πinv ^ n) * y
  -- Step 4: g_val ∈ pairSubring P (all coefficients are in P.A₀)
  have hg_in : g_val ∈ pairSubring P := by
    intro l
    -- coeff l g_val = πinv^n * coeff l y.val
    have hcoeff_g : MvPowerSeries.coeff l g_val.val = πinv ^ n * MvPowerSeries.coeff l y.val := by
      show MvPowerSeries.coeff l
        (((algebraMap A ↥(TateAlgebra A)) (πinv ^ n) * y).val) = _
      show MvPowerSeries.coeff l
        ((MvPowerSeries.C (πinv ^ n) : MvPowerSeries (Fin 1) A) * y.val) = _
      rw [MvPowerSeries.coeff_C_mul]
    show MvPowerSeries.coeff l g_val.val ∈ P.A₀
    rw [hcoeff_g]
    -- coeff l y.val = (b_l : A) for b_l ∈ P.I^n = span{π^n}, so b_l = a_l * π^n
    obtain ⟨b, hb_mem, hb_eq⟩ := hy_coeff l
    rw [← hb_eq]
    rw [hpow] at hb_mem
    obtain ⟨a, ha_eq⟩ := Ideal.mem_span_singleton.mp hb_mem
    -- b = π^n * a (Ideal.mem_span_singleton gives the multiple form)
    rw [ha_eq]
    -- Goal: πinv^n * ((π^n * a : P.A₀) : A) ∈ P.A₀
    show πinv ^ n * ((π ^ n * a : P.A₀) : A) ∈ P.A₀
    have : πinv ^ n * ((π ^ n * a : P.A₀) : A) = (a : A) := by
      push_cast
      rw [show πinv ^ n * ((π : A) ^ n * (a : A)) = ((π : A) ^ n * πinv ^ n) * (a : A) by ring,
        hπinv_pow, one_mul]
    rw [this]
    exact a.property
  -- Step 5: y = pairConstantHom(π^n) * g_in_subring in pairSubring P.
  let g_in_subring : ↥(pairSubring P) := ⟨g_val, hg_in⟩
  have hy_eq : (⟨y, hy_pair⟩ : ↥(pairSubring P)) = pairConstantHom P (π ^ n) * g_in_subring := by
    apply Subtype.ext
    apply Subtype.ext
    -- Both sides as MvPowerSeries (Fin 1) A
    ext l
    show MvPowerSeries.coeff l y.val =
      MvPowerSeries.coeff l
        ((pairConstantHom P (π ^ n) * g_in_subring : ↥(pairSubring P)) : ↥(TateAlgebra A)).val
    -- RHS = coeff l ((pairConstantHom (π^n)).val * g_val.val)
    -- = coeff l (C (π^n : A) * (C (πinv^n) * y.val))
    -- = coeff l (C ((π^n : A) * πinv^n) * y.val)
    -- = coeff l (C 1 * y.val) = coeff l y.val
    show MvPowerSeries.coeff l y.val =
      MvPowerSeries.coeff l
        ((MvPowerSeries.C ((π : A) ^ n)) * g_val.val)
    change MvPowerSeries.coeff l y.val =
      MvPowerSeries.coeff l ((MvPowerSeries.C ((π : A) ^ n)) *
        ((MvPowerSeries.C (πinv ^ n)) * y.val))
    rw [← mul_assoc, ← map_mul, hπinv_pow, map_one, one_mul]
  -- Step 6: Conclude y ∈ tateAlgNhd P n.
  refine ⟨⟨y, hy_pair⟩, ?_, rfl⟩
  rw [hy_eq]
  -- (pairConstantHom(π^n) * g_in_subring) ∈ (pairIdeal P)^n
  have hπ_in : pairConstantHom P π ∈ pairIdeal P := by
    unfold pairIdeal
    exact Ideal.mem_map_of_mem _
      (by rw [hπ_gen]; exact Ideal.mem_span_singleton_self π)
  have hπn_in : pairConstantHom P (π ^ n) ∈ (pairIdeal P) ^ n := by
    rw [map_pow]
    exact Ideal.pow_mem_pow hπ_in n
  exact ((pairIdeal P) ^ n).mul_mem_right g_in_subring hπn_in

omit [IsTopologicalRing A] in
/-- **Easy case of leftMul:** when `x ∈ pairSubring P`, multiplication by `x`
preserves the basic neighborhoods because they are images of ideals of
`pairSubring P`, which are closed under multiplication by elements of
`pairSubring P`. Take `j = i`. -/
private theorem tateAlgNhd_leftMul_of_mem (P : PairOfDefinition A)
    {x : ↥(TateAlgebra A)} (hx : x ∈ pairSubring P) (i : ℕ) :
    (tateAlgNhd P i : Set ↥(TateAlgebra A)) ⊆
      (x * ·) ⁻¹' (tateAlgNhd P i : Set ↥(TateAlgebra A)) := by
  rintro _ ⟨y, hy, rfl⟩
  -- `x · ↑y = ↑(⟨x, hx⟩ * y)` and `⟨x, hx⟩ * y ∈ (pairIdeal P)^i` because
  -- ideals are closed under left multiplication by ring elements.
  refine ⟨⟨x, hx⟩ * y, ?_, ?_⟩
  · exact ((pairIdeal P) ^ i).mul_mem_left ⟨x, hx⟩ hy
  · exact MulMemClass.coe_mul ..

/-- **Sub-task F (assembly): the leftMul condition for a principal pair.**

For a principal pair `P.I = (π : P.A₀)` with `π` a unit in `A`, the condition
`∃ j, x · tateAlgNhd P j ⊆ tateAlgNhd P i` holds for every `x ∈ TateAlgebra A`
and every `i : ℕ`.

**Proof:** Using Sub-tasks A (forward coefficient extraction), B (I-adic
continuity), C (restricted series convergence), and D (reverse coefficient
characterization, principal case):
1. By Sub-task C, `S := {l : coeff l x ∉ image P.I^i}` is finite.
2. For each `l ∈ S`, Sub-task B gives `m_l` with `coeff l x · image P.I^{m_l} ⊆ image P.I^i`.
3. Take `j := max(i, sup {m_l : l ∈ S})` (over the finite set).
4. For `y ∈ tateAlgNhd P j`: Sub-task A gives all coefficients of `y` in image P.I^j.
5. Compute coefficients of `x · y` via `MvPowerSeries.coeff_mul`:
   `(x · y)_k = Σ_{l+m=k} (coeff l x) · (coeff m y)`.
   Each term is in image P.I^i (splitting on `l ∈ S` vs `l ∉ S`).
6. Hence all coefficients of `x · y` are in image P.I^i. Since these are in
   P.A₀, `x · y ∈ pairSubring P`.
7. By Sub-task D (principal case), `x · y ∈ (pairIdeal P)^i`, i.e.,
   `x · y ∈ tateAlgNhd P i`. -/
theorem tateAlgNhd_leftMul_of_principal [IsTateRing A] (P : PairOfDefinition A)
    (π : P.A₀) (hπ_gen : P.I = Ideal.span {π})
    (hπ_unit : IsUnit ((π : A)))
    (x : ↥(TateAlgebra A)) (i : ℕ) :
    ∃ j, (tateAlgNhd P j : Set ↥(TateAlgebra A)) ⊆
      (x * ·) ⁻¹' (tateAlgNhd P i : Set ↥(TateAlgebra A)) := by
  classical
  -- Step 1: Find the finite set S of "bad" indices (coeff l x ∉ image P.I^i).
  have hS : ∀ᶠ (l : Fin 1 →₀ ℕ) in Filter.cofinite,
      MvPowerSeries.coeff l x.val ∈
        (Subtype.val '' ((P.I ^ i : Ideal P.A₀) : Set P.A₀) : Set A) :=
    tateAlgebra_coeff_eventually_in_pow P x i
  -- Extract the finite set where the condition fails.
  set S : Set (Fin 1 →₀ ℕ) := {l |
    MvPowerSeries.coeff l x.val ∉
      (Subtype.val '' ((P.I ^ i : Ideal P.A₀) : Set P.A₀) : Set A)} with hS_def
  have hS_finite : S.Finite := hS
  -- Step 2: For each l ∈ S, find m_l via Sub-task B.
  let m_fn : (Fin 1 →₀ ℕ) → ℕ := fun (l : Fin 1 →₀ ℕ) =>
    (exists_mul_pow_subset_pow P (MvPowerSeries.coeff l x.val) i).choose
  have hm_spec : ∀ (l : Fin 1 →₀ ℕ), ∀ b : P.A₀, b ∈ P.I ^ (m_fn l) →
      ∃ c : P.A₀, c ∈ P.I ^ i ∧ (c : A) = MvPowerSeries.coeff l x.val * (b : A) :=
    fun l => (exists_mul_pow_subset_pow P (MvPowerSeries.coeff l x.val) i).choose_spec
  -- Step 3: Take j := max(i, sup {m_l : l ∈ S}).
  let j : ℕ := max i (hS_finite.toFinset.sup m_fn)
  have hj_ge_i : i ≤ j := le_max_left _ _
  have hj_ge_m : ∀ l ∈ hS_finite.toFinset, m_fn l ≤ j := fun l hl =>
    le_max_of_le_right (Finset.le_sup hl)
  refine ⟨j, ?_⟩
  -- Step 4: For y with ↑y ∈ tateAlgNhd P j, show x * ↑y ∈ tateAlgNhd P i.
  rintro _ ⟨y, hy, rfl⟩
  change (x * (pairSubring P).subtype y) ∈ tateAlgNhd P i
  -- From Sub-task A: coefficients of y lie in image P.I^j.
  have hy_coeff : ∀ l, ∃ b : P.A₀, b ∈ P.I ^ j ∧
      (b : A) = MvPowerSeries.coeff l ((pairSubring P).subtype y).val :=
    pairIdeal_pow_le_coeffInIdeal P j hy
  set xy : ↥(TateAlgebra A) := x * (pairSubring P).subtype y with hxy_def
  -- **Key claim:** every coefficient of xy is in the image of P.I^i.
  -- For each antidiagonal pair p = (p.1, p.2), the product
  -- `(coeff p.1 x) * (coeff p.2 y)` is in image P.I^i, with a concrete
  -- P.A₀ witness `term_of p`. Define this witness first.
  have hterm : ∀ p : (Fin 1 →₀ ℕ) × (Fin 1 →₀ ℕ),
      ∃ c : P.A₀, c ∈ P.I ^ i ∧
        (c : A) = MvPowerSeries.coeff p.1 x.val * MvPowerSeries.coeff p.2 y.val.val := by
    intro p
    -- Extract the y-coefficient witness (in P.I^j).
    obtain ⟨b_p, hb_p_mem, hb_p_eq⟩ := hy_coeff p.2
    by_cases hp : p.1 ∈ S
    · -- Bad case: use Sub-task B via `hm_spec`.
      have hb_lower : b_p ∈ P.I ^ (m_fn p.1) := by
        have hle : m_fn p.1 ≤ j := hj_ge_m p.1 (hS_finite.mem_toFinset.mpr hp)
        exact Ideal.pow_le_pow_right hle hb_p_mem
      obtain ⟨c, hc_mem, hc_eq⟩ := hm_spec p.1 b_p hb_lower
      refine ⟨c, hc_mem, ?_⟩
      rw [hc_eq, hb_p_eq]
      rfl
    · -- Good case: coeff p.1 x is already in image P.I^i.
      rw [hS_def] at hp
      simp only [Set.mem_setOf_eq, not_not] at hp
      obtain ⟨a, ha_mem, ha_eq⟩ := hp
      refine ⟨a * b_p, Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hj_ge_i hb_p_mem), ?_⟩
      push_cast
      rw [ha_eq, hb_p_eq]
      rfl
  -- Assemble the sum witness for each coefficient of xy.
  have hxy_coeff : ∀ l, ∃ c : P.A₀, c ∈ P.I ^ i ∧
      (c : A) = MvPowerSeries.coeff l xy.val := by
    intro l
    -- coeff l xy = Σ_p (coeff p.1 x) * (coeff p.2 y) over antidiagonal.
    have hcoeff : MvPowerSeries.coeff l xy.val =
        ∑ p ∈ Finset.antidiagonal l,
          MvPowerSeries.coeff p.1 x.val * MvPowerSeries.coeff p.2 y.val.val := by
      change MvPowerSeries.coeff l (x.val * y.val.val) = _
      rw [MvPowerSeries.coeff_mul]
    -- Build the sum witness in P.A₀.
    refine ⟨∑ p ∈ Finset.antidiagonal l, (hterm p).choose, ?_, ?_⟩
    · -- Sum of elements of P.I^i stays in P.I^i.
      exact (P.I ^ i).sum_mem fun p _ => (hterm p).choose_spec.1
    · -- Coerce and match with coeff l xy.
      rw [hcoeff]
      push_cast
      refine Finset.sum_congr rfl fun p _ => ?_
      exact (hterm p).choose_spec.2
  -- Coefficient condition implies `xy ∈ pairSubring P` (since P.I^i ⊆ P.A₀).
  have hxy_pair : xy ∈ pairSubring P := by
    intro l
    obtain ⟨c, _, hc_eq⟩ := hxy_coeff l
    rw [← hc_eq]
    exact c.property
  -- Apply Sub-task D (principal case) to conclude.
  exact tateAlgNhd_of_coeff_mem_principal P i π hπ_gen hπ_unit hxy_pair hxy_coeff

omit [IsTopologicalRing A] in
/-- **The leftMul condition (Phase 2.2):** for every `x ∈ TateAlgebra A` and
every `i : ℕ`, there exists `j` with `x · tateAlgNhd P j ⊆ tateAlgNhd P i`.

This is the general-pair version, derived from the principal-pair version
`tateAlgNhd_leftMul_of_principal` via Wedhorn 6.14 (any Tate ring admits a
principal pair of definition). Phase 2.2 session 2 supplies the principal
case; the reduction to the general case via Wedhorn 6.14 is deferred.

For now, we state the general theorem with an explicit principal-pair
hypothesis passed via `IsTateRing`. This matches the typical usage pattern
where downstream consumers supply an appropriate principal pair. -/
theorem tateAlgNhd_leftMul [IsTateRing A] (P : PairOfDefinition A)
    (π : P.A₀) (hπ_gen : P.I = Ideal.span {π})
    (hπ_unit : IsUnit ((π : A)))
    (x : ↥(TateAlgebra A)) (i : ℕ) :
    ∃ j, (tateAlgNhd P j : Set ↥(TateAlgebra A)) ⊆
      (x * ·) ⁻¹' (tateAlgNhd P i : Set ↥(TateAlgebra A)) :=
  tateAlgNhd_leftMul_of_principal P π hπ_gen hπ_unit x i

/-- The `RingSubgroupsBasis` for the natural Tate topology on `TateAlgebra A`.
Requires a principal pair of definition. -/
noncomputable def tateAlgBasis [IsTateRing A] (P : PairOfDefinition A)
    (π : P.A₀) (hπ_gen : P.I = Ideal.span {π})
    (hπ_unit : IsUnit ((π : A))) :
    RingSubgroupsBasis (tateAlgNhd P) :=
  .of_comm _
    (fun i j ↦ ⟨max i j,
      le_inf (tateAlgNhd_antitone P (le_max_left i j))
        (tateAlgNhd_antitone P (le_max_right i j))⟩)
    (tateAlgNhd_mul P)
    (tateAlgNhd_leftMul P π hπ_gen hπ_unit)

/-- The natural Tate topology on `TateAlgebra A`, with `0`-neighborhoods
`{set-image of (pairIdeal P)^n}`. Requires a principal pair of definition. -/
@[reducible] noncomputable def tateAlgebraTopology [IsTateRing A]
    (P : PairOfDefinition A) (π : P.A₀) (hπ_gen : P.I = Ideal.span {π})
    (hπ_unit : IsUnit ((π : A))) :
    TopologicalSpace ↥(TateAlgebra A) :=
  (tateAlgBasis P π hπ_gen hπ_unit).topology

omit [IsTopologicalRing A] in
/-- The natural Tate topology is a ring topology. -/
theorem tateAlgebraTopology_isTopologicalRing [IsTateRing A]
    (P : PairOfDefinition A) (π : P.A₀) (hπ_gen : P.I = Ideal.span {π})
    (hπ_unit : IsUnit ((π : A))) :
    @IsTopologicalRing ↥(TateAlgebra A) (tateAlgebraTopology P π hπ_gen hπ_unit) _ :=
  (tateAlgBasis P π hπ_gen hπ_unit).toRingFilterBasis.isTopologicalRing

omit [IsTopologicalRing A] in
/-- `tateAlgNhd P n` (as a set in `TateAlgebra A`) is contained in `pairSubring P`,
because each basic neighborhood is the image of an ideal of `pairSubring P` under
the subring inclusion. -/
theorem tateAlgNhd_le_pairSubring (P : PairOfDefinition A) (n : ℕ) :
    (tateAlgNhd P n : Set ↥(TateAlgebra A)) ⊆
      (pairSubring P : Set ↥(TateAlgebra A)) := by
  rintro _ ⟨y, _, rfl⟩
  exact y.property

omit [IsTopologicalRing A] in
/-- `pairSubring P` is open in `TateAlgebra A` with the natural Tate topology.
The subgroup `tateAlgNhd P 1 = image of pairIdeal P` is a basic neighborhood of `0`
contained in `pairSubring P`. -/
theorem pairSubring_isOpen [IsTateRing A] (P : PairOfDefinition A)
    (π : P.A₀) (hπ_gen : P.I = Ideal.span {π}) (hπ_unit : IsUnit ((π : A))) :
    @IsOpen ↥(TateAlgebra A) (tateAlgebraTopology P π hπ_gen hπ_unit)
      ((pairSubring P : Subring ↥(TateAlgebra A)) : Set ↥(TateAlgebra A)) := by
  letI : TopologicalSpace ↥(TateAlgebra A) := tateAlgebraTopology P π hπ_gen hπ_unit
  haveI := tateAlgebraTopology_isTopologicalRing P π hπ_gen hπ_unit
  refine (pairSubring P).toAddSubgroup.isOpen_of_mem_nhds (g := 0) ?_
  refine Filter.mem_of_superset
    ((tateAlgBasis P π hπ_gen hπ_unit).hasBasis_nhds_zero.mem_of_mem (i := 1) trivial) ?_
  exact tateAlgNhd_le_pairSubring P 1

/-! ### Unparameterized canonical natural Tate topology

Using `IsTateRing.principalPair` (via `exists_principal_pairOfDefinition`,
Wedhorn 6.14), we get a canonical principal pair of definition and hence a
canonical natural Tate topology on `TateAlgebra A`, without needing to supply
a pair of definition explicitly. -/

/-- The canonical `RingSubgroupsBasis` for the natural Tate topology on
`TateAlgebra A`, using `IsTateRing.principalPair` via Wedhorn 6.14. -/
noncomputable def tateAlgBasis' [IsTateRing A] :
    RingSubgroupsBasis (tateAlgNhd (IsTateRing.principalPair A).toPairOfDefinition) :=
  let P := IsTateRing.principalPair A
  tateAlgBasis P.toPairOfDefinition P.π P.I_eq_span P.π_isUnit

/-- The canonical natural Tate topology on `TateAlgebra A` for any Tate ring `A`.
Uses the canonical principal pair of definition `IsTateRing.principalPair A`
supplied by Wedhorn 6.14. -/
@[reducible] noncomputable def tateAlgebraTopology' [IsTateRing A] :
    TopologicalSpace ↥(TateAlgebra A) :=
  tateAlgBasis' (A := A).topology

omit [IsTopologicalRing A] in
/-- The canonical natural Tate topology is a ring topology. -/
theorem tateAlgebraTopology'_isTopologicalRing [IsTateRing A] :
    @IsTopologicalRing ↥(TateAlgebra A) tateAlgebraTopology' _ :=
  tateAlgBasis'.toRingFilterBasis.isTopologicalRing

omit [IsTopologicalRing A] in
/-- `pairSubring (IsTateRing.principalPair A).toPairOfDefinition` is open in the
canonical natural Tate topology. -/
theorem pairSubring_principalPair_isOpen' [IsTateRing A] :
    @IsOpen ↥(TateAlgebra A) tateAlgebraTopology'
      ((pairSubring (IsTateRing.principalPair A).toPairOfDefinition :
        Subring ↥(TateAlgebra A)) : Set ↥(TateAlgebra A)) :=
  let P := IsTateRing.principalPair A
  pairSubring_isOpen P.toPairOfDefinition P.π P.I_eq_span P.π_isUnit

end TateAlgebraNaturalTopology

end TateAlgebra
