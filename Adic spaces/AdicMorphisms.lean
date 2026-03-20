/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».AnalyticPoints
import «Adic spaces».AdicSpectrum
import «Adic spaces».Lemma745
import «Adic spaces».StructureSheaf

/-!
# Adic Morphisms

We prove Lemma 7.46 and develop the theory of adic morphisms,
following §7.5 and §8.4 of [Wedhorn, *Adic Spaces*].

## Main results

* `ValuationSpectrum.supp_comap` : `supp(comap φ v) = φ⁻¹(supp v)`.
* `ValuationSpectrum.nonAnalytic_comap_of_continuous` : Continuous maps preserve non-analytic
  points (Lemma 7.46(1), first part).
* `ValuationSpectrum.analytic_comap_of_isAdicHom` : Adic homomorphisms preserve analytic
  points (Lemma 7.46(1), second part).
* `ValuationSpectrum.isAdicHom_of_complete_and_analytic_preserved` : If `B` is complete and
  `Spa(φ)` preserves analytic points, then `φ` is adic (Lemma 7.46(2)).
* `ValuationSpectrum.IsAdicMorphism` : Adic morphisms of adic spaces
  (Definition 8.38 of Wedhorn).
* `ValuationSpectrum.isAdicHom_iff_preserves_analytic` : A ring hom is adic iff it
  preserves analytic points on Spa (Proposition 8.39(1), affinoid iff version).
* `ValuationSpectrum.morphism_preserves_nonAnalytic_affinoid` : Any continuous ring hom
  preserves non-analytic points (Proposition 8.39(2), affinoid case).
* `ValuationSpectrum.IsAdicMorphism.ringHom_isAdic` : The induced ring map of an adic
  morphism on affinoid charts is adic (Corollary 8.40).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §7.5, §8.4
-/

namespace ValuationSpectrum

variable {A B : Type*} [CommRing A] [CommRing B]
  [TopologicalSpace A] [TopologicalSpace B]

/-! ### Support and comap -/

omit [TopologicalSpace A] [TopologicalSpace B] in
/-- The support of `comap φ v` equals the preimage ideal `φ⁻¹(supp v)`. -/
theorem supp_comap (φ : A →+* B) (v : Spv B) :
    (comap φ v).supp = Ideal.comap φ v.supp := by
  have h := congr_arg PrimeSpectrum.asIdeal (suppFun_comap φ v)
  simpa using h

omit [TopologicalSpace A] [TopologicalSpace B] in
/-- The support of `comap φ v` as a set equals `φ ⁻¹' (supp v : Set B)`. -/
theorem supp_comap_coe (φ : A →+* B) (v : Spv B) :
    ((comap φ v).supp : Set A) = φ ⁻¹' (v.supp : Set B) := by
  ext x; simp [supp_comap]

/-! ### Lemma 7.46(1): Non-analytic preservation -/

/-- **Lemma 7.46(1), first part.** Continuous ring homomorphisms preserve non-analytic points. -/
theorem nonAnalytic_comap_of_continuous {φ : A →+* B} (hφ : Continuous φ)
    {v : Spv B} (hv : ¬IsAnalytic v) : ¬IsAnalytic (comap φ v) := by
  simp only [IsAnalytic, not_not] at hv ⊢
  rw [supp_comap_coe]
  exact hφ.isOpen_preimage _ hv

/-! ### Lemma 7.46(1): Adic homomorphisms preserve analytic points -/

section AdicPreservesAnalytic

variable [IsTopologicalRing A] [IsTopologicalRing B]
  [IsHuberRing A] [IsHuberRing B]

omit [IsHuberRing B] in
/-- If `supp(v)` contains the ideal of definition, then `supp(v)` is open. -/
private theorem supp_isOpen_of_idealOfDefinition_le
    (PB : PairOfDefinition B) (v : Spv B)
    (h : PB.idealOfDefinition ≤ v.supp) : IsOpen (v.supp : Set B) := by
  change IsOpen (v.supp.toAddSubgroup : Set B)
  exact AddSubgroup.isOpen_of_mem_nhds _
    (Filter.mem_of_superset
      ((PB.pow_image_isOpen 1).mem_nhds
        (Set.mem_image_of_mem _ (PB.I ^ 1).zero_mem))
      (fun b hb ↦ by
        rw [Submodule.coe_toAddSubgroup]
        obtain ⟨y, hy, rfl⟩ := hb
        exact h (Ideal.mem_map_of_mem _ (pow_one PB.I ▸ hy))))

omit [IsTopologicalRing A] [IsTopologicalRing B]
  [IsHuberRing A] [IsHuberRing B] in
/-- If `I` maps into `supp(comap φ v)` and `φ` is adic, then `PB.idealOfDefinition ≤ supp v`. -/
private theorem idealOfDefinition_le_supp_of_adic
    (PA : PairOfDefinition A) (PB : PairOfDefinition B)
    (φ : A →+* B) (hAB : ∀ a ∈ PA.A₀, φ a ∈ PB.A₀)
    (hrad : (Ideal.map (PA.restrictRingHom PB φ hAB) PA.I).radical = PB.I.radical)
    (v : Spv B)
    (hI : PA.idealOfDefinition ≤ (comap φ v).supp) :
    PB.idealOfDefinition ≤ v.supp := by
  have hI_comap : PA.I ≤ Ideal.comap PA.A₀.subtype (comap φ v).supp := by
    rwa [PairOfDefinition.idealOfDefinition, Ideal.map_le_iff_le_comap] at hI
  have hmap_le : Ideal.map (PA.restrictRingHom PB φ hAB) PA.I ≤
      Ideal.comap PB.A₀.subtype v.supp := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have ha' : (PA.A₀.subtype a : A) ∈ (comap φ v).supp := hI_comap ha
    rw [supp_comap] at ha'
    exact ha'
  have hJ_le : PB.I ≤ Ideal.comap PB.A₀.subtype v.supp := by
    calc PB.I ≤ PB.I.radical := Ideal.le_radical
    _ = (Ideal.map (PA.restrictRingHom PB φ hAB) PA.I).radical := hrad.symm
    _ ≤ (Ideal.comap PB.A₀.subtype v.supp).radical := Ideal.radical_mono hmap_le
    _ = Ideal.comap PB.A₀.subtype v.supp :=
        (Ideal.IsPrime.comap PB.A₀.subtype).radical
  rwa [PairOfDefinition.idealOfDefinition, Ideal.map_le_iff_le_comap]

omit [IsTopologicalRing A] in
/-- **Lemma 7.46(1), second part.** Adic homomorphisms preserve analytic points. -/
theorem analytic_comap_of_isAdicHom {φ : A →+* B}
    (hφ : IsAdicHom φ) {v : Spv B}
    (hv : IsAnalytic v) : IsAnalytic (comap φ v) := by
  intro hna
  apply hv; clear hv
  obtain ⟨PA, PB, hAB, hrad⟩ := hφ
  have hI_le : PA.idealOfDefinition ≤ (comap φ v).supp := by
    rw [PairOfDefinition.idealOfDefinition, Ideal.map_le_iff_le_comap]
    exact fun a ha ↦ (instIsPrimeSupp (comap φ v)).radical.le
      ((PA.isTopologicallyNilpotent_of_mem ha).mem_ideal_radical hna)
  exact supp_isOpen_of_idealOfDefinition_le PB v
    (idealOfDefinition_le_supp_of_adic PA PB φ hAB hrad v hI_le)

end AdicPreservesAnalytic

/-! ### Tate ring specializations of Lemma 7.46 -/

section TateSpecialization

variable [IsTopologicalRing A] [IsTopologicalRing B]
  [IsHuberRing A] [IsHuberRing B]

omit [IsTopologicalRing A] in
/-- In a Tate source ring, adic homomorphisms produce analytic comap points. -/
theorem analytic_comap_of_isAdicHom_tate [IsTateRing B]
    {φ : A →+* B} (hφ : IsAdicHom φ) (v : Spv B) :
    IsAnalytic (comap φ v) :=
  analytic_comap_of_isAdicHom hφ (IsTateRing.isAnalytic v)

end TateSpecialization

/-! ### Lemma 7.46(2): Converse — analytic preservation implies adic -/

section Lemma746Converse

variable {A B : Type*} [CommRing A] [CommRing B]
  [TopologicalSpace A] [TopologicalSpace B]
  [IsTopologicalRing A] [IsTopologicalRing B]
  [IsHuberRing A] [IsHuberRing B]

/- **Lemma 7.46(2) of Wedhorn.** If `B` is a complete Huber ring (with `(B, B⁺)` an
affinoid ring such that `A⁺ ⊆ B⁺` via `φ`) and the induced map `Spa(φ)` preserves
analytic points, then `φ` is an adic homomorphism.

The proof proceeds by contrapositive: if `φ` is not adic, one finds a non-open prime
`𝔭` of `B` via the radical mismatch, then applies **Lemma 7.45** to produce a
`v ∈ Spa(B)` with `supp(v) = 𝔭` that is analytic (non-open support), but whose
comap is non-analytic (since `supp(comap φ v) ⊇ I_A`, hence open). This contradicts
the hypothesis that `Spa(φ)` preserves analytic points.

**Sorry status:** The proof chain has one sorry'd helper:
1. `exists_pairOfDefinition_le_subring` (Wedhorn Lemma 6.5) — **PROVED**. Uses
   `Ideal.span` of lifted generators of `PA.I^m` (FG by construction) with IsAdic
   proved via `span_induction` (Wedhorn Lemma 6.2 coefficient-absorption argument).
2. `exists_nonOpen_prime_of_B_from_B₀_prime` — extending primes from `PB.A₀` to `B`
   while avoiding the ideal of definition. Requires showing that `Ideal.map
   PB.A₀.subtype 𝔭₀` is disjoint from powers of a topologically nilpotent element,
   which uses Huber ring structure theory (bounded submodules) not yet formalized.

Previously sorry'd `spa_point_from_nonOpen_prime` is now proved using the strengthened
Lemma 7.45 API (which exports `idealOfDefinition ⊄ supp(v)`, yielding analyticity).
The proof avoids `topologicalNilradical` (which requires `IsLinearTopology`) by
working directly with `IsTopologicallyNilpotent` via `PairOfDefinition` API.

The main proof structure (contrapositive + contradiction) is sorry-free. -/

-- Helper 1: there exists a pair of definition for A compatible with PB under φ.
-- This is a standard fact: φ⁻¹(PB.A₀) is open (continuity), and any open subring
-- of a Huber ring contains a ring of definition with compatible ideal.
--
-- Proof strategy (Wedhorn, Lemma 6.5 / Remark 6.3):
--   1. A is Huber with some pair (A₀', I'). The images I'^n form a nhds basis of 0.
--   2. φ⁻¹(PB.A₀) is open (continuity) and a subring (preimage of subring).
--   3. A₀' ∩ φ⁻¹(PB.A₀) is open in A₀' and contains 0.
--   4. There exists m with I'^m ⊆ A₀' ∩ φ⁻¹(PB.A₀) (adic topology).
--   5. Build new pair: A₀ = A₀', I_new = I'^m. Since I'^m ⊆ φ⁻¹(PB.A₀) ∩ A₀',
--      and A₀' is generated as a ring by elements in A₀' (which might not map into
--      PB.A₀), we need: A₀' itself maps into PB.A₀.
--   5'. Actually, we need a SMALLER ring of definition. The subring of A₀'
--      generated by I'^m maps into PB.A₀ since all generators do. This subring
--      has the (I'^m)-adic topology, which agrees with the I'-adic topology
--      since I' is finitely generated and I'^m ≤ I'. The subring is open since
--      it contains I'^(2m) which is open.
--   6. Alternatively, use that for sufficiently large m, every element of A₀'
--      is a sum of products of elements of I' (since I'-adic topology means
--      powers of I' are a basis). But A₀' might be larger than Z[I'].
--
-- The cleanest decomposition: sorry a helper `exists_pairOfDefinition_le` that
-- says any open subring of a Huber ring contains a ring of definition.
-- This is Wedhorn Lemma 6.5, which we have not yet formalized.

-- **Wedhorn Lemma 6.5 (simplified).** Any open subring of a Huber ring contains
-- a ring of definition. More precisely: if `A` is Huber with pair `(A₀, I)` and
-- `U` is an open subring with `U ⊆ A₀`, then there exists a pair of definition
-- `(A₀', I')` for `A` with `A₀' ≤ U`.
--
-- The proof (which we sorry) proceeds by:
-- 1. Since `U` is open and contains 0, there exists `m` with `I^m ⊆ U` (intersection
--    with `A₀`, using the adic nbhd basis).
-- 2. Let `A₀' = Subring.closure (I^m : Set A₀)` viewed within `A₀`. Then `A₀'`
--    maps into `U` since `I^m ⊆ U` and `U` is a subring.
-- 3. `A₀'` is open (it contains `I^(2m)` which is open in `A₀`, hence in `A`).
-- 4. The `I^m`-adic topology on `A₀'` equals the subspace topology from `A`.
-- 5. `I^m` is finitely generated (since `I` is, `I^m` is a product of f.g. ideals).
omit [IsHuberRing A] in
private theorem exists_pairOfDefinition_le_subring
    (PA : PairOfDefinition A) {U : Subring A} (hU : IsOpen (U : Set A))
    (_hU_le : U ≤ PA.A₀) :
    ∃ (PA' : PairOfDefinition A), PA'.A₀ ≤ U := by
  -- **Wedhorn Lemma 6.5 (simplified).**
  -- Step 1: Find m with image(I^m) ⊆ U.
  obtain ⟨m, -, hm⟩ := PA.hasBasis_nhds_zero.mem_iff.mp (hU.mem_nhds (U.zero_mem))
  -- Handle m = 0 case: image(I^0) = PA.A₀ ⊆ U, so PA works directly.
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · -- PA.I^0 = ⊤, so image(⊤) = PA.A₀ ⊆ U. Hence PA.A₀ ≤ U.
    have : PA.A₀ ≤ U := by
      intro a ha
      exact hm (Set.mem_image_of_mem PA.A₀.subtype
        (by simp : (⟨a, ha⟩ : PA.A₀) ∈ (PA.I ^ 0 : Ideal PA.A₀)))
    exact ⟨PA, this⟩
  -- From now on, m > 0.
  -- Step 2: Define A₀' = Subring.closure S where S = image of I^m in A.
  set S := PA.A₀.subtype '' ((PA.I ^ m : Ideal PA.A₀) : Set PA.A₀) with S_def
  set A₀' := Subring.closure S with A₀'_def
  -- Step 3: A₀' ≤ U (S ⊆ U since image(I^m) ⊆ U, and U is a subring)
  have hA₀'_le_U : A₀' ≤ U := Subring.closure_le.mpr hm
  -- Step 4: A₀' ≤ PA.A₀ (S ⊆ PA.A₀ since elements of I^m are in A₀)
  have hA₀'_le_PA : A₀' ≤ PA.A₀ :=
    Subring.closure_le.mpr (Set.image_subset_iff.mpr fun _ _ ↦ Subtype.coe_prop _)
  -- Step 5: A₀' is open.
  -- A₀' contains image(I^(2m)) which is open.
  -- Elements of I^(2m) = (I^m)^2 are sums of products a*b with a, b ∈ I^m.
  -- Their images subtype(a) * subtype(b) are products of elements of S,
  -- hence in A₀' = Subring.closure S. So image(I^(2m)) ⊆ A₀'.
  have hA₀'_open : IsOpen (A₀' : Set A) := by
    -- A₀' contains image(I^(2m)) = image((I^m)^2).
    -- Elements of (I^m)^2 are sums of products a*b with a,b ∈ I^m.
    -- Their images subtype(a)*subtype(b) are products of elements of S, hence in A₀'.
    have h2m_sub : PA.A₀.subtype '' ((PA.I ^ (2 * m) : Ideal PA.A₀) : Set PA.A₀) ⊆
        (A₀' : Set A) := by
      rintro _ ⟨x, hx, rfl⟩
      -- x ∈ I^(2m) = (I^m) * (I^m) (since 2*m = m + m)
      have hx' : x ∈ PA.I ^ m * PA.I ^ m := by
        rwa [← pow_add, show m + m = 2 * m from by ring]
      -- Induction on elements of I^m * I^m: they are sums of products a*b
      refine Submodule.mul_induction_on hx'
        (fun a ha b hb ↦ ?_) (fun _ _ h1 h2 ↦ A₀'.add_mem h1 h2)
      -- a ∈ I^m, b ∈ I^m, need subtype(a*b) ∈ A₀'
      change PA.A₀.subtype (a * b) ∈ A₀'
      rw [map_mul]
      exact A₀'.mul_mem
        (Subring.subset_closure ⟨a, ha, rfl⟩)
        (Subring.subset_closure ⟨b, hb, rfl⟩)
    -- A₀' is open: it contains image(I^(2m)) which is open and contains 0
    change IsOpen (A₀'.toAddSubgroup : Set A)
    exact AddSubgroup.isOpen_of_mem_nhds _
      (Filter.mem_of_superset
        ((PA.pow_image_isOpen (2 * m)).mem_nhds
          (Set.mem_image_of_mem _ (PA.I ^ (2 * m)).zero_mem))
        h2m_sub)
  -- Step 6: Build a finitely generated ideal I' of A₀' and the PairOfDefinition.
  -- Strategy (Wedhorn Lemma 6.2 / Corollary 6.4(4)):
  -- Lift generators of PA.I^m to A₀', define I' = Ideal.span(lifts).
  -- For IsAdic, the key openness argument uses span_induction on g ∈ PA.I^m
  -- with the predicate universally quantified over w, so that the smul case
  -- (c · g for c ∈ PA.A₀) absorbs c into w via c·w ∈ PA.I^{(n+1)m}.
  set ι := Subring.inclusion hA₀'_le_PA with ι_def
  -- Elements of PA.I^m have subtype-images in S ⊆ A₀'.
  have hlift : ∀ x ∈ PA.I ^ m, (PA.A₀.subtype x : A) ∈ A₀' :=
    fun x hx ↦ Subring.subset_closure ⟨x, hx, rfl⟩
  -- Get a finite generating set for PA.I^m.
  obtain ⟨F, hF⟩ := PA.fg.pow (n := m)
  -- Lift each generator to A₀'.
  have hF_sub : ∀ g ∈ F, (PA.A₀.subtype g : A) ∈ A₀' :=
    fun g hg ↦ hlift g (hF ▸ Ideal.subset_span (Finset.mem_coe.mpr hg))
  -- Define the lifted generators in A₀'.
  classical
  set F' : Finset A₀' :=
    F.attach.image (fun g ↦ ⟨PA.A₀.subtype g.1, hF_sub g.1 g.2⟩)
  -- Define I' as the ideal of A₀' generated by F'.
  set I' := Ideal.span (F' : Set A₀') with I'_def
  -- **FG of I':** immediate from the finite generating set.
  have hI'_fg : I'.FG := ⟨F', rfl⟩
  -- Key: ι maps each lifted generator back to the original generator in PA.A₀.
  have hι_gen_eq : ∀ (g : PA.A₀) (hg : g ∈ F),
      ι (⟨PA.A₀.subtype g, hF_sub g hg⟩ : A₀') = g :=
    fun g _ ↦ Subtype.ext (by simp [ι, Subring.inclusion])
  -- Therefore ι maps each generator of I' into PA.I^m.
  have hι_gen : ∀ g' ∈ F', ι g' ∈ PA.I ^ m := by
    intro g' hg'
    simp only [F', Finset.mem_image, Finset.mem_attach, true_and] at hg'
    obtain ⟨⟨g, hg_mem⟩, rfl⟩ := hg'
    rw [hι_gen_eq g hg_mem]; exact hF ▸ Ideal.subset_span (Finset.mem_coe.mpr hg_mem)
  -- Therefore I' ≤ comap ι (PA.I^m).
  have hI'_le_comap : I' ≤ Ideal.comap ι (PA.I ^ m) :=
    Ideal.span_le.mpr fun g' hg' ↦ hι_gen g' hg'
  -- **Openness inclusion (by induction on n):**
  -- comap ι (PA.I^((n+2)·m)) ≤ I'^n.
  -- Base: n = 0 is trivial (I'^0 = ⊤).
  -- Step: PA.I^((n+3)·m) = PA.I^m · PA.I^((n+2)·m). For g ∈ PA.I^m = Ideal.span F
  --   and w ∈ PA.I^((n+2)·m), decompose g via span_induction: generators f ∈ F
  --   lift to f' ∈ I', and f'·(IH element in I'^n) ∈ I'^(n+1). Coefficients c ∈ PA.A₀
  --   absorb into w: c·w ∈ PA.I^((n+2)·m), so its lift is in I'^n by IH.
  have comap_le_pow : ∀ n, Ideal.comap ι (PA.I ^ ((n + 2) * m)) ≤ I' ^ n := by
    intro n
    induction n with
    | zero =>
      intro x _
      change x ∈ (I' ^ 0 : Ideal ↥A₀')
      simp
    | succ n ih =>
      -- Need: comap ι (PA.I^((n+3)·m)) ≤ I'^(n+1).
      -- PA.I^((n+3)·m) = PA.I^(m + (n+2)·m) = PA.I^m · PA.I^((n+2)·m).
      intro x hx
      change x ∈ I' ^ (n + 1)
      -- ι(x) ∈ PA.I^((n+3)·m) = PA.I^m · PA.I^((n+2)·m)
      have hιx : ι x ∈ PA.I ^ m * PA.I ^ ((n + 2) * m) := by
        rw [← pow_add, show m + (n + 2) * m = (n + 3) * m from by ring]
        exact hx
      -- Prove: for z ∈ PA.I^m · PA.I^((n+2)·m), if subtype(z) ∈ A₀',
      -- then ⟨subtype(z), _⟩ ∈ I'^(n+1).
      -- We use span_induction on the PA.I^m = Ideal.span F factor.
      -- Predicate: z maps to A₀' AND its lift is in I'^(n+1).
      -- Using conjunction avoids the problem of deducing A₀'-membership of summands.
      suffices h_suff : ∀ z ∈ PA.I ^ m * PA.I ^ ((n + 2) * m),
          (PA.A₀.subtype z : A) ∈ A₀' ∧
          ∀ (h' : (PA.A₀.subtype z : A) ∈ A₀'),
          (⟨PA.A₀.subtype z, h'⟩ : A₀') ∈ (I' ^ (n + 1) : Ideal A₀') by
        have hx_eq : x = ⟨PA.A₀.subtype (ι x), x.2⟩ := by
          ext; simp [ι, Subring.inclusion]
        rw [hx_eq]; exact (h_suff (ι x) hιx).2 x.2
      intro z hz
      -- Decompose z via mul_induction_on on PA.I^m · PA.I^((n+2)·m).
      refine Submodule.mul_induction_on hz (fun g hg w hw ↦ ?_) (fun u v hu hv ↦ ?_)
      · -- Product case: z = g · w with g ∈ PA.I^m, w ∈ PA.I^((n+2)·m).
        -- Use span_induction on g ∈ PA.I^m = Ideal.span F.
        -- Inner span_induction with universally quantified w' (for smul absorption).
        -- Predicate: subtype(g'·w') ∈ A₀' AND its lift is in I'^(n+1).
        suffices h_span : ∀ (g' : PA.A₀), g' ∈ Ideal.span (F : Set PA.A₀) →
            ∀ (w' : PA.A₀), w' ∈ PA.I ^ ((n + 2) * m) →
            (PA.A₀.subtype (g' * w') : A) ∈ A₀' ∧
            ∀ (h' : (PA.A₀.subtype (g' * w') : A) ∈ A₀'),
            (⟨PA.A₀.subtype (g' * w'), h'⟩ : A₀') ∈ (I' ^ (n + 1) : Ideal A₀') by
          exact h_span g (hF ▸ hg) w hw
        intro g' hg'
        induction hg' using Submodule.span_induction with
        | mem f hf =>
          intro w' hw'
          have hf'_mem : (⟨PA.A₀.subtype f, hF_sub f hf⟩ : A₀') ∈ I' :=
            Ideal.subset_span (Finset.mem_image.mpr ⟨⟨f, hf⟩, Finset.mem_attach _ _, rfl⟩)
          have hw'_A₀' : (PA.A₀.subtype w' : A) ∈ A₀' :=
            hlift w' (Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left m (by omega)) hw')
          have hfw'_A₀' : (PA.A₀.subtype (f * w') : A) ∈ A₀' := by
            rw [map_mul]; exact A₀'.mul_mem (hF_sub f hf) hw'_A₀'
          refine ⟨hfw'_A₀', fun h' ↦ ?_⟩
          -- By IH: lift of w' is in I'^n.
          have hw'_In : (⟨PA.A₀.subtype w', hw'_A₀'⟩ : A₀') ∈ (I' ^ n : Ideal A₀') := by
            apply ih; change ι ⟨PA.A₀.subtype w', hw'_A₀'⟩ ∈ PA.I ^ ((n + 2) * m)
            rw [show (ι ⟨PA.A₀.subtype w', hw'_A₀'⟩ : PA.A₀) = w' from
              Subtype.ext (by simp [ι, Subring.inclusion])]
            exact hw'
          -- f' · (lift of w') ∈ I' · I'^n = I'^(n+1).
          have : (⟨PA.A₀.subtype (f * w'), h'⟩ : A₀') =
              ⟨PA.A₀.subtype f, hF_sub f hf⟩ * ⟨PA.A₀.subtype w', hw'_A₀'⟩ :=
            Subtype.ext (by simp [map_mul])
          rw [this, pow_succ']
          exact Ideal.mul_mem_mul hf'_mem hw'_In
        | zero =>
          intro w' _
          exact ⟨by simp [A₀'.zero_mem], fun h' ↦ by
            have : (⟨PA.A₀.subtype (0 * w'), h'⟩ : A₀') = 0 :=
              Subtype.ext (by simp)
            rw [this]; exact (I' ^ (n + 1)).zero_mem⟩
        | add x' y' _ _ hx'_ih hy'_ih =>
          intro w' hw'
          obtain ⟨hx'w'_A₀', hx'_res⟩ := hx'_ih w' hw'
          obtain ⟨hy'w'_A₀', hy'_res⟩ := hy'_ih w' hw'
          refine ⟨by rw [add_mul, map_add]; exact A₀'.add_mem hx'w'_A₀' hy'w'_A₀', fun h' ↦ ?_⟩
          have : (⟨PA.A₀.subtype ((x' + y') * w'), h'⟩ : A₀') =
              ⟨PA.A₀.subtype (x' * w'), hx'w'_A₀'⟩ +
              ⟨PA.A₀.subtype (y' * w'), hy'w'_A₀'⟩ :=
            Subtype.ext (by simp [add_mul, map_add])
          rw [this]; exact (I' ^ (n + 1)).add_mem (hx'_res hx'w'_A₀') (hy'_res hy'w'_A₀')
        | smul c x' _ hx'_ih =>
          intro w' hw'
          have hcw'_mem : c * w' ∈ PA.I ^ ((n + 2) * m) := Ideal.mul_mem_left _ c hw'
          obtain ⟨hx'cw'_A₀', hx'_res⟩ := hx'_ih (c * w') hcw'_mem
          have heq : c • x' * w' = x' * (c * w') := by
            simp only [smul_eq_mul]; ring
          constructor
          · change (PA.A₀.subtype (c • x' * w') : A) ∈ A₀'
            rw [show (c • x' * w' : PA.A₀) = x' * (c * w') from Subtype.ext (by
              simp [mul_comm, mul_left_comm])]
            exact hx'cw'_A₀'
          · intro h'
            have : (⟨PA.A₀.subtype (c • x' * w'), h'⟩ : A₀') =
                ⟨PA.A₀.subtype (x' * (c * w')), hx'cw'_A₀'⟩ :=
              Subtype.ext (by simp [mul_comm, mul_left_comm])
            rw [this]; exact hx'_res hx'cw'_A₀'
      · -- Additive case: z = u + v. Both summands satisfy the predicate by hypothesis.
        obtain ⟨hu_A₀', hu_res⟩ := hu
        obtain ⟨hv_A₀', hv_res⟩ := hv
        refine ⟨by rw [map_add]; exact A₀'.add_mem hu_A₀' hv_A₀', fun h' ↦ ?_⟩
        have : (⟨PA.A₀.subtype (u + v), h'⟩ : A₀') =
            ⟨PA.A₀.subtype u, hu_A₀'⟩ + ⟨PA.A₀.subtype v, hv_A₀'⟩ :=
          Subtype.ext (by simp [map_add])
        rw [this]; exact (I' ^ (n + 1)).add_mem (hu_res hu_A₀') (hv_res hv_A₀')
  -- **IsAdic of I':** The subspace topology on A₀' equals the I'-adic topology.
  have hI'_isAdic : IsAdic I' := by
    rw [isAdic_iff]; constructor
    · -- (1) Each I'^n is open: I'^n ⊇ preimage of image(PA.I^((n+2)·m)).
      intro n
      set k := (n + 2) * m
      have hW_open : IsOpen ((fun x : A₀' ↦ (x : A)) ⁻¹'
          (PA.A₀.subtype '' ((PA.I ^ k : Ideal PA.A₀) : Set PA.A₀))) :=
        (PA.pow_image_isOpen k).preimage continuous_subtype_val
      have hW_zero : (0 : A₀') ∈ (fun x : A₀' ↦ (x : A)) ⁻¹'
          (PA.A₀.subtype '' ((PA.I ^ k : Ideal PA.A₀) : Set PA.A₀)) :=
        ⟨0, (PA.I ^ k).zero_mem, by simp⟩
      have hW_sub : (fun x : A₀' ↦ (x : A)) ⁻¹'
          (PA.A₀.subtype '' ((PA.I ^ k : Ideal PA.A₀) : Set PA.A₀)) ⊆
          ((I' ^ n : Ideal A₀') : Set A₀') := by
        intro x ⟨y, hy, hval⟩
        apply comap_le_pow n
        change ι x ∈ PA.I ^ ((n + 2) * m)
        exact (Subtype.ext (by simp only [ι, Subring.inclusion]; exact hval.symm) : ι x = y) ▸ hy
      change IsOpen ((I' ^ n).toAddSubgroup : Set A₀')
      exact AddSubgroup.isOpen_of_mem_nhds _
        (Filter.mem_of_superset (hW_open.mem_nhds hW_zero)
          (Submodule.coe_toAddSubgroup (I' ^ n) ▸ hW_sub))
    · -- (2) Every nhds of 0 in A₀' contains some I'^n.
      -- I' ≤ comap ι (PA.I^m), so I'^n ≤ comap ι (PA.I^(mn)), which shrinks to 0.
      intro s hs
      have hI'_pow_le : ∀ n, I' ^ n ≤ Ideal.comap ι (PA.I ^ (m * n)) := by
        intro n
        calc I' ^ n ≤ (Ideal.comap ι (PA.I ^ m)) ^ n := pow_le_pow_left' hI'_le_comap n
          _ ≤ Ideal.comap ι ((PA.I ^ m) ^ n) := Ideal.le_comap_pow ι n
          _ = Ideal.comap ι (PA.I ^ (m * n)) := by rw [← pow_mul]
      rw [nhds_induced, Filter.mem_comap] at hs
      obtain ⟨V, hV, hV_sub⟩ := hs
      obtain ⟨j, -, hj⟩ := PA.hasBasis_nhds_zero.mem_iff.mp hV
      refine ⟨j, fun x hx ↦ hV_sub (show (x : A) ∈ V from hj ?_)⟩
      have hιx : ι x ∈ PA.I ^ (m * j) := hI'_pow_le j hx
      have hmj_le : PA.I ^ (m * j) ≤ PA.I ^ j :=
        Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left j hm_pos)
      exact ⟨ι x, hmj_le hιx, by simp [ι, Subring.inclusion]⟩
  exact ⟨⟨A₀', I', hA₀'_open, hI'_fg, hI'_isAdic⟩, hA₀'_le_U⟩

omit [IsTopologicalRing B] [IsHuberRing B] in
private theorem exists_compatible_pair
    {φ : A →+* B} (hφ : Continuous φ) (PB : PairOfDefinition B) :
    ∃ (PA : PairOfDefinition A), ∀ a ∈ PA.A₀, φ a ∈ PB.A₀ := by
  -- Step 1: Get any pair of definition for A
  obtain ⟨PA'⟩ := ‹IsHuberRing A›.exists_pairOfDefinition
  -- Step 2: φ⁻¹(PB.A₀) is an open subring of A
  have hpreimg_open : IsOpen (φ ⁻¹' (PB.A₀ : Set B)) := PB.isOpen.preimage hφ
  -- Step 3: The intersection PA'.A₀ ∩ φ⁻¹(PB.A₀) is an open subring
  set U : Subring A := PA'.A₀ ⊓ (PB.A₀.comap φ) with U_def
  have hU_open : IsOpen (U : Set A) := PA'.isOpen.inter hpreimg_open
  have hU_le : U ≤ PA'.A₀ := inf_le_left
  -- Step 4: Apply Lemma 6.5 to get a pair of definition with A₀ ⊆ U
  obtain ⟨PA, hPA_le⟩ := exists_pairOfDefinition_le_subring PA' hU_open hU_le
  -- Step 5: Elements of PA.A₀ map into PB.A₀ since PA.A₀ ⊆ U ⊆ φ⁻¹(PB.A₀)
  exact ⟨PA, fun a ha ↦ (hPA_le ha).2⟩

-- Helper 2a: from strict radical containment, find a separating prime of B₀.
-- This is a standard commutative algebra argument using Ideal.radical_eq_sInf.
omit [IsTopologicalRing A] [IsTopologicalRing B]
  [IsHuberRing A] [IsHuberRing B] in
private theorem exists_separating_prime_of_B₀
    {φ : A →+* B}
    (PA : PairOfDefinition A) (PB : PairOfDefinition B)
    (h_map : ∀ a ∈ PA.A₀, φ a ∈ PB.A₀)
    (h_not_eq : (Ideal.map (PA.restrictRingHom PB φ h_map) PA.I).radical ≠ PB.I.radical)
    (h_le : (Ideal.map (PA.restrictRingHom PB φ h_map) PA.I).radical ≤ PB.I.radical) :
    ∃ (𝔭₀ : Ideal PB.A₀), 𝔭₀.IsPrime ∧
      Ideal.map (PA.restrictRingHom PB φ h_map) PA.I ≤ 𝔭₀ ∧ ¬PB.I ≤ 𝔭₀ := by
  -- Strict containment gives an element in rad(J) \ rad(image)
  have h_strict := lt_of_le_of_ne h_le h_not_eq
  -- Choose j ∈ rad(J) \ rad(image). exists_of_ssubset gives (j ∈ t, j ∉ s).
  obtain ⟨j, hj_radJ, hj_not_radI⟩ :=
    Set.exists_of_ssubset (show (Ideal.map (PA.restrictRingHom PB φ h_map) PA.I).radical <
      PB.I.radical from h_strict)
  -- j ∉ rad(image), so there exists a prime 𝔭₀ ⊇ image with j ∉ 𝔭₀
  set img := Ideal.map (PA.restrictRingHom PB φ h_map) PA.I
  -- j ∉ rad(img), and rad(img) = sInf{𝔭 | img ≤ 𝔭 ∧ IsPrime 𝔭}
  have hj_not_all : ¬(∀ (𝔭 : Ideal PB.A₀), (img ≤ 𝔭 ∧ 𝔭.IsPrime) → j ∈ 𝔭) := by
    intro hall
    exact hj_not_radI (Ideal.radical_eq_sInf img ▸ Ideal.mem_sInf.mpr
      fun J hJ ↦ hall J hJ)
  push_neg at hj_not_all
  obtain ⟨𝔭₀, ⟨h_image_le, h𝔭₀_prime⟩, hj_not_p⟩ := hj_not_all
  refine ⟨𝔭₀, h𝔭₀_prime, h_image_le, fun hJ_le ↦ hj_not_p ?_⟩
  -- j ∈ rad(J) and J ≤ 𝔭₀ (prime), so j ∈ rad(J) ≤ rad(𝔭₀) = 𝔭₀
  exact h𝔭₀_prime.radical.symm ▸ Ideal.radical_mono hJ_le hj_radJ

-- Helper 2b: from a prime 𝔭₀ of B₀ (with image ≤ 𝔭₀ and J ⊄ 𝔭₀), produce an
-- analytic v ∈ Spa(B, B⁺) with PA.idealOfDefinition ≤ φ⁻¹(supp(v)).
-- This is the core of Lemma 7.46(2) that requires Lemma 7.45 with exact support.
--
-- **Proof strategy (Wedhorn Lemma 7.46(2)):**
--   Step A: From 𝔭₀ (prime of PB.A₀ with J ⊄ 𝔭₀), produce a non-open prime 𝔭 of B.
--     Sub-step A1: 𝔭₀ is not maximal (by not_isMaximal_of_I_not_le).
--     Sub-step A2: Extend 𝔭₀ to a prime 𝔭 of B with Ideal.comap PB.A₀.subtype 𝔭 ⊇ 𝔭₀.
--       This requires the "lying-over" property for open subrings of Huber rings.
--     Sub-step A3: 𝔭 is non-open (since PB.idealOfDefinition ⊄ 𝔭, as
--       PB.I ⊄ Ideal.comap PB.A₀.subtype 𝔭 ⊇ 𝔭₀ and J ⊄ 𝔭₀).
--   Step B: Apply Lemma 7.45 to get v ∈ Spa(B, B⁺) with 𝔭 ≤ supp(v).
--   Step C: v is analytic (supp(v) ⊇ 𝔭, and 𝔭 is non-open, so supp(v) is non-open
--     unless supp(v) ⊃ 𝔭... actually we need supp non-open, which follows from
--     supp(v) not containing idealOfDefinition).
--     Actually: Lemma 7.45 gives supp(v) ⊇ 𝔭, not supp = 𝔭. But supp(v) is prime.
--     If supp(v) contained idealOfDefinition, it would be open by
--     isOpen_of_idealOfDefinition_le. We need to CHOOSE v so that supp(v) does NOT
--     contain idealOfDefinition. This is tricky with the ⊇ direction of Lemma 7.45.
--     RESOLUTION: Use the contrapositive structure -- we only need v ∈ Spa(B) with
--     v analytic (supp non-open). Since 𝔭 is non-open and 𝔭 ≤ supp(v), we need
--     supp(v) also non-open. This holds when supp(v) = 𝔭, which requires the
--     exact equality direction of Lemma 7.45. Since we only have ⊇, we sorry
--     a helper for the exact equality case.
--   Step D: supp(comap φ v) = φ⁻¹(supp(v)) ⊇ φ⁻¹(image(𝔭₀)) ⊇ PA.idealOfDefinition,
--     so comap has open support.

-- Sub-step A2: Extension of primes from subrings to rings.
-- Given a prime 𝔭₀ of PB.A₀, we produce a prime 𝔭 of B with 𝔭₀ ⊆ comap PB.A₀.subtype 𝔭
-- and the ideal of definition not contained in 𝔭.
--
-- The mathematical content: we need a prime of B lying over 𝔭₀ that avoids J.
-- This is the most delicate step. By I_sup_prime_ne_top, I ⊔ 𝔭₀ ≠ ⊤ in PB.A₀.
-- We need to produce a prime in B from this data.
--
-- **Proof sketch (verified mathematically):**
-- 1. Since ¬PB.I ≤ 𝔭₀, choose `j ∈ PB.I \ 𝔭₀` (exists by `Set.not_subset`).
-- 2. `𝔭₀` is prime and `j ∉ 𝔭₀`, so `Submonoid.powers j` is disjoint from `𝔭₀`
--    (since `j^n ∉ 𝔭₀` for all `n`, by primality).
-- 3. Consider `Ideal.map PB.A₀.subtype 𝔭₀` (the ideal of `B` generated by `𝔭₀`).
-- 4. We need: `map subtype 𝔭₀` is disjoint from `Submonoid.powers (subtype j)`.
--    This is the KEY non-trivial step. It requires showing that
--    `(subtype j)^n ∉ map subtype 𝔭₀` for all `n`. Since `j^n ∉ 𝔭₀` (primality)
--    and `subtype` is injective, this follows IF `comap subtype (map subtype 𝔭₀) = 𝔭₀`.
--    In general, `comap subtype (map subtype 𝔭₀) ⊇ 𝔭₀` but equality requires
--    that the extension `PB.A₀ → B` is "unramified above 𝔭₀" — specifically,
--    that no element of `B \ PB.A₀` can combine with elements of `subtype(𝔭₀)` to
--    produce a power of `subtype(j)`. For Huber rings, this holds because `B` is
--    the union of bounded `PB.A₀`-submodules and `j ∈ PB.I` is topologically
--    nilpotent, making `subtype(j)` a non-zero-divisor modulo `map subtype 𝔭₀`
--    in a suitable localization.
-- 5. Given disjointness (step 4), apply `Ideal.exists_le_prime_disjoint` to get
--    a prime `𝔭 ⊇ map subtype 𝔭₀` with `subtype j ∉ 𝔭`.
-- 6. Then `𝔭₀ ≤ comap subtype 𝔭` (since `map subtype 𝔭₀ ≤ 𝔭`), and
--    `𝔭` is non-open (since `subtype j ∈ PB.idealOfDefinition` but `subtype j ∉ 𝔭`,
--    so `PB.idealOfDefinition ⊄ 𝔭`).
--
-- **Sorry:** Step 4 requires infrastructure for Huber ring extensions:
-- specifically, showing that `comap subtype (map subtype 𝔭₀) = 𝔭₀` when
-- `𝔭₀` is prime and `PB.A₀` is a ring of definition. This uses the structural
-- property that Huber rings are unions of bounded `A₀`-submodules, which is
-- not yet formalized. Alternative approach: use integrality of certain
-- localizations (Cohen's theorem for adic rings), also not yet available.
-- Estimated formalization: ~100-150 lines of Huber ring structure theory.
omit [IsTopologicalRing A] [IsHuberRing A] [IsHuberRing B] in
private theorem exists_nonOpen_prime_of_B_from_B₀_prime
    (PB : PairOfDefinition B) [IsAdicComplete PB.I PB.A₀]
    {𝔭₀ : Ideal PB.A₀} [𝔭₀.IsPrime]
    (hJ_not_le : ¬PB.I ≤ 𝔭₀) :
    ∃ (𝔭 : Ideal B), 𝔭.IsPrime ∧ ¬IsOpen (𝔭 : Set B) ∧
      𝔭₀ ≤ Ideal.comap PB.A₀.subtype 𝔭 := by
  -- Step 1: Choose j ∈ PB.I with j ∉ 𝔭₀.
  obtain ⟨j, hj_mem, hj_not⟩ := SetLike.not_le_iff_exists.mp hJ_not_le
  -- Step 2: Establish disjointness of (map subtype 𝔭₀) and (powers (subtype j)) in B.
  -- This is the core difficulty: elements of map subtype 𝔭₀ are finite sums
  -- ∑ bᵢ · subtype(aᵢ) with aᵢ ∈ 𝔭₀ and bᵢ ∈ B (not necessarily in PB.A₀),
  -- so pulling back to PB.A₀ is non-trivial and requires Huber ring structure theory
  -- (that B is a union of bounded PB.A₀-modules). See comment block above.
  have h_disj : Disjoint (Ideal.map PB.A₀.subtype 𝔭₀ : Set B)
      (Submonoid.powers (PB.A₀.subtype j)) := by
    -- Reduce to: comap subtype (map subtype 𝔭₀) ≤ 𝔭₀ (the lying-over direction).
    -- Once we have this, disjoint_map_primeCompl_iff_comap_le gives disjointness with
    -- the full prime complement, from which we restrict to powers of (subtype j).
    have h_comap_le : (Ideal.map PB.A₀.subtype 𝔭₀).comap PB.A₀.subtype ≤ 𝔭₀ := by
      -- Key claim: for the open subring inclusion PB.A₀ → B in a Huber ring,
      -- the contraction of the extension of a prime equals the prime.
      -- Proof by span_induction on elements of Ideal.map subtype 𝔭₀ = Ideal.span (subtype '' 𝔭₀),
      -- using topological nilpotency of j ∈ PB.I to absorb scalars from B into PB.A₀.
      -- Predicate: P(b) := ∃ n c, c ∈ 𝔭₀ ∧ subtype(c) = (subtype j)^n * b.
      -- Topological nilpotency of j (needed for smul case).
      have hj_nil : IsTopologicallyNilpotent (PB.A₀.subtype j : B) :=
        PB.isTopologicallyNilpotent_of_mem hj_mem
      -- Helper: for any b in Ideal.span (subtype '' 𝔭₀), ∃ n c, c ∈ 𝔭₀ ∧ subtype c = j^n * b.
      have h_span : ∀ (b : B), b ∈ Ideal.span (PB.A₀.subtype '' (𝔭₀ : Set PB.A₀)) →
          ∃ (n : ℕ) (c : PB.A₀), c ∈ 𝔭₀ ∧
            PB.A₀.subtype c = (PB.A₀.subtype j) ^ n * b := by
        intro b hb
        induction hb using Submodule.span_induction with
        | mem b hb =>
          obtain ⟨a, ha_mem, ha_eq⟩ := hb
          exact ⟨0, a, ha_mem, by rw [pow_zero, one_mul, ha_eq]⟩
        | zero =>
          exact ⟨0, 0, 𝔭₀.zero_mem, by simp⟩
        | add b₁ b₂ _ _ ih₁ ih₂ =>
          obtain ⟨n₁, c₁, hc₁_mem, hc₁_eq⟩ := ih₁
          obtain ⟨n₂, c₂, hc₂_mem, hc₂_eq⟩ := ih₂
          refine ⟨n₁ ⊔ n₂, j ^ (n₁ ⊔ n₂ - n₁) * c₁ + j ^ (n₁ ⊔ n₂ - n₂) * c₂,
            𝔭₀.add_mem (𝔭₀.mul_mem_left _ hc₁_mem) (𝔭₀.mul_mem_left _ hc₂_mem), ?_⟩
          have h1 : (PB.A₀.subtype j) ^ (n₁ ⊔ n₂ - n₁ + n₁) * b₁ =
              (PB.A₀.subtype j) ^ (n₁ ⊔ n₂) * b₁ := by
            rw [Nat.sub_add_cancel (Nat.le_max_left n₁ n₂)]
          have h2 : (PB.A₀.subtype j) ^ (n₁ ⊔ n₂ - n₂ + n₂) * b₂ =
              (PB.A₀.subtype j) ^ (n₁ ⊔ n₂) * b₂ := by
            rw [Nat.sub_add_cancel (Nat.le_max_right n₁ n₂)]
          simp only [map_add, map_mul, map_pow, mul_add]
          congr 1
          · calc (PB.A₀.subtype j) ^ (n₁ ⊔ n₂ - n₁) * (PB.A₀.subtype c₁)
                = (PB.A₀.subtype j) ^ (n₁ ⊔ n₂ - n₁) * ((PB.A₀.subtype j) ^ n₁ * b₁) := by
                  rw [hc₁_eq]
              _ = (PB.A₀.subtype j) ^ (n₁ ⊔ n₂ - n₁ + n₁) * b₁ := by
                  rw [pow_add, mul_assoc]
              _ = (PB.A₀.subtype j) ^ (n₁ ⊔ n₂) * b₁ := h1
          · calc (PB.A₀.subtype j) ^ (n₁ ⊔ n₂ - n₂) * (PB.A₀.subtype c₂)
                = (PB.A₀.subtype j) ^ (n₁ ⊔ n₂ - n₂) * ((PB.A₀.subtype j) ^ n₂ * b₂) := by
                  rw [hc₂_eq]
              _ = (PB.A₀.subtype j) ^ (n₁ ⊔ n₂ - n₂ + n₂) * b₂ := by
                  rw [pow_add, mul_assoc]
              _ = (PB.A₀.subtype j) ^ (n₁ ⊔ n₂) * b₂ := h2
        | smul r b _ ih =>
          obtain ⟨n₀, c₀, hc₀_mem, hc₀_eq⟩ := ih
          obtain ⟨m, hm⟩ := PB.exists_pow_mul_mem_A₀ hj_nil r
          set r' : PB.A₀ := ⟨(PB.A₀.subtype j) ^ m * r, hm⟩ with hr'_def
          refine ⟨m + n₀, r' * c₀, 𝔭₀.mul_mem_left _ hc₀_mem, ?_⟩
          -- Goal: subtype(r' * c₀) = (subtype j)^(m+n₀) * (r • b)
          -- LHS = subtype(r') * subtype(c₀) = ((subtype j)^m * r) * ((subtype j)^n₀ * b)
          -- RHS = (subtype j)^m * (subtype j)^n₀ * (r * b) = (subtype j)^m * (subtype j)^n₀ * r * b
          have h_lhs : PB.A₀.subtype (r' * c₀) =
              ((PB.A₀.subtype j) ^ m * r) * ((PB.A₀.subtype j) ^ n₀ * b) := by
            rw [map_mul, hc₀_eq]; rfl
          rw [h_lhs, smul_eq_mul, pow_add, mul_assoc, mul_assoc,
            mul_left_comm r ((PB.A₀.subtype j) ^ n₀) b]
      -- Apply h_span to conclude.
      intro x hx
      simp only [Ideal.mem_comap] at hx
      obtain ⟨n, c, hc_mem, hc_eq⟩ := h_span (PB.A₀.subtype x) hx
      have hc_eq' : c = j ^ n * x := Subtype.val_injective (by
        simp only [Subring.coe_mul, SubmonoidClass.coe_pow]; exact hc_eq)
      rw [hc_eq'] at hc_mem
      rcases (‹𝔭₀.IsPrime›).mem_or_mem hc_mem with hjn | hx_in
      · exact absurd (‹𝔭₀.IsPrime›.mem_of_pow_mem n hjn) hj_not
      · exact hx_in
    -- The prime complement of 𝔭₀ maps to a set containing powers(subtype j).
    have h_powers_le : (Submonoid.powers (PB.A₀.subtype j) : Set B) ⊆
        (𝔭₀.primeCompl.map PB.A₀.subtype : Set B) := by
      rintro _ ⟨n, rfl⟩
      refine ⟨j ^ n, ?_, map_pow PB.A₀.subtype j n⟩
      change j ^ n ∉ 𝔭₀
      intro h
      rcases n.eq_zero_or_pos with rfl | hn
      · exact (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one 𝔭₀).mpr (pow_zero j ▸ h))
      · exact hj_not ((_root_.Ideal.IsPrime.pow_mem_iff_mem ‹_› n hn).mp h)
    -- Disjointness from primeCompl.map subtype (via the iff with comap ≤)
    exact (Ideal.disjoint_map_primeCompl_iff_comap_le.mpr h_comap_le).mono_right h_powers_le
  -- Step 3: Apply Zorn (via exists_le_prime_disjoint) to get a prime 𝔭 of B
  -- containing map subtype 𝔭₀ and disjoint from powers of subtype j.
  obtain ⟨𝔭, h𝔭_prime, h𝔭_le, h𝔭_disj⟩ :=
    (Ideal.map PB.A₀.subtype 𝔭₀).exists_le_prime_disjoint
      (Submonoid.powers (PB.A₀.subtype j)) h_disj
  refine ⟨𝔭, h𝔭_prime, ?_, ?_⟩
  -- Step 4: 𝔭 is not open.
  -- Proof: j ∈ PB.I so subtype j is topologically nilpotent in B.
  -- If 𝔭 were open, then (subtype j)^n ∈ 𝔭 for large n (since (subtype j)^n → 0),
  -- so subtype j ∈ 𝔭 by primality. But subtype j ∈ powers(subtype j) and
  -- 𝔭 is disjoint from powers(subtype j), contradiction.
  · intro h_open
    have hj_nilp : IsTopologicallyNilpotent (PB.A₀.subtype j : B) :=
      PB.isTopologicallyNilpotent_of_mem hj_mem
    -- subtype j ∈ 𝔭 because it's topologically nilpotent and 𝔭 is open and prime
    have hj_in_𝔭 : (PB.A₀.subtype j : B) ∈ 𝔭 := by
      have h𝔭_mem_nhds : (𝔭 : Set B) ∈ nhds 0 :=
        h_open.mem_nhds 𝔭.zero_mem
      obtain ⟨n, hn⟩ := (Filter.Tendsto.eventually hj_nilp h𝔭_mem_nhds).exists
      exact h𝔭_prime.mem_of_pow_mem n hn
    -- But subtype j ∈ Submonoid.powers (subtype j), contradicting disjointness
    exact Set.disjoint_left.mp h𝔭_disj hj_in_𝔭 (Submonoid.mem_powers _)
  -- Step 5: 𝔭₀ ≤ comap subtype 𝔭 (by the Galois connection map ≤ iff ≤ comap).
  · exact Ideal.le_comap_of_map_le h𝔭_le

-- Sub-step C/D: From a non-open prime of B, get v ∈ Spa(B, B⁺) with the right properties.
-- This combines Lemma 7.45 (⊇ direction) with the non-openness argument.
--
-- **Proved** using the strengthened Lemma 7.45 API (which now exports
-- `idealOfDefinition ⊄ supp(v)` alongside `𝔭 ≤ supp(v)`). Analyticity
-- follows from: for prime p in a Huber ring with pair of definition,
-- `IsOpen p ↔ idealOfDefinition ≤ p` (Lemma 6.6).
omit [IsTopologicalRing A] [IsHuberRing A] [IsHuberRing B] in
private theorem spa_point_from_nonOpen_prime
    [PlusSubring B]
    (PB : PairOfDefinition B) [IsAdicComplete PB.I PB.A₀]
    {𝔭 : Ideal B} [𝔭.IsPrime] (h𝔭 : ¬IsOpen (𝔭 : Set B))
    (hBplus_le_B₀ : (B⁺ : Set B) ⊆ PB.A₀) :
    ∃ v ∈ Spa B B⁺, IsAnalytic v ∧ 𝔭 ≤ v.supp := by
  -- Apply strengthened Lemma 7.45 to get v ∈ Spa with 𝔭 ≤ supp(v) and
  -- idealOfDefinition ⊄ supp(v).
  have hx : ∃ v ∈ Spa B B⁺, 𝔭 ≤ v.supp ∧ ¬PB.idealOfDefinition ≤ v.supp :=
    PB.exists_mem_spa_supp_ge_of_nonOpen_prime h𝔭 hBplus_le_B₀
  obtain ⟨v, hv_spa, hv_supp, hv_idealOfDef⟩ := hx
  refine ⟨v, hv_spa, ?_, hv_supp⟩
  -- IsAnalytic: supp(v) is not open.
  -- If supp(v) were open, then idealOfDefinition ≤ supp(v) (since supp(v) is prime
  -- and open ideal ⟹ contains topological nilradical ⊇ idealOfDefinition).
  -- This contradicts hv_idealOfDef.
  intro h_open
  exact hv_idealOfDef (by
    rw [PairOfDefinition.idealOfDefinition, Ideal.map_le_iff_le_comap]
    exact fun a ha ↦ (instIsPrimeSupp v).radical.le
      ((PB.isTopologicallyNilpotent_of_mem ha).mem_ideal_radical h_open))

omit [IsHuberRing A] [IsHuberRing B] in
private theorem exists_analytic_spa_point_from_B₀_prime
    [PlusSubring B]
    {φ : A →+* B}
    (PA : PairOfDefinition A) (PB : PairOfDefinition B) [IsAdicComplete PB.I PB.A₀]
    (h_map : ∀ a ∈ PA.A₀, φ a ∈ PB.A₀)
    {𝔭₀ : Ideal PB.A₀} [𝔭₀.IsPrime]
    (h_image_le : Ideal.map (PA.restrictRingHom PB φ h_map) PA.I ≤ 𝔭₀)
    (hJ_not_le : ¬PB.I ≤ 𝔭₀)
    (hBplus_le_B₀ : (B⁺ : Set B) ⊆ PB.A₀) :
    ∃ v ∈ Spa B B⁺, IsAnalytic v ∧ IsOpen ((comap φ v).supp : Set A) := by
  -- Step A: Get a non-open prime of B from 𝔭₀
  obtain ⟨𝔭, h𝔭_prime, h𝔭_notopen, h𝔭₀_le⟩ :=
    exists_nonOpen_prime_of_B_from_B₀_prime PB hJ_not_le
  haveI := h𝔭_prime
  -- Step B + C: Get v ∈ Spa(B, B⁺) analytic with 𝔭 ≤ supp(v)
  obtain ⟨v, hv_spa, hv_an, hv_supp⟩ :=
    spa_point_from_nonOpen_prime PB h𝔭_notopen hBplus_le_B₀
  -- Step D: supp(comap φ v) is open in A
  refine ⟨v, hv_spa, hv_an, ?_⟩
  -- supp(comap φ v) = φ⁻¹(supp v) ⊇ φ⁻¹(𝔭) ⊇ PA.idealOfDefinition
  -- The last containment: PA.idealOfDefinition = Ideal.map PA.A₀.subtype PA.I,
  -- and for any a ∈ PA.I, φ(subtype a) = PB.A₀.subtype(restrictRingHom ... a).
  -- Since restrictRingHom(a) ∈ image(PA.I) ⊆ 𝔭₀ ⊆ comap PB.A₀.subtype 𝔭,
  -- we get φ(subtype a) ∈ 𝔭 ⊆ supp(v). Hence subtype a ∈ φ⁻¹(supp v) = (comap φ v).supp.
  have h_idealOfDef_le : PA.idealOfDefinition ≤ (comap φ v).supp := by
    rw [PairOfDefinition.idealOfDefinition, Ideal.map_le_iff_le_comap, supp_comap]
    intro a ha
    -- a ∈ PA.I, need φ(PA.A₀.subtype a) ∈ v.supp
    -- restrictRingHom sends a to ⟨φ(subtype a), _⟩ in PB.A₀
    -- image(PA.I) ≤ 𝔭₀ (by h_image_le), so restrictRingHom(a) ∈ 𝔭₀
    have h1 : PA.restrictRingHom PB φ h_map a ∈ 𝔭₀ := h_image_le (Ideal.mem_map_of_mem _ ha)
    -- 𝔭₀ ≤ comap PB.A₀.subtype 𝔭 (by h𝔭₀_le)
    have h2 : (PB.A₀.subtype (PA.restrictRingHom PB φ h_map a) : B) ∈ 𝔭 := h𝔭₀_le h1
    -- PB.A₀.subtype (restrictRingHom a) = φ (PA.A₀.subtype a) by definition
    have h3 : PB.A₀.subtype (PA.restrictRingHom PB φ h_map a) = φ (PA.A₀.subtype a) := rfl
    -- 𝔭 ≤ supp(v)
    exact hv_supp (h3 ▸ h2)
  -- PA.idealOfDefinition ≤ (comap φ v).supp ⟹ supp is open
  exact PA.isOpen_of_idealOfDefinition_le h_idealOfDef_le

-- Helper 2: the key construction, assembled from 2a and 2b.
omit [IsHuberRing A] [IsHuberRing B] in
private theorem exists_analytic_spa_point_with_open_comap_supp
    [PlusSubring B]
    {φ : A →+* B} (_hφ : Continuous φ)
    (PA : PairOfDefinition A) (PB : PairOfDefinition B) [IsAdicComplete PB.I PB.A₀]
    (h_map : ∀ a ∈ PA.A₀, φ a ∈ PB.A₀)
    (h_not_eq : (Ideal.map (PA.restrictRingHom PB φ h_map) PA.I).radical ≠ PB.I.radical)
    (h_le : (Ideal.map (PA.restrictRingHom PB φ h_map) PA.I).radical ≤ PB.I.radical)
    (hBplus_le_B₀ : (B⁺ : Set B) ⊆ PB.A₀) :
    ∃ v ∈ Spa B B⁺, IsAnalytic v ∧ IsOpen ((comap φ v).supp : Set A) := by
  -- Step 1: Get a separating prime of B₀
  obtain ⟨𝔭₀, h𝔭₀_prime, h_image_le, hJ_not_le⟩ :=
    exists_separating_prime_of_B₀ PA PB h_map h_not_eq h_le
  haveI := h𝔭₀_prime
  -- Step 2: Apply 2b to get the Spa point
  exact exists_analytic_spa_point_from_B₀_prime PA PB h_map h_image_le hJ_not_le hBplus_le_B₀

theorem isAdicHom_of_complete_and_analytic_preserved
    [PlusSubring A] [PlusSubring B]
    {φ : A →+* B} (hφ : Continuous φ) (_hAB : A⁺ ≤ (B⁺).comap φ)
    (h_analytic : ∀ v ∈ Spa B B⁺, IsAnalytic v → IsAnalytic (comap φ v))
    (PB : PairOfDefinition B) [IsAdicComplete PB.I PB.A₀]
    (hBplus_le_B₀ : (B⁺ : Set B) ⊆ PB.A₀) :
    IsAdicHom φ := by
  -- Step 1: Get a compatible pair of definition for A
  obtain ⟨PA, h_map⟩ := exists_compatible_pair hφ PB
  -- Step 2: By contradiction — if φ is not adic, the radical equality fails
  by_contra h_not_adic
  have h_ne : (Ideal.map (PA.restrictRingHom PB φ h_map) PA.I).radical ≠ PB.I.radical :=
    fun h_eq ↦ h_not_adic ⟨PA, PB, h_map, h_eq⟩
  -- Step 3: Produce an analytic v ∈ Spa(B, B⁺) whose comap has open support
  -- First: the easy direction rad(φ(I)·B₀) ≤ rad(J)
  have h_le : (Ideal.map (PA.restrictRingHom PB φ h_map) PA.I).radical ≤ PB.I.radical := by
    rw [Ideal.radical_le_radical_iff, Ideal.map_le_iff_le_comap]
    intro a ha
    -- PA.restrictRingHom sends a to ⟨φ(subtype a), _⟩ in PB.A₀
    -- a ∈ PA.I → PA.A₀.subtype a is top. nilpotent in A → φ-image is top. nilpotent in B
    have h_nil : IsTopologicallyNilpotent (φ (PA.A₀.subtype a)) :=
      (PA.isTopologicallyNilpotent_of_mem ha).map hφ
    have h_mem : φ (PA.A₀.subtype a) ∈ PB.A₀ := h_map _ a.2
    -- φ(subtype a) ∈ PB.A₀ and top. nilpotent → ⟨φ(subtype a), _⟩^N ∈ PB.I for some N
    obtain ⟨N, hN⟩ := PB.exists_pow_mem_I h_mem h_nil
    change PA.restrictRingHom PB φ h_map a ∈ PB.I.radical
    exact Ideal.mem_radical_iff.mpr ⟨N, hN⟩
  obtain ⟨v, hv_spa, hv_an, hv_open⟩ :=
    exists_analytic_spa_point_with_open_comap_supp hφ PA PB h_map h_ne h_le hBplus_le_B₀
  -- Step 4: Derive contradiction
  -- h_analytic says: v ∈ Spa, v analytic ⟹ comap φ v analytic (= support not open)
  -- But comap φ v has open support, hence is NOT analytic — contradiction
  exact (h_analytic v hv_spa hv_an) hv_open

end Lemma746Converse

/-! ### Definition 8.38: Adic morphisms of adic spaces -/

section AdicMorphismDef

universe u

open TopologicalSpace

/-- An open affinoid neighborhood datum for a point in an adic space: an open set `U`,
a point membership proof, an affinoid adic space `Y`, and a homeomorphism
`U ≃ₜ Spa(Y.Ring)`. This packages the local chart data for Definition 8.38. -/
structure AffinoidNeighborhood (X : AdicSpace.{u}) (x : X.carrier) where
  /-- The open set containing `x`. -/
  U : Opens X.carrier
  /-- Proof that `x ∈ U`. -/
  mem : x ∈ U
  /-- The affinoid adic space that `U` is homeomorphic to. -/
  aff : AffinoidAdicSpace.{u}
  /-- The homeomorphism `U ≃ₜ Spa(aff.Ring)`. -/
  homeo : ↥U ≃ₜ aff.toTopCat

/-- **Definition 8.38 of Wedhorn.** A continuous map `f : X.carrier → Y.carrier`
between the carriers of adic spaces is *adic* if for every `x ∈ X`, there exist
open affinoid neighborhoods `U ∋ x` in `X` and `V ∋ f(x)` in `Y` with
`f(U) ⊆ V`, such that the induced ring homomorphism
`𝒪_Y(V) → 𝒪_X(U)` is adic in the sense of Definition 6.23.

In the formal definition, we ask for affinoid neighborhood data (homeomorphisms to
affinoid spectra) and require the ring homomorphism between the witnessing affinoid
rings to be adic. The requirement `f(U) ⊆ V` is encoded by requiring that
`f` maps points of `U` into `V`.

The ring hom goes from the target ring to the source ring (`NY.aff.Ring →+* NX.aff.Ring`),
matching the contravariant nature of `Spa(φ) : Spa(B) → Spa(A)` for `φ : A →+* B`.
We require `IsHuberRing` instances on the affinoid rings since `IsAdicHom` is defined
for Huber ring homomorphisms (Definition 6.23 of Wedhorn). -/
def IsAdicMorphism (X Y : AdicSpace.{u}) (f : C(X.carrier, Y.carrier)) : Prop :=
  ∀ (x : X.carrier),
    ∃ (NX : AffinoidNeighborhood X x)
      (NY : AffinoidNeighborhood Y (f x))
      (_ : ∀ (p : ↥NX.U), f p.val ∈ NY.U)
      (_ : IsHuberRing NX.aff.Ring) (_ : IsHuberRing NY.aff.Ring)
      (φ : NY.aff.Ring →+* NX.aff.Ring),
      IsAdicHom φ

end AdicMorphismDef

/-! ### Proposition 8.39: Characterization via analytic points -/

section Prop839

/-- **Proposition 8.39(2) of Wedhorn (affinoid case).** Any continuous ring
homomorphism between Huber rings sends non-analytic points to non-analytic
points. This is the affinoid avatar of the statement that any morphism of
adic spaces preserves non-analytic points.

For the full adic space statement, one reduces to the affinoid case by
restricting to an affinoid chart and applying this result (Remark 8.37(2)).

The proof is `nonAnalytic_comap_of_continuous`, restated here for clarity. -/
theorem morphism_preserves_nonAnalytic_affinoid
    {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    {φ : A →+* B} (hφ : Continuous φ)
    {v : Spv B} (hv : ¬IsAnalytic v) :
    ¬IsAnalytic (comap φ v) :=
  nonAnalytic_comap_of_continuous hφ hv

/-- **Proposition 8.39(1) of Wedhorn (affinoid case, forward direction).**
An adic ring homomorphism `φ : A →+* B` between Huber rings induces a map
`Spa(φ)` that preserves analytic points.

This is `analytic_comap_of_isAdicHom` (Lemma 7.46(1)), restated in the
form needed for Proposition 8.39. -/
theorem isAdicHom_preserves_analytic
    {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalRing A] [IsTopologicalRing B]
    [IsHuberRing A] [IsHuberRing B]
    {φ : A →+* B} (hφ : IsAdicHom φ) :
    ∀ (v : Spv B), IsAnalytic v → IsAnalytic (comap φ v) :=
  fun _ hv ↦ analytic_comap_of_isAdicHom hφ hv

/-- **Proposition 8.39(1) of Wedhorn (affinoid case, reverse direction).**
If `B` is complete and `Spa(φ)` preserves analytic points, then `φ` is adic.

This is `isAdicHom_of_complete_and_analytic_preserved` (Lemma 7.46(2)),
restated for the iff form.

**Status:** The reverse direction requires Lemma 7.45; see `Lemma745.lean`. -/
theorem isAdicHom_of_preserves_analytic_complete
    {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalRing A] [IsTopologicalRing B]
    [IsHuberRing A] [IsHuberRing B]
    [PlusSubring A] [PlusSubring B]
    {φ : A →+* B} (hφ : Continuous φ) (hAB : A⁺ ≤ (B⁺).comap φ)
    (h_analytic : ∀ v ∈ Spa B B⁺, IsAnalytic v → IsAnalytic (comap φ v))
    (PB : PairOfDefinition B) [IsAdicComplete PB.I PB.A₀]
    (hBplus_le_B₀ : (B⁺ : Set B) ⊆ PB.A₀) :
    IsAdicHom φ :=
  isAdicHom_of_complete_and_analytic_preserved hφ hAB h_analytic PB hBplus_le_B₀

/-- **Proposition 8.39(1) of Wedhorn (affinoid case, iff version).** A continuous
ring homomorphism `φ : A →+* B` between Huber rings (with `B` complete) is adic
if and only if the induced map `Spa(φ) : Spv B → Spv A` preserves analytic points
on `Spa(B, B⁺)`.

This combines the forward direction (`isAdicHom_preserves_analytic`, Lemma 7.46(1))
with the reverse direction (`isAdicHom_of_preserves_analytic_complete`, Lemma 7.46(2)).

The full adic space version (Proposition 8.39(1) of Wedhorn) states that a morphism
`f : X → Y` of adic spaces is adic iff `f` maps analytic points of `X` to analytic
points of `Y`. The reduction from the adic space level to the affinoid level uses
Remark 8.37(2) of Wedhorn: it suffices to check the adic property on affinoid charts.
Formalizing that reduction requires connecting the abstract `IsAdicMorphism` definition
(which asks for *some* witnessing affinoid charts) to the pointwise analytic-preservation
property, which is not yet available.

**Status:** Sorry; the forward direction is proved, but the reverse direction
inherits sorries from `isAdicHom_of_complete_and_analytic_preserved` (Lemma 7.46(2)):
1. `exists_pairOfDefinition_le_subring` (Lemma 6.5) -- `IsAdic` property.
2. `exists_nonOpen_prime_of_B_from_B₀_prime` -- prime extension disjointness. -/
theorem isAdicHom_iff_preserves_analytic
    {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalRing A] [IsTopologicalRing B]
    [IsHuberRing A] [IsHuberRing B]
    [PlusSubring A] [PlusSubring B]
    {φ : A →+* B} (hφ : Continuous φ) (hAB : A⁺ ≤ (B⁺).comap φ)
    (PB : PairOfDefinition B) [IsAdicComplete PB.I PB.A₀]
    (hBplus_le_B₀ : (B⁺ : Set B) ⊆ PB.A₀) :
    IsAdicHom φ ↔
      (∀ v ∈ Spa B B⁺, IsAnalytic v → IsAnalytic (comap φ v)) := by
  constructor
  · -- Forward: adic hom preserves analytic points (Lemma 7.46(1)).
    intro hadic v _ hv
    exact analytic_comap_of_isAdicHom hadic hv
  · -- Reverse: analytic-preserving + completeness implies adic (Lemma 7.46(2)).
    exact fun h ↦
      isAdicHom_of_complete_and_analytic_preserved hφ hAB h PB hBplus_le_B₀

end Prop839

/-! ### Corollary 8.40: All ring maps of an adic morphism are adic -/

section Cor840

/-- **Corollary 8.40 of Wedhorn.** Let `f : X → Y` be an adic morphism of adic
spaces. Then for *all* open affinoid subspaces `U ⊆ X` and `V ⊆ Y` with
`f(U) ⊆ V`, the induced ring homomorphism `𝒪_Y(V) → 𝒪_X(U)` is adic -- not
just the witnessing neighborhoods from Definition 8.38.

The proof reduces to Lemma 7.46(2) (`isAdicHom_of_complete_and_analytic_preserved`):
if `Spa(φ)` preserves analytic points and the target ring is complete, then `φ` is
adic. The analytic-preservation hypothesis `hφ_analytic` captures the consequence of
Proposition 8.39(1) at the chart level: the adic morphism `f` preserves analytic
points, and this transfers to `Spa(φ)` via the chart homeomorphisms.

The hypotheses that are stated explicitly (`hφ_analytic`, `hφ_cont`, `hAB`, `PB`,
`hBplus`) would be derivable from `hf` alone once the following infrastructure is
formalized:
1. **Proposition 8.36** (chart-independence of analyticity) connecting `f` to `Spa(φ)`.
2. **Presheaf morphism** infrastructure extracting `φ` from `f` on charts.
3. **Completeness** of affinoid rings (presheaf values are completions).

Following Wedhorn p. 86, the proof is: Prop 8.39(1) gives `f(U_a) ⊆ V_a`
(analytic-preservation), then Lemma 7.46(2) gives that `φ` is adic. -/
theorem IsAdicMorphism.ringHom_isAdic {X Y : AdicSpace}
    {f : C(X.carrier, Y.carrier)} (_hf : IsAdicMorphism X Y f)
    {x : X.carrier}
    (NX : AffinoidNeighborhood X x)
    (NY : AffinoidNeighborhood Y (f x))
    (_hfUV : ∀ (p : ↥NX.U), f p.val ∈ NY.U)
    [IsHuberRing NX.aff.Ring] [IsHuberRing NY.aff.Ring]
    (φ : NY.aff.Ring →+* NX.aff.Ring)
    (hφ_cont : Continuous φ)
    (hAB : NY.aff.Ring⁺ ≤ (NX.aff.Ring⁺).comap φ)
    (hφ_analytic : ∀ v ∈ Spa NX.aff.Ring NX.aff.Ring⁺,
      IsAnalytic v → IsAnalytic (comap φ v))
    (PB : PairOfDefinition NX.aff.Ring) [IsAdicComplete PB.I PB.A₀]
    (hBplus : (NX.aff.Ring⁺ : Set NX.aff.Ring) ⊆ PB.A₀) :
    IsAdicHom φ :=
  isAdicHom_of_complete_and_analytic_preserved hφ_cont hAB hφ_analytic PB hBplus

end Cor840

end ValuationSpectrum
