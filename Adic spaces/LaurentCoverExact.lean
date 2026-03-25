/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Localization.Away.Basic
import «Adic spaces».TateAlgebra

/-!
# Laurent Cover Exactness (Wedhorn Lemma 8.33)

For any element `f ∈ A` (in a strongly noetherian Tate ring), the 2-element
Laurent cover yields an exact sequence:

  `0 → A → B₁ × B₂ → B₁₂ → 0`

where:
- `B₁ = A⟨ζ⟩/(f-ζ)` (presheaf at `R(f/1)`)
- `B₂ = A⟨η⟩/(1-fη)` (presheaf at `R(1/f)`)
- `B₁₂ = A⟨ζ,ζ⁻¹⟩/(f-ζ)` (presheaf at `R(f/1) ∩ R(1/f)`)

## Discrete case

For `[DiscreteTopology A]`:
- `B₁ ≅ A` (via `quotientFSubXEquiv`)
- `B₂ ≅ Localization.Away f` (via `quotientOneSubfXEquiv`)
- `B₁₂ ≅ Localization.Away f`
- The exact sequence becomes: `0 → A → A × A[1/f] → A[1/f] → 0`

This is the standard Čech complex for the cover `Spec A = D(f) ∪ Spec A`.

## General (non-discrete) case

For `[IsDomain A] [IsNoetherianRing A]` without `[DiscreteTopology A]`:
- `B₁` and `B₂` are defined as the same quotient rings (these are purely algebraic).
- The diagonal map `ε : A → B₁ × B₂` is injective when `f` is not a unit, via the
  Krull intersection theorem for domains: the coefficient recurrence from
  `(f - X) · c = algebraMap a` forces `a ∈ ⋂ₙ (f)ⁿ = 0`.
- Both quotients `B₁` and `B₂` are flat over `A` (from `flat_quotient_fSubX_general`
  and `flat_quotient_oneSubfX_general` in `TateAlgebra.lean`).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 8.33
-/

open TateAlgebra LaurentTateAlgebra

namespace LaurentCover

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-! ### The Laurent cover maps (Row 2 of the 3×3 diagram) -/

/-- The diagonal embedding `ι : A → A⟨ζ⟩ × A⟨η⟩` sending `a ↦ (a, a)`. -/
noncomputable def iotaHom :
    A →+* ↥(TateAlgebra A) × ↥(TateAlgebra A) :=
  RingHom.prod (algebraMap A ↥(TateAlgebra A)) (algebraMap A ↥(TateAlgebra A))

/-- The difference map `λ : A⟨ζ⟩ × A⟨η⟩ → A⟨ζ, ζ⁻¹⟩` sending
`(g, h) ↦ posEmb(g) - negEmb(h)`. This is an additive group homomorphism. -/
noncomputable def lambdaMap :
    ↥(TateAlgebra A) × ↥(TateAlgebra A) →+ LaurentTateAlgebra A where
  toFun p := posEmbHom p.1 - negEmbHom p.2
  map_zero' := by simp
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring

/-! ### Discrete case: direct exactness via ring isomorphisms -/

section Discrete

variable [DiscreteTopology A] [IsNoetherianRing A]

/-- `B₁ = A⟨X⟩/(f-X)` for the discrete case. -/
noncomputable abbrev B₁ (f : A) :=
  ↥(TateAlgebra A) ⧸ Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X}

/-- `B₂ = A⟨Y⟩/(1-fY)` for the discrete case. -/
noncomputable abbrev B₂ (f : A) :=
  ↥(TateAlgebra A) ⧸ Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X}

/-- The diagonal map `ε : A → B₁ × B₂` from Row 3. -/
noncomputable def epsilonHom (f : A) : A →+* B₁ f × B₂ f :=
  RingHom.prod
    ((Ideal.Quotient.mk _).comp (algebraMap A ↥(TateAlgebra A)))
    ((Ideal.Quotient.mk _).comp (algebraMap A ↥(TateAlgebra A)))

omit [IsNoetherianRing A] in
/-- `ε` is injective: the diagonal embedding into B₁ × B₂ is injective.
For discrete A, B₁ ≅ A via `quotientFSubXEquiv`, and the first projection
composed with this equivalence is the identity. -/
theorem epsilonHom_injective (f : A) : Function.Injective (epsilonHom f) := by
  intro a b hab
  have h1 := (Prod.mk.inj hab).1
  have hcomp : (TateAlgebra.quotientFSubXToA f).comp
      (TateAlgebra.AToQuotientFSubX f) = RingHom.id A :=
    TateAlgebra.quotientFSubXToA_comp_AToQuotientFSubX f
  have ha := RingHom.congr_fun hcomp a
  have hb := RingHom.congr_fun hcomp b
  simp only [RingHom.comp_apply, RingHom.id_apply] at ha hb
  rw [← ha, ← hb]
  exact congr_arg (TateAlgebra.quotientFSubXToA f) h1

/-- The δ map: `B₁ f × B₂ f →+ Localization.Away f` defined as the difference
of the two natural maps to `Localization.Away f`:
- First component: `B₁ f ≅ A → Localization.Away f` (algebraMap composed with equiv)
- Second component: `B₂ f ≅ Localization.Away f` (just the equiv)

This is the second map in the Cech complex for the Laurent cover. -/
noncomputable def deltaMap (f : A) : B₁ f × B₂ f →+ Localization.Away f where
  toFun p :=
    algebraMap A (Localization.Away f) (TateAlgebra.quotientFSubXToA f p.1) -
      TateAlgebra.quotientOneSubfXToLoc f p.2
  map_zero' := by simp [map_zero]
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    ring

omit [IsNoetherianRing A] in
/-- The composition `delta circ epsilon = 0`: the image of `epsilon` lands in the
kernel of `delta`. -/
theorem deltaMap_comp_epsilonHom (f : A) :
    ∀ a : A, deltaMap f (epsilonHom f a) = 0 := by
  intro a
  simp only [deltaMap, epsilonHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    RingHom.prod_apply, RingHom.comp_apply]
  have h1 : TateAlgebra.quotientFSubXToA f
      ((Ideal.Quotient.mk _) (algebraMap A ↥(TateAlgebra A) a)) = a := by
    have := RingHom.congr_fun (TateAlgebra.quotientFSubXToA_comp_AToQuotientFSubX f) a
    simp only [RingHom.comp_apply, RingHom.id_apply, TateAlgebra.AToQuotientFSubX] at this
    exact this
  have h2 : TateAlgebra.quotientOneSubfXToLoc f
      ((Ideal.Quotient.mk _) (algebraMap A ↥(TateAlgebra A) a)) =
      algebraMap A (Localization.Away f) a := by
    simp only [TateAlgebra.quotientOneSubfXToLoc, Ideal.Quotient.lift_mk,
      TateAlgebra.evalInvFHom_algebraMap]
  rw [h1, h2, sub_self]

omit [IsNoetherianRing A] in
/-- The delta map is surjective: given any element of `Localization.Away f`,
we can find a preimage in `B_1 f x B_2 f`. -/
theorem deltaMap_surjective (f : A) : Function.Surjective (deltaMap f) := by
  intro y
  refine ⟨(0, (TateAlgebra.quotientOneSubfXEquiv f).symm (-y)), ?_⟩
  simp only [deltaMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_zero]
  have h : TateAlgebra.quotientOneSubfXToLoc f
      ((TateAlgebra.quotientOneSubfXEquiv f).symm (-y)) = -y :=
    (TateAlgebra.quotientOneSubfXEquiv f).right_inv (-y)
  rw [h]
  ring

omit [IsNoetherianRing A] in
/-- Helper: `quotientOneSubfXToLoc` is injective (it's one direction of an equiv). -/
theorem quotientOneSubfXToLoc_injective (f : A) :
    Function.Injective (TateAlgebra.quotientOneSubfXToLoc f) :=
  (TateAlgebra.quotientOneSubfXEquiv f).injective

omit [IsNoetherianRing A] in
/-- Reverse inclusion: if `delta(b_1, b_2) = 0` then `(b_1, b_2)` is in the range
of `epsilon`. This uses that both equivalences allow us to recover the element
`a` in `A`. -/
theorem ker_deltaMap_le_range_epsilonHom (f : A) :
    ∀ p : B₁ f × B₂ f, deltaMap f p = 0 → ∃ a : A, epsilonHom f a = p := by
  intro ⟨b₁, b₂⟩ h
  simp only [deltaMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
  -- From h: algebraMap(quotientFSubXToA(b₁)) - quotientOneSubfXToLoc(b₂) = 0
  have heq : algebraMap A (Localization.Away f) (TateAlgebra.quotientFSubXToA f b₁) =
      TateAlgebra.quotientOneSubfXToLoc f b₂ := sub_eq_zero.mp h
  set a := TateAlgebra.quotientFSubXToA f b₁
  -- b₁ = AToQuotientFSubX(a) since the equiv round-trips
  have hb₁ : TateAlgebra.AToQuotientFSubX f a = b₁ := by
    change (TateAlgebra.quotientFSubXEquiv f).symm (TateAlgebra.quotientFSubXEquiv f b₁) = b₁
    exact (TateAlgebra.quotientFSubXEquiv f).symm_apply_apply b₁
  -- quotientOneSubfXToLoc(mk(algebraMap a)) = algebraMap(a)
  have himg : TateAlgebra.quotientOneSubfXToLoc f
      ((Ideal.Quotient.mk _) (algebraMap A ↥(TateAlgebra A) a)) =
      algebraMap A (Localization.Away f) a := by
    simp only [TateAlgebra.quotientOneSubfXToLoc, Ideal.Quotient.lift_mk,
      TateAlgebra.evalInvFHom_algebraMap]
  have hb₂ : (Ideal.Quotient.mk _) (algebraMap A ↥(TateAlgebra A) a) = b₂ := by
    apply quotientOneSubfXToLoc_injective f
    rw [himg, heq]
  exact ⟨a, Prod.ext hb₁ hb₂⟩

omit [IsNoetherianRing A] in
/-- **Laurent cover exactness (Wedhorn Lemma 8.33, discrete case).**
The sequence `0 -> A ->[epsilon] B_1 f x B_2 f ->[delta] Localization.Away f -> 0`
is exact:
1. `epsilon` is injective
2. `delta` is surjective
3. `delta circ epsilon = 0` (image of epsilon is contained in kernel of delta)
4. `ker delta` is a subset of `im epsilon` -/
theorem laurentCover_exact (f : A) :
    Function.Injective (epsilonHom f) ∧
    Function.Surjective (deltaMap f) ∧
    (∀ x, deltaMap f (epsilonHom f x) = 0) ∧
    (∀ p, deltaMap f p = 0 → ∃ a, epsilonHom f a = p) :=
  ⟨epsilonHom_injective f,
   deltaMap_surjective f,
   deltaMap_comp_epsilonHom f,
   ker_deltaMap_le_range_epsilonHom f⟩

end Discrete

/-! ### General (non-discrete) case: algebraic exactness via Krull intersection

For a noetherian domain `A` (without `[DiscreteTopology A]`), the quotient rings
`B₁ = A⟨X⟩/(f-X)` and `B₂ = A⟨X⟩/(1-fX)` are defined identically to the discrete
case. The key new result is the injectivity of the diagonal embedding `ε : A → B₁ × B₂`
for non-unit `f`, proved via the Krull intersection theorem.

The delta map and full exactness in the non-discrete case require completing these
quotients with respect to the T-topology (Wedhorn, Definition 8.27), which belongs
to the completed presheaf theory. Here we establish the algebraic ingredients. -/

section General

variable [IsNoetherianRing A] [IsDomain A]

/-- `B₁` for the general (non-discrete) case: the quotient `A⟨X⟩/(f-X)`.
This is the same type as the discrete `B₁`, but without requiring `[DiscreteTopology A]`. -/
noncomputable abbrev B₁_gen (f : A) :=
  ↥(TateAlgebra A) ⧸ Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X}

/-- `B₂` for the general (non-discrete) case: the quotient `A⟨X⟩/(1-fX)`.
This is the same type as the discrete `B₂`, but without requiring `[DiscreteTopology A]`. -/
noncomputable abbrev B₂_gen (f : A) :=
  ↥(TateAlgebra A) ⧸ Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X}

/-- The diagonal map `ε : A → B₁ × B₂` (general case, no `[DiscreteTopology A]`). -/
noncomputable def epsilonHom_gen (f : A) : A →+* B₁_gen f × B₂_gen f :=
  RingHom.prod
    ((Ideal.Quotient.mk _).comp (algebraMap A ↥(TateAlgebra A)))
    ((Ideal.Quotient.mk _).comp (algebraMap A ↥(TateAlgebra A)))

omit [IsNoetherianRing A] [IsDomain A] in
/-- The 0-th coefficient of a constant series equals the constant. -/
private theorem coeff_zero_algebraMap (a : A) :
    TateAlgebra.coeff 0 (algebraMap A ↥(TateAlgebra A) a) = a := by
  simp only [TateAlgebra.coeff, TateAlgebra.toIndex_zero]; norm_cast

omit [IsNoetherianRing A] [IsDomain A] in
/-- Higher coefficients of a constant series vanish. -/
private theorem coeff_succ_algebraMap (a : A) (n : ℕ) :
    TateAlgebra.coeff (n + 1) (algebraMap A ↥(TateAlgebra A) a) = 0 := by
  simp only [TateAlgebra.coeff, TateAlgebra.toIndex]
  change MvPowerSeries.coeff (Finsupp.single 0 (n + 1)) (algebraMap A _ a) = 0
  rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C]
  exact if_neg (Finsupp.single_ne_zero.mpr (Nat.succ_ne_zero n))

/-- If a constant `algebraMap a` lies in `Ideal.span {f - X}` and `f` is not a unit
in a noetherian domain, then `a = 0`.

The proof extracts the coefficient recurrence from `(f - X) · c = algebraMap a`:
- Constant term: `f · coeff 0 c = a`
- Higher terms: `coeff n c = f · coeff (n + 1) c` for all `n`

This yields `a = f^(n+1) · coeff n c`, hence `a ∈ (f)^n` for all `n`. Since `f`
is not a unit in a noetherian domain, the Krull intersection theorem
(`Ideal.iInf_pow_eq_bot_of_isDomain`) gives `a ∈ ⋂ₙ (f)ⁿ = 0`. -/
theorem algebraMap_mem_span_fSubX_eq_zero (f : A) (hf : ¬IsUnit f) (a : A)
    (h : algebraMap A ↥(TateAlgebra A) a ∈
      Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X}) : a = 0 := by
  rw [Ideal.mem_span_singleton'] at h
  obtain ⟨c, hc⟩ := h
  -- Rewrite with (f - X) on the left
  have hc' : (algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X) * c =
      algebraMap A _ a := by rw [mul_comm]; exact hc
  -- Coefficient equations from (f - X) * c = algebraMap a
  have hcoeff_eq : ∀ n,
      f * TateAlgebra.coeff n c - TateAlgebra.coeff n (TateAlgebra.X * c) =
      TateAlgebra.coeff n (algebraMap A ↥(TateAlgebra A) a) := by
    intro n; have := congr_arg (TateAlgebra.coeff n) hc'
    rw [sub_mul, TateAlgebra.coeff_sub, TateAlgebra.coeff_algebraMap_mul] at this
    exact this
  -- Constant coefficient: f * coeff 0 c = a
  have h0 : f * TateAlgebra.coeff 0 c = a := by
    have := hcoeff_eq 0
    rw [TateAlgebra.coeff_zero_X_mul, sub_zero, coeff_zero_algebraMap] at this
    exact this
  -- Recurrence: coeff n c = f * coeff (n + 1) c
  have hstep : ∀ n,
      TateAlgebra.coeff n c = f * TateAlgebra.coeff (n + 1) c := by
    intro n; have h1 := hcoeff_eq (n + 1)
    rw [TateAlgebra.coeff_succ_X_mul, coeff_succ_algebraMap] at h1
    exact (sub_eq_zero.mp h1).symm
  -- Power relation: coeff 0 c = f^n * coeff n c
  have hpow : ∀ n,
      TateAlgebra.coeff 0 c = f ^ n * TateAlgebra.coeff n c := by
    intro n; induction n with
    | zero => simp
    | succ n ih => rw [ih, hstep n, pow_succ, mul_assoc]
  -- a ∈ (f)^n for all n
  have ha_mem : ∀ n, a ∈ Ideal.span {f} ^ n := by
    intro n; cases n with
    | zero => simp [Ideal.one_eq_top]
    | succ n =>
      have : a = f ^ (n + 1) * TateAlgebra.coeff n c := by
        rw [← h0, hpow n]; ring
      rw [this]
      exact Ideal.mul_mem_right _ _
        (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self f) (n + 1))
  -- Krull intersection: ⋂_n (f)^n = 0 in a noetherian domain with (f) ≠ ⊤
  have hf_ne_top : Ideal.span ({f} : Set A) ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  exact Ideal.mem_bot.mp
    (Ideal.iInf_pow_eq_bot_of_isDomain _ hf_ne_top ▸ Ideal.mem_iInf.mpr ha_mem)

/-- **`ε` is injective (general case, Wedhorn Lemma 8.33 without `[DiscreteTopology A]`).**

For a noetherian domain `A` and non-unit `f`, the diagonal embedding
`ε : A → B₁(f) × B₂(f)` is injective. The proof uses the first projection:
if `ε(a) = ε(b)` then `algebraMap(a - b) ∈ (f - X)`, and the Krull intersection
theorem forces `a - b = 0`. -/
theorem epsilonHom_gen_injective (f : A) (hf : ¬IsUnit f) :
    Function.Injective (epsilonHom_gen f) := by
  intro a b hab
  have h1 := (Prod.mk.inj hab).1
  simp only [RingHom.comp_apply] at h1
  have hmem : algebraMap A ↥(TateAlgebra A) (a - b) ∈
      Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X} := by
    rw [map_sub]; exact Ideal.Quotient.eq.mp h1
  exact sub_eq_zero.mp (algebraMap_mem_span_fSubX_eq_zero f hf (a - b) hmem)

omit [IsDomain A] in
/-- Multiplication by `f - X` is injective on `A⟨X⟩` (general case, no topology needed
beyond `[IsNoetherianRing A]`). This is `TateAlgebra.mul_fSubX_regular`, re-exported
here for convenience. -/
theorem fSubX_regular (f : A) :
    ∀ x : ↥(TateAlgebra A),
      (algebraMap A _ f - TateAlgebra.X) * x = 0 → x = 0 :=
  TateAlgebra.mul_fSubX_regular f

omit [IsDomain A] in
/-- Multiplication by `1 - fX` is injective on `A⟨X⟩` (general case). This is
`TateAlgebra.mul_oneSubfX_regular`, re-exported here for convenience. -/
theorem oneSubfX_regular (f : A) :
    ∀ x : ↥(TateAlgebra A),
      (1 - algebraMap A _ f * TateAlgebra.X) * x = 0 → x = 0 :=
  TateAlgebra.mul_oneSubfX_regular f

end General

/-! ### Row 2 exactness: ker(lambda) = im(iota) (Wedhorn Lemma 8.33, Row 2)

The sequence `A ->[iota] A<X> x A<X> ->[lambda] A<zeta, zeta^{-1}>` is exact at
the middle term. The composition `lambda circ iota = 0` because both embeddings
`posEmbHom` and `negEmbHom` agree on constants from `A`. The reverse inclusion
`ker(lambda) <= im(iota)` uses the restricted power series structure: if
`posEmbHom(g) = negEmbHom(h)`, the ideal membership witness `c` satisfying
`(XY - 1) * c = posIncl(g) - negIncl(h)` is constant along diagonal lines in
the bivariate index space, and the restricted condition forces these constants
(hence all higher coefficients of `g` and `h`) to vanish. -/

section Row2Exactness

/-! #### Helper lemmas for bivariate coefficient manipulation -/

/-- A bivariate multi-index `(i, j) : Fin 2 →₀ ℕ`. -/
private noncomputable def idx (i j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i + Finsupp.single 1 j

private theorem idx_apply_zero (i j : ℕ) : idx i j 0 = i := by
  simp [idx]

private theorem idx_apply_one (i j : ℕ) : idx i j 1 = j := by
  simp [idx]

private theorem idx_eq_single_zero_iff (i j : ℕ) :
    idx i j = Finsupp.single 0 (idx i j 0) ↔ j = 0 := by
  rw [idx_apply_zero]
  constructor
  · intro h
    have := Finsupp.ext_iff.mp h 1
    simp [idx] at this
    exact this
  · intro hj
    subst hj; ext k; fin_cases k <;> simp [idx]

private theorem idx_eq_single_one_iff (i j : ℕ) :
    idx i j = Finsupp.single 1 (idx i j 1) ↔ i = 0 := by
  rw [idx_apply_one]
  constructor
  · intro h
    have := Finsupp.ext_iff.mp h 0
    simp [idx] at this
    exact this
  · intro hi
    subst hi; ext k; fin_cases k <;> simp [idx]

private theorem idx_zero_zero : idx 0 0 = (0 : Fin 2 →₀ ℕ) := by
  ext k; fin_cases k <;> simp [idx]

/-- Every `Fin 2 →₀ ℕ` index equals `idx (e 0) (e 1)`. -/
private theorem eq_idx (e : Fin 2 →₀ ℕ) : e = idx (e 0) (e 1) := by
  ext k; fin_cases k <;> simp [idx]

/-- The RHS coefficient: `posIncl g` at index `idx i j`. -/
private theorem coeff_posIncl (g : ↥(TateAlgebra A)) (i j : ℕ) :
    MvPowerSeries.coeff (idx i j) (posIncl g).val =
      if j = 0 then MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) i) g.val else 0 := by
  change varInclFun 0 g.val (idx i j) = _
  rw [varInclFun_apply]
  have h1 : idx i j 0 = i := idx_apply_zero i j
  rw [h1]
  have h2 : (idx i j = Finsupp.single 0 i) ↔ j = 0 := by
    rw [show Finsupp.single (0 : Fin 2) i = Finsupp.single 0 (idx i j 0) from by rw [h1]]
    exact idx_eq_single_zero_iff i j
  by_cases hj : j = 0
  · rw [if_pos (h2.mpr hj), if_pos hj]
  · rw [if_neg (mt h2.mp hj), if_neg hj]

/-- The RHS coefficient: `negIncl h` at index `idx i j`. -/
private theorem coeff_negIncl (h : ↥(TateAlgebra A)) (i j : ℕ) :
    MvPowerSeries.coeff (idx i j) (negIncl h).val =
      if i = 0 then MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) j) h.val else 0 := by
  change varInclFun 1 h.val (idx i j) = _
  rw [varInclFun_apply]
  have h1 : idx i j 1 = j := idx_apply_one i j
  rw [h1]
  have h2 : (idx i j = Finsupp.single 1 j) ↔ i = 0 := by
    rw [show Finsupp.single (1 : Fin 2) j = Finsupp.single 1 (idx i j 1) from by rw [h1]]
    exact idx_eq_single_one_iff i j
  by_cases hi : i = 0
  · rw [if_pos (h2.mpr hi), if_pos hi]
  · rw [if_neg (mt h2.mp hi), if_neg hi]

private theorem idx_11 :
    Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1 = idx 1 1 := by
  ext k; fin_cases k <;> simp [idx]

omit [TopologicalSpace A] [NonarchimedeanRing A] in
/-- The LHS: coefficient of `(X₀ * X₁ - 1) * c` at index `idx i j`.
This equals `c(i-1, j-1) - c(i, j)` when `i, j ≥ 1`, and `-c(i, j)` otherwise. -/
private theorem coeff_XY_sub_one_mul (c : MvPowerSeries (Fin 2) A) (i j : ℕ) :
    MvPowerSeries.coeff (idx i j)
      ((MvPowerSeries.X 0 * MvPowerSeries.X 1 - 1) * c) =
      (if 0 < i ∧ 0 < j then MvPowerSeries.coeff (idx (i - 1) (j - 1)) c else 0) -
      MvPowerSeries.coeff (idx i j) c := by
  have hsub : MvPowerSeries.coeff (idx i j) ((MvPowerSeries.X 0 * MvPowerSeries.X 1 - 1) * c) =
    MvPowerSeries.coeff (idx i j) (MvPowerSeries.X 0 * MvPowerSeries.X 1 * c) -
    MvPowerSeries.coeff (idx i j) (1 * c) := by
    rw [sub_mul]; exact map_sub _ _ _
  rw [hsub, one_mul]
  congr 1
  -- Need: coeff_{idx i j} (X₀ * X₁ * c) = if (0 < i ∧ 0 < j) then c(i-1, j-1) else 0
  rw [show MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) =
    MvPowerSeries.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) (1 : A) by
    rw [MvPowerSeries.X, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial, one_mul]]
  rw [MvPowerSeries.coeff_monomial_mul]
  set m := Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1
  by_cases h : m ≤ idx i j
  · rw [if_pos h, one_mul]
    have hi : 0 < i := by
      have h0 := h (0 : Fin 2)
      simp [m, idx] at h0; omega
    have hj : 0 < j := by
      have h1 := h (1 : Fin 2)
      simp [m, idx] at h1; omega
    rw [if_pos ⟨hi, hj⟩]
    have hsub_eq : idx i j - m = idx (i - 1) (j - 1) := by
      apply Finsupp.ext; intro k
      simp only [Finsupp.tsub_apply, idx, m, Finsupp.add_apply, Finsupp.single_apply]
      fin_cases k <;> (simp (config := { decide := true }); try omega)
    rw [hsub_eq]
  · rw [if_neg h]
    have hnotij : ¬(0 < i ∧ 0 < j) := by
      intro ⟨hi, hj⟩; apply h; intro k
      fin_cases k <;> simp [m, idx] <;> omega
    rw [if_neg hnotij]

omit [NonarchimedeanRing A] in
/-- In a T1 space, if a restricted power series has a constant value `b` along infinitely
many indices, then `b = 0`. More precisely, if `tendsto (coeff s) cofinite (nhds 0)` and
there is an injection `ℕ → σ →₀ ℕ` such that `coeff` is constantly `b` on the range,
then `b = 0`. -/
private theorem eq_zero_of_restricted_const [T1Space A] {σ : Type*}
    (f : (σ →₀ ℕ) → A) (hf : Filter.Tendsto f Filter.cofinite (nhds 0))
    (ι : ℕ → σ →₀ ℕ) (hinj : Function.Injective ι)
    {b : A} (hconst : ∀ n, f (ι n) = b) : b = 0 := by
  by_contra hne
  -- In a T1 space, singletons are closed, so {b}ᶜ is open and contains 0
  have hopen : IsOpen ({b}ᶜ : Set A) := isOpen_compl_singleton
  have h0 : (0 : A) ∈ ({b}ᶜ : Set A) := Set.mem_compl_singleton_iff.mpr (Ne.symm hne)
  -- The set of indices where f ∉ {b}ᶜ (i.e., f = b) is finite by restrictedness
  have hmem : {b}ᶜ ∈ nhds (0 : A) := hopen.mem_nhds h0
  have hev := hf hmem
  rw [Filter.mem_map, Filter.mem_cofinite] at hev
  -- hev : {s | f s ∉ {b}ᶜ} is cofinite, i.e. {s | f s = b} is finite (in complement form)
  -- But the range of ι is infinite and lands in {s | f s = b}
  have hinf : Set.Infinite (Set.range ι) := Set.infinite_range_of_injective hinj
  have hrange_sub : Set.range ι ⊆ {s | f s ∉ ({b}ᶜ : Set A)} := by
    rintro s ⟨n, rfl⟩
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff, not_not]
    exact hconst n
  exact (hev.subset hrange_sub).not_infinite hinf

private theorem posIncl_algebraMap (a : A) :
    posIncl (algebraMap A ↥(TateAlgebra A) a) =
      algebraMap A ↥(TateAlgebra₂ A) a := by
  ext1; apply MvPowerSeries.ext; intro e
  change varInclFun 0 (algebraMap A (MvPowerSeries (Fin 1) A) a) e =
    (MvPowerSeries.coeff e) (algebraMap A (MvPowerSeries (Fin 2) A) a)
  rw [varInclFun_apply]
  simp only [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C]
  by_cases he : e = 0
  · subst he; simp [Finsupp.single_zero (0 : Fin 2)]
  · rw [if_neg he]
    by_cases h1 : e = Finsupp.single (0 : Fin 2) (e 0)
    · rw [if_pos h1]
      exact if_neg (Finsupp.single_ne_zero.mpr
        (fun h => he (by rw [h1, h, Finsupp.single_zero])))
    · rw [if_neg h1]

private theorem negIncl_algebraMap (a : A) :
    negIncl (algebraMap A ↥(TateAlgebra A) a) =
      algebraMap A ↥(TateAlgebra₂ A) a := by
  ext1; apply MvPowerSeries.ext; intro e
  change varInclFun 1 (algebraMap A (MvPowerSeries (Fin 1) A) a) e =
    (MvPowerSeries.coeff e) (algebraMap A (MvPowerSeries (Fin 2) A) a)
  rw [varInclFun_apply]
  simp only [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C]
  by_cases he : e = 0
  · subst he; simp [Finsupp.single_zero (1 : Fin 2)]
  · rw [if_neg he]
    by_cases h1 : e = Finsupp.single (1 : Fin 2) (e 1)
    · rw [if_pos h1]
      exact if_neg (Finsupp.single_ne_zero.mpr
        (fun h => he (by rw [h1, h, Finsupp.single_zero])))
    · rw [if_neg h1]

/-- The composition `lambda circ iota = 0`: the image of `iotaHom` lies in
the kernel of `lambdaMap`. Both embeddings `posEmbHom` and `negEmbHom`
agree on constants from `A`. -/
theorem lambdaMap_comp_iotaHom (a : A) : lambdaMap (iotaHom a) = 0 := by
  simp only [lambdaMap, iotaHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    RingHom.prod_apply]
  rw [sub_eq_zero]
  change mkHom (posIncl (algebraMap A ↥(TateAlgebra A) a)) =
    mkHom (negIncl (algebraMap A ↥(TateAlgebra A) a))
  rw [posIncl_algebraMap, negIncl_algebraMap]

/-- **Kernel exactness (Row 2): `ker(lambda) <= im(iota)`.**

If `posEmbHom(g) = negEmbHom(h)` in the Laurent algebra, then `g` and `h`
are both equal to `algebraMap(a)` for some `a : A`.

**Proof sketch.** The hypothesis gives `posIncl(g) - negIncl(h) in (XY - 1)`,
so there exists a restricted `c` with `c * (XY - 1) = posIncl(g) - negIncl(h)`.
Since `posIncl(g) - negIncl(h)` vanishes at all mixed indices `(m, n)` with
`m, n >= 1`, extracting the coefficient at such an index from the equation
gives the diagonal recurrence `c_{m,n} = c_{m-1,n-1}`. Iterating shows `c` is
constant along each line parallel to the main diagonal. In a T1 topological
ring, the restricted condition on `c` forces each such constant to be zero.
The boundary conditions `-c_{k,0} = g_k` and `c_{0,k} = h_k` then give
`g_k = h_k = 0` for `k >= 1`, and the diagonal `c_{n,n} = c_{0,0} = 0`
gives `g_0 = h_0`. -/
theorem ker_lambdaMap_le_range_iotaHom [T1Space A]
    (p : ↥(TateAlgebra A) × ↥(TateAlgebra A))
    (hp : lambdaMap p = 0) :
    ∃ a : A, iotaHom a = p := by
  obtain ⟨g, h⟩ := p
  have heq_laurent : posEmbHom g = negEmbHom h := by
    simp only [lambdaMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hp
    exact sub_eq_zero.mp hp
  have hmem : posIncl g - negIncl h ∈ laurentIdeal A := by
    change posIncl g - negIncl h ∈ Ideal.span {TateAlgebra₂.XY_sub_one}
    rw [← Ideal.Quotient.eq]; exact heq_laurent
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  -- hc: c * XY_sub_one = posIncl g - negIncl h
  -- Translate to MvPowerSeries level with (XY - 1) on the left
  have hc_ps : (MvPowerSeries.X (0 : Fin 2) *
      MvPowerSeries.X (1 : Fin 2) - 1) * c.val =
      (posIncl g).val - (negIncl h).val := by
    have := congr_arg Subtype.val hc; rw [mul_comm] at this; exact this
  -- Step 1: Extract the coefficient equation at every (i, j)
  -- From hc_ps, for each (i,j): (XY-1)*c at (i,j) = (posIncl g - negIncl h) at (i,j)
  have hcoeff_eq : ∀ i j,
      (if 0 < i ∧ 0 < j then MvPowerSeries.coeff (idx (i - 1) (j - 1)) c.val else 0) -
        MvPowerSeries.coeff (idx i j) c.val =
      MvPowerSeries.coeff (idx i j) (posIncl g).val -
        MvPowerSeries.coeff (idx i j) (negIncl h).val := by
    intro i j
    have h1 := congr_arg (MvPowerSeries.coeff (idx i j)) hc_ps
    rw [coeff_XY_sub_one_mul] at h1
    rwa [map_sub] at h1
  -- Step 2: Diagonal recurrence: for i ≥ 1, j ≥ 1, c(i,j) = c(i-1,j-1)
  have hdiag : ∀ i j, 0 < i → 0 < j →
      MvPowerSeries.coeff (idx i j) c.val =
      MvPowerSeries.coeff (idx (i - 1) (j - 1)) c.val := by
    intro i j hi hj
    have h1 := hcoeff_eq i j
    rw [if_pos ⟨hi, hj⟩] at h1
    -- RHS: posIncl g at (i,j) with i ≥ 1, j ≥ 1 is 0; negIncl h at (i,j) with i ≥ 1 is 0
    rw [coeff_posIncl, if_neg (by omega : ¬(j = 0))] at h1
    rw [coeff_negIncl, if_neg (by omega : ¬(i = 0))] at h1
    -- h1 : c(i-1,j-1) - c(i,j) = 0 - 0
    simp only [sub_zero] at h1
    -- h1 : c(i-1,j-1) - c(i,j) = 0
    exact eq_of_sub_eq_zero h1 |>.symm
  -- Step 2b: Iterated diagonal: c(i+k, j+k) = c(i, j) for all k
  have hdiag_iter : ∀ i j k,
      MvPowerSeries.coeff (idx (i + k) (j + k)) c.val =
      MvPowerSeries.coeff (idx i j) c.val := by
    intro i j k; induction k with
    | zero => simp
    | succ k ih =>
      rw [show i + (k + 1) = (i + k) + 1 from by omega,
          show j + (k + 1) = (j + k) + 1 from by omega]
      rw [hdiag _ _ (by omega) (by omega)]
      simp only [show (i + k + 1) - 1 = i + k from by omega,
                  show (j + k + 1) - 1 = j + k from by omega]
      exact ih
  -- Step 3: c is restricted (coefficients tend to 0)
  have hc_restr : Filter.Tendsto
      (fun s => MvPowerSeries.coeff s c.val) Filter.cofinite (nhds 0) := c.prop
  -- Step 4: Along diagonal n+k, k (for n ≥ 1): c(n+k,k) = c(n,0) = -coeff_n g
  -- First: boundary equation at (n, 0) for n ≥ 1: -c(n,0) = coeff_n g
  have hboundary_x : ∀ n, 0 < n →
      MvPowerSeries.coeff (idx n 0) c.val =
      -(MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) n) g.val) := by
    intro n hn
    have h1 := hcoeff_eq n 0
    rw [if_neg (by omega : ¬(0 < n ∧ 0 < 0))] at h1
    rw [coeff_posIncl, if_pos rfl, coeff_negIncl, if_neg (by omega : ¬(n = 0))] at h1
    -- h1 : 0 - c(n,0) = coeff_n g - 0
    simp only [zero_sub, sub_zero] at h1
    -- h1 : -c(n,0) = coeff_n g, so c(n,0) = -coeff_n g
    have : MvPowerSeries.coeff (idx n 0) c.val =
        -(MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) n) g.val) := by
      rw [← h1, neg_neg]
    exact this
  -- Boundary equation at (0, m) for m ≥ 1: -c(0,m) = -coeff_m h, i.e. c(0,m) = coeff_m h
  have hboundary_y : ∀ m, 0 < m →
      MvPowerSeries.coeff (idx 0 m) c.val =
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) m) h.val := by
    intro m hm
    have h1 := hcoeff_eq 0 m
    rw [if_neg (by omega : ¬(0 < 0 ∧ 0 < m))] at h1
    rw [coeff_posIncl, if_neg (by omega : ¬(m = 0)), coeff_negIncl, if_pos rfl] at h1
    -- h1 : 0 - c(0,m) = 0 - coeff_m h
    simp only [zero_sub] at h1
    -- h1 : -c(0,m) = -coeff_m h
    exact neg_injective h1
  -- Boundary at (0, 0): -c(0,0) = coeff_0 g - coeff_0 h
  have hboundary_00 :
      MvPowerSeries.coeff (idx 0 0) c.val =
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) 0) h.val -
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) 0) g.val := by
    have h1 := hcoeff_eq 0 0
    rw [if_neg (by omega : ¬(0 < 0 ∧ 0 < 0))] at h1
    rw [coeff_posIncl, if_pos rfl, coeff_negIncl, if_pos rfl] at h1
    -- h1 : 0 - c(0,0) = coeff_0 g - coeff_0 h
    simp only [zero_sub] at h1
    -- h1 : -c(0,0) = coeff_0 g - coeff_0 h
    -- Want: c(0,0) = coeff_0 h - coeff_0 g
    have : MvPowerSeries.coeff (idx 0 0) c.val =
      -(MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) 0) g.val -
       MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) 0) h.val) := by
      rw [← h1, neg_neg]
    rw [this]; ring
  -- Step 5: For n ≥ 1, the diagonal c(n+k, k) = c(n, 0) for all k.
  -- This is constant, and by restricted condition in T1 space, must be 0.
  -- Therefore coeff_n g = 0 for all n ≥ 1.
  have hg_higher_zero : ∀ n, 0 < n →
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) n) g.val = 0 := by
    intro n hn
    -- c(n, 0) = -coeff_n g, and c(n+k, k) = c(n, 0) for all k
    have hconst : ∀ k, MvPowerSeries.coeff (idx (n + k) k) c.val =
        MvPowerSeries.coeff (idx n 0) c.val := by
      intro k
      have := hdiag_iter n 0 k
      simp only [Nat.zero_add] at this; exact this
    -- The injection ℕ → Fin 2 →₀ ℕ sending k ↦ idx (n + k) k
    have hinj : Function.Injective (fun k => idx (n + k) k) := by
      intro a b hab
      have := Finsupp.ext_iff.mp hab 1
      simp [idx] at this; omega
    -- By restricted + T1, the constant value must be 0
    have h0 := eq_zero_of_restricted_const (fun s => MvPowerSeries.coeff s c.val)
      hc_restr (fun k => idx (n + k) k) hinj hconst
    rw [hboundary_x n hn] at h0
    -- h0 : -(coeff_n g) = 0
    exact neg_eq_zero.mp h0
  -- Step 6: Similarly, coeff_m h = 0 for all m ≥ 1.
  have hh_higher_zero : ∀ m, 0 < m →
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) m) h.val = 0 := by
    intro m hm
    have hconst : ∀ k, MvPowerSeries.coeff (idx k (m + k)) c.val =
        MvPowerSeries.coeff (idx 0 m) c.val := by
      intro k
      have := hdiag_iter 0 m k
      simp only [Nat.zero_add] at this; exact this
    have hinj : Function.Injective (fun k => idx k (m + k)) := by
      intro a b hab
      have := Finsupp.ext_iff.mp hab 0
      simp [idx] at this; omega
    have h0 := eq_zero_of_restricted_const (fun s => MvPowerSeries.coeff s c.val)
      hc_restr (fun k => idx k (m + k)) hinj hconst
    rw [hboundary_y m hm] at h0
    exact h0
  -- Step 7: c(0,0) = 0, which gives coeff_0 g = coeff_0 h.
  have hc00_zero : MvPowerSeries.coeff (idx 0 0) c.val = 0 := by
    have hconst : ∀ k, MvPowerSeries.coeff (idx k k) c.val =
        MvPowerSeries.coeff (idx 0 0) c.val := by
      intro k
      have := hdiag_iter 0 0 k
      simp only [Nat.zero_add] at this; exact this
    have hinj : Function.Injective (fun k => idx k k) := by
      intro a b hab
      have := Finsupp.ext_iff.mp hab 0
      simp [idx] at this; omega
    exact eq_zero_of_restricted_const (fun s => MvPowerSeries.coeff s c.val)
      hc_restr (fun k => idx k k) hinj hconst
  have hg0_eq_h0 :
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) 0) g.val =
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) 0) h.val := by
    have := hboundary_00
    rw [hc00_zero] at this
    -- this : 0 = coeff_0 h - coeff_0 g
    -- So coeff_0 h - coeff_0 g = 0, hence coeff_0 h = coeff_0 g
    exact (eq_of_sub_eq_zero this.symm).symm
  -- Step 8: Assemble. Set a = coeff_0 g (as TateAlgebra.coeff).
  -- coeff_zero_algebraMap and coeff_succ_algebraMap use TateAlgebra.coeff.
  set a := TateAlgebra.coeff 0 g with ha_def
  -- Convert MvPowerSeries-level results to TateAlgebra.coeff
  have hg0_eq_h0' : TateAlgebra.coeff 0 g = TateAlgebra.coeff 0 h :=
    hg0_eq_h0  -- both are definitionally MvPowerSeries.coeff (Finsupp.single 0 0) _.val
  have hg_higher' : ∀ n, 0 < n → TateAlgebra.coeff n g = 0 :=
    hg_higher_zero  -- TateAlgebra.coeff n = MvPowerSeries.coeff (Finsupp.single 0 n) _.val
  have hh_higher' : ∀ n, 0 < n → TateAlgebra.coeff n h = 0 :=
    hh_higher_zero
  refine ⟨a, ?_⟩
  rw [show iotaHom a = (algebraMap A ↥(TateAlgebra A) a,
    algebraMap A ↥(TateAlgebra A) a) from rfl]
  -- Prove g = algebraMap a
  have hg_eq : algebraMap A ↥(TateAlgebra A) a = g := by
    apply TateAlgebra.ext; intro n
    cases n with
    | zero => rw [coeff_zero_algebraMap]
    | succ n =>
      rw [coeff_succ_algebraMap]
      exact (hg_higher' (n + 1) (Nat.succ_pos n)).symm
  -- Prove h = algebraMap a
  have hh_eq : algebraMap A ↥(TateAlgebra A) a = h := by
    apply TateAlgebra.ext; intro n
    cases n with
    | zero => rw [coeff_zero_algebraMap]; rw [ha_def]; exact hg0_eq_h0'
    | succ n =>
      rw [coeff_succ_algebraMap]
      exact (hh_higher' (n + 1) (Nat.succ_pos n)).symm
  exact Prod.ext hg_eq hh_eq

/-- **Row 2 exactness of the Laurent cover (Wedhorn Lemma 8.33, Row 2).**
1. `lambda circ iota = 0`: both embeddings agree on constants.
2. `ker(lambda) <= im(iota)`: restricted condition forces constants. -/
theorem row2_exact_at_middle [T1Space A] :
    (∀ a : A, lambdaMap (iotaHom a) = 0) ∧
    (∀ p : ↥(TateAlgebra A) × ↥(TateAlgebra A),
      lambdaMap p = 0 → ∃ a : A, iotaHom a = p) :=
  ⟨lambdaMap_comp_iotaHom, ker_lambdaMap_le_range_iotaHom⟩

end Row2Exactness

end LaurentCover
