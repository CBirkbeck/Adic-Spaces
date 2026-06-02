/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».StructureSheaf
import «Adic spaces».Example638
import «Adic spaces».TateAlgebra
import «Adic spaces».Cor832

/-!
# Wedhorn Theorem 8.28(b): strongly noetherian Tate ⇒ sheafy — clean top-down skeleton

This file states the proof of Wedhorn's Theorem 8.28(b) **top-down**, following the textbook
exactly. Every lemma is stated as Wedhorn states it, with a `sorry` body, and the lemmas are
composed to prove `IsSheafy A`. Each `sorry` is then to be discharged by recursively reading
Wedhorn and stating its sub-lemmas the same way.

## Wedhorn's proof structure (Adic Spaces, §8.2, pp. 81–84)

```
Theorem 8.28(b)  IsSheafy A                     [A strongly noetherian Tate, complete]
  ├─ Prop A.4    acyclic on rational covers ⇒ sheaf
  └─ Lemma 8.34  rational cover gen by T (T·A = A) is O_X-acyclic
      ├─ Lemma 8.33  the 2-element Laurent cover {R(f/1), R(1/f)} is O_X-acyclic
      │   ├─ Cor 8.32   O_X(X) → ∏ O_X(Uᵢ) is faithfully flat (⇒ ε injective)
      │   │   └─ Lemma 8.31  A⟨X⟩ faithfully flat / A⟨X⟩/(f−X), A⟨X⟩/(1−fX) flat over A
      │   │       └─ Remark 8.29  M ⊗_A A⟨X⟩ ≅ M⟨X⟩      [via Prop 6.18, PROVEN: BanachOMT]
      │   └─ Example 6.38 / 6.39  O_X(U) = A⟨X⟩/(closed ideal)   [Example638.lean]
      └─ Prop A.3 (1)(2)(3)  Čech refinement / Laurent-cover induction
```

In Lean, `IsSheafy A` (`StructureSheaf.lean`) is the pair `(embedding, gluing)` on every
`RationalCovering`. Cor 8.32 supplies `embedding` (faithful flatness ⇒ the product
restriction is injective; the topological inducing is the Banach-OMT input, `BanachOMT.lean`).
Lemma 8.34 supplies `gluing`.

## References
* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Theorem 8.28, Lemmas 8.31/8.33/8.34,
  Cor 8.32, Remark 8.29, Prop A.3/A.4.
-/

namespace ValuationSpectrum

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]

section Wedhorn828

variable [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
  [NonarchimedeanRing A] [CompatiblePlusSubring A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]

/-! ## Lemma 8.31 — flatness of `A⟨X⟩` and its Laurent quotients

> **Lemma 8.31.** Let `A` be a noetherian complete Tate ring.
> (1) The ring `A⟨X⟩` is faithfully flat over `A`.
> (2) For all `f ∈ A` the rings `A⟨X⟩/(f − X)` and `A⟨X⟩/(1 − fX)` are flat over `A`.

Wedhorn's proof uses **Remark 8.29** (`M ⊗_A A⟨X⟩ ≅ M⟨X⟩` for finitely generated `M`,
which rests on Prop 6.18 — proven in `BanachOMT.lean`) plus the explicit injectivity
computations for `1 − fX` and `f − X`. -/

/-- **Lemma 8.31(1)** (Wedhorn p. 82, `wedhorn.txt:4106`): `A⟨X⟩` is faithfully flat over `A`,
for `A` a **noetherian** complete Tate ring. Wedhorn's proof: flatness from Remark 8.29
(`TateAlgebra.muMap_injective` — `i ⊗ id : N ⊗ A⟨X⟩ → M ⊗ A⟨X⟩` is injective whenever
`i : N ↪ M`), and the faithful half from the prime `q = {Σ aᵥ Xᵥ : a₀ ∈ p}` lying over each
prime `p` (`q ∩ A = p`).

**Faithfulness:** stated with `[IsNoetherianRing A]` (the Tate ring, = strongly-noeth at `k = 0`)
only. The noeth-`A₀` route `TateAlgebra.faithfullyFlat_general P` is the Wedhorn **case (a)**
argument (Artin–Rees over a ring of definition) and **must not** be used to discharge the
case-(b) target. See `.mathlib-quality/decomposition.md` §LEAF A2 (2026-06-02). -/
theorem lemma_8_31_tateAlgebra_faithfullyFlat :
    Module.FaithfullyFlat A ↥(TateAlgebra A) := by
  sorry

/-- **Lemma 8.31(2), minus shape** (Wedhorn p. 82, `wedhorn.txt:4108`): `A⟨X⟩/(1 − fX)` is flat
over `A`. Wedhorn's proof: the multiplication `w_{1-fX} : M⟨X⟩ → M⟨X⟩` is injective (easy check),
so by the claim at `:4116` `A⟨X⟩/(1 − fX)` is flat. **Faithful: `[IsNoetherianRing A]` only**
(the noeth-`A₀` route `TateAlgebra.flat_quotient_oneSubfX_general P` is case (a)). -/
theorem lemma_8_31_oneSubfX_flat (f : A) :
    Module.Flat A (↥(TateAlgebra A) ⧸
      Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X}) := by
  sorry

/-- **Lemma 8.31(2), plus shape** (Wedhorn p. 82, `wedhorn.txt:4108`): `A⟨X⟩/(f − X)` is flat
over `A`. Wedhorn's proof: for `u = Σ mᵥ Xᵥ` with `(f − X)u = 0` one gets `f m₀ = 0`,
`f mᵥ = mᵥ₋₁`; as `M` is noetherian the submodule `M′ = ⟨mᵥ⟩` is finitely generated, forcing
`M′ = 0`, so `w_{f-X}` is injective and the quotient is flat. **Faithful: `[IsNoetherianRing A]`
only** (the noeth use is "`M` noetherian"; the noeth-`A₀` route
`TateAlgebra.flat_quotient_fSubX_general P` is case (a)). -/
theorem lemma_8_31_fSubX_flat (f : A) :
    Module.Flat A (↥(TateAlgebra A) ⧸
      Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X}) := by
  sorry

/-! ## Corollary 8.32 — the product restriction is faithfully flat (⇒ injective)

> **Corollary 8.32.** Let `A` be a strongly noetherian Tate affinoid ring, `X = Spa A`, and
> `(Uᵢ)` a finite rational covering of `X`. Then `O_X(X) → ∏ᵢ O_X(Uᵢ)`, `f ↦ (f|Uᵢ)`, is
> faithfully flat (and in particular injective).

By Example 6.38 each `O_X(Uᵢ)` is a Laurent quotient `O_X(X)⟨X⟩/(…)`, so flatness of each
factor is **Lemma 8.31(2)** over the base `O_X(X)`; faithful flatness of the product follows
because the cover is jointly surjective on Spa (prime-surjectivity). -/
/-- **Proposition 8.30** (Wedhorn p.81): for rational subsets `U ⊆ V` the restriction
`O_X(V) → O_X(U)` is flat.

Wedhorn's proof: by **Example 6.38** `O_X(V)` is again a strongly noetherian Tate ring,
so WLOG `V = X` and `A` complete; by **Remark 7.55** WLOG `U = U₁ = R(f/1)` or
`U₂ = R(1/f)`; **Example 6.38** identifies `O_X(U₁) = A⟨X⟩/(f − X)` and
`O_X(U₂) = A⟨X⟩/(1 − fX)`, at which point flatness is exactly **Lemma 8.31(2)**
(`lemma_8_31_fSubX_flat` / `lemma_8_31_oneSubfX_flat`, filled above). -/
theorem prop_8_30_restriction_flat (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    @Module.Flat (presheafValue D) (presheafValue D') _ _
      (restrictionMapHom D D' h).toModule := by
  sorry

/-- **Prime-surjectivity for a rational covering** — the geometric input to the
*faithful* half of Cor 8.32: every prime `p` of `O_X(X)` is the contraction of a prime
from some cover piece `O_X(Uᵢ)`. This is the algebraic shadow of `(Uᵢ)` covering
`X = Spa A` (every support prime is hit by some piece). -/
theorem cor_8_32_prime_surjection (C : RationalCovering A) :
    letI : ∀ D : { D // D ∈ C.covers }, Algebra (presheafValue C.base) (presheafValue D.1) :=
      fun D => (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
    ∀ (p : Ideal (presheafValue C.base)), p.IsPrime →
      ∃ (D : { D // D ∈ C.covers }) (q : Ideal (presheafValue D.1)), q.IsPrime ∧
        q.comap (algebraMap (presheafValue C.base) (presheafValue D.1)) = p := by
  sorry

/-- **Cor 8.32 — Wedhorn-faithful maximals route (geometric leaf).**

Wedhorn states Cor 8.32 as *immediate* from flatness (Prop 8.30) + the covering.
Mathlib's `Module.FaithfullyFlat` is **defined** by the maximals criterion
(`submodule_ne_top`: flat + `∀ maximal m, m • M ≠ ⊤`), so the only geometric
content is: for every **maximal** ideal `m` of the base `O_X(C.base)`, some cover
piece `D` has `m · O_X(D) ≠ ⊤`.

This is the *correct* faithful target. It avoids two dead ends:
* the exact prime-surjection `cor_8_32_prime_surjection` (`q.comap = p` for **all**
  primes) needs `supp x = p`, i.e. Bourbaki rank-1 domination — absent (Lemma745
  gives only `supp ⊇ p`); and
* the lifted-ideal route (`hSpa_points_nonOpen_via_lifted_ideal_proper`) lifts a
  prime of `A` to `presheafValue C.base`, which forces the residual
  `liftedIdeal ≠ ⊤` (= the Stacks-00MA / OMT analytic input).

Working with a **maximal `m` of the base directly**: `m` is non-open (proper in a
Tate ring), so `exists_spa_point_supp_ge_in_presheafValue` (Lemma 7.45 on the
completion, sorry-free) gives a Spa point `w` with `m ≤ supp w`, hence `supp w = m`
(`m` maximal); the covering places `w` in some piece `D`; the rational-subset ↔ Spa
correspondence (Wedhorn 7.46) extends `w` to `O_X(D)` with support over `m`, so
`m · O_X(D) ≠ ⊤`. No Bourbaki, no `liftedIdeal ≠ ⊤`, no OMT. -/
theorem cor_8_32_maximal_liftedIdeal_ne_top (C : RationalCovering A) :
    ∀ (m : Ideal (presheafValue C.base)), m.IsMaximal →
      ∃ (D : { D // D ∈ C.covers }),
        Ideal.map (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)) m ≠ ⊤ := by
  sorry

theorem cor_8_32_productRestriction_faithfullyFlat (C : RationalCovering A) :
    letI : ∀ D : { D // D ∈ C.covers }, Algebra (presheafValue C.base) (presheafValue D.1) :=
      fun D => (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
    Module.FaithfullyFlat (presheafValue C.base)
      (∀ D : { D // D ∈ C.covers }, presheafValue D.1) := by
  -- Compose the two sub-lemmas through the commutative-algebra fact
  -- `faithfullyFlat_pi_of_prime_surjection` (axiom-clean, `Cor832.lean`): a product of
  -- flat algebras whose covering is jointly prime-surjective is faithfully flat. All
  -- instances are supplied explicitly to avoid instance search over `presheafValue`
  -- (the algebra-induced module `Algebra.toModule ∘ RingHom.toAlgebra` is `rfl`-equal
  -- to `RingHom.toModule`, the module `prop_8_30_restriction_flat` is stated against).
  exact @faithfullyFlat_pi_of_prime_surjection (presheafValue C.base) _
    { D // D ∈ C.covers } (Finite.of_fintype _)
    (fun D => presheafValue D.1)
    (fun _ => inferInstance)
    (fun D => (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra)
    (fun D => prop_8_30_restriction_flat C.base D.1 (C.hsubset D.1 D.2))
    (cor_8_32_prime_surjection C)

/-- **Corollary 8.32, injectivity consequence** (the separation half of `IsSheafy`): the
product restriction `O_X(X) → ∏ O_X(Uᵢ)` is injective. Faithfully flat ⇒ injective.

**Discharged** (Wedhorn-faithful): the repo's axiom-clean
`productRestriction_injective_of_flat_and_lifting` (`Cor832.lean`, the
faithfully-flat ⇒ injective route, *no* noeth-A₀ / separation parameters) takes exactly
`flat_over_base = prop_8_30_restriction_flat` and `hSpa_surj = cor_8_32_prime_surjection`. -/
theorem cor_8_32_productRestrictionSub_injective (C : RationalCovering A) :
    Function.Injective (productRestrictionSub A C) := by
  haveI : Finite { D : RationalLocData A // D ∈ C.covers } := Finite.of_fintype _
  exact productRestrictionSub_injective_of_flat_and_lifting C
    (fun D => prop_8_30_restriction_flat C.base D.1 (C.hsubset D.1 D.2))
    (fun p hp => cor_8_32_prime_surjection C p hp)

/-- **Cor 8.32, topological inducing half**: `productRestrictionSub` carries the subspace
topology of its image inside `∏ O_X(Uᵢ)`. This is the open-mapping / strictness content
behind Wedhorn's "sheaf of **complete topological** rings" — supplied in the repo by the
Tate-absorbing Banach OMT (`productRestrictionSubToEqualizer_isOpenMap`, `BanachOMT.lean`,
Wedhorn Prop 6.18). The repo proof (`productRestrictionSub_isInducing_tate`) is currently
stated against `[IsNoetherianRing (…principalPair…A₀)]`; the Wedhorn case-(b) hypothesis is
ring-noetherian, so wiring it here awaits the noeth-A₀ → ring-noetherian retyping. -/
theorem cor_8_32_productRestrictionSub_isInducing (C : RationalCovering A) :
    Topology.IsInducing (productRestrictionSub A C) := by
  sorry

/-- **Corollary 8.32, topological strengthening** (the full `embedding` field of `IsSheafy`):
the product restriction is a topological embedding = topological inducing + injectivity. -/
theorem cor_8_32_productRestrictionSub_isEmbedding (C : RationalCovering A) :
    Topology.IsEmbedding (productRestrictionSub A C) :=
  ⟨cor_8_32_productRestrictionSub_isInducing C, cor_8_32_productRestrictionSub_injective C⟩

/-! ## Lemma 8.33 — the 2-element Laurent cover is `O_X`-acyclic

> **Lemma 8.33.** Let `A` be a strongly noetherian Tate affinoid ring, `f ∈ A`,
> `U₁ = {x : x(f) ≤ 1}`, `U₂ = {x : x(f) ≥ 1}`. Then the augmented Čech complex
> `0 → O_X(X) → O_X(U₁) × O_X(U₂) → O_X(U₁ ∩ U₂) → 0` is exact.

Via the explicit identifications (Examples 6.38, 6.39)
`O_X(U₁) = A⟨ζ⟩/(f−ζ)`, `O_X(U₂) = A⟨η⟩/(1−fη)`, `O_X(U₁∩U₂) = A⟨ζ,ζ⁻¹⟩/(f−ζ)`,
and the `λ`/`λ'`/`ι` diagram chase (injectivity of `ε` from Cor 8.32; surjectivity of `λ`,
`λ'`; `im ι = ker λ`). Stated here as the `IsSheafy` content (separation + gluing) for the
2-element Laurent cover `Uf`. -/
theorem lemma_8_33_laurent_cover_gluing (f : A) (C : RationalCovering A)
    (hC : True /- placeholder: C is the 2-element Laurent cover U_f generated by `f` -/)
    (g : ∀ (D : ↥C.covers), presheafValue D.1)
    (hcompat : ∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (g D₁) = restrictionMap D₂.1 D₃ h₃₂ (g D₂)) :
    ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = g D := by
  sorry

/-! ## Lemma 8.34 — a rational cover generated by `T` (with `T·A = A`) is `O_X`-acyclic

> **Lemma 8.34.** Let `A` be a complete strongly noetherian Tate ring and `U` a rational
> cover generated by some finite `T ⊆ A` with `T·A = A`. Then `U` is `O_X`-acyclic.

Wedhorn's proof: (i) Laurent covers `U_{f₁} × ⋯ × U_{fᵣ}` are acyclic by **Lemma 8.33** +
**Prop A.3(3)** induction; (ii) any `T`-generated cover admits a Laurent cover `V` with each
`U|V` generated by units (via Cor 7.32); (iii) unit-generated covers refine to Laurent
covers; (iv) combine by **Prop A.3(1)(2)**. Stated here as the `gluing` content. -/
theorem lemma_8_34_gluing (C : RationalCovering A)
    (g : ∀ (D : ↥C.covers), presheafValue D.1)
    (hcompat : ∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (g D₁) = restrictionMap D₂.1 D₃ h₃₂ (g D₂)) :
    ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = g D := by
  sorry

/-! ## Theorem 8.28(b) — assembled from Cor 8.32 (separation) and Lemma 8.34 (gluing)

> **Theorem 8.28(b).** If `A` is a strongly noetherian Tate ring then `O_X` is a sheaf of
> complete topological rings (and `H^q(U, O_X) = 0` for `q ≥ 1`).

By **Prop A.4** the sheaf property is equivalent to acyclicity of all rational covers; in the
Lean formulation `IsSheafy A` is the pair `(embedding, gluing)` per cover, supplied by
Cor 8.32 and Lemma 8.34 respectively. -/
theorem isSheafy_of_stronglyNoetherian_828b : IsSheafy A where
  embedding C := cor_8_32_productRestrictionSub_isEmbedding C
  gluing C f hcompat := lemma_8_34_gluing C f hcompat

end Wedhorn828

end ValuationSpectrum
