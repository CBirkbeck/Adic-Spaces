/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornLocalizedArchimedeanTransfer

/-!
# Value-group strictMono hom audit + corrected target signature

The genuine remaining piece for the MulArchimedean transfer
(`WedhornLocalizedArchimedeanTransfer.lean`, commit `fa682a5`):
constructing the strictly monotonic monoid homomorphism

```
ValueGroupWithZero (Localization.Away s) →* ValueGroupWithZero A
```

(in the `Localization → A` direction) needed by
`mulArchimedean_localization_comap_via_strictMono_hom`.

## Audit finding

Mathlib provides `ValuativeExtension.mapValueGroupWithZero A B`
(`Mathlib.RingTheory.Valuation.ValuativeRel.Basic:1237`):

```
def mapValueGroupWithZero : ValueGroupWithZero A →*₀ ValueGroupWithZero B
```

This goes the **OPPOSITE direction** to what we need (`A → B` instead
of `B → A`). It's strictly monotonic
(`mapValueGroupWithZero_strictMono`).

`MulArchimedean.comap (f : G →* M) (hf : StrictMono f) [MulArchimedean M]
: MulArchimedean G` requires the homomorphism to go `G → M` with
`M` Archimedean. With `G = ValueGroupWithZero B` (target — we want
this Archimedean) and `M = ValueGroupWithZero A` (source — given
Archimedean), we need `f : VG(B) → VG(A)`. Mathlib's map is `VG(A) → VG(B)`.

**Resolution**: for `B = Localization.Away s` with `w(s) ≠ 0`, the
Mathlib map `mapValueGroupWithZero A B` is BIJECTIVE (every `[b]_B` for
`b = a/s^k` equals `mapValueGroupWithZero ([a]_A · [s]_A^(-k))`,
well-defined since `[s]_A ≠ 0`). Taking the inverse gives the desired
`B → A` direction.

## Corrected target signature

The single remaining residual is now precisely:

```lean
theorem mapValueGroupWithZero_bijective_of_localization
    {A : Type*} [CommRing A] (s : A)
    (w : Spv (Localization.Away s))
    (hws : ¬ w.vle (algebraMap A (Localization.Away s) s) 0) :
    letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
    letI : ValuativeRel A :=
      (comap (algebraMap A (Localization.Away s)) w).toValuativeRel
    Function.Bijective
      (ValuativeExtension.mapValueGroupWithZero A (Localization.Away s))
```

Mathematical content:

* **Surjectivity**: every `b ∈ Localization.Away s = a/s^k` has class
  `[b]_B`. We compute:
  `[b]_B = [a]_B · [s]_B^(-k)`
  `      = mapValueGroupWithZero ([a]_A) · mapValueGroupWithZero ([s]_A)^(-k)`
  `      = mapValueGroupWithZero ([a]_A · [s]_A^(-k))`
  (well-defined since `[s]_A ≠ 0` in `ValueGroupWithZero A` — derived
  from `hws` via `comap_vle`).

* **Injectivity**: follows from `mapValueGroupWithZero_strictMono`
  (a strictly monotonic function is injective).

## Composition with the existing reducer

Once `mapValueGroupWithZero_bijective_of_localization` lands, the chain
to `mulArchimedean_localization_comap_via_strictMono_hom` is:

1. From bijectivity, build a `MulEquiv₀` from `ValueGroupWithZero A`
   to `ValueGroupWithZero (Localization.Away s)` (via
   `MonoidWithZeroHom.toMulEquiv` plus the bijectivity hypothesis).
2. Take `.symm` to get the inverse `ValueGroupWithZero (Localization.Away s)
   →*₀ ValueGroupWithZero A`.
3. Strict monotonicity of the inverse follows from strict monotonicity
   of `mapValueGroupWithZero` plus bijectivity (an order-preserving
   bijection has an order-preserving inverse).
4. Apply `MulArchimedean.comap` (the inverse + strict mono).

## Why this file does NOT prove the residual

The bijectivity proof requires:
* The well-definedness verification of the surjective formula
  `[a]_A · [s]_A^(-k) ↦ [b]_B` (independent of the `(a, k)`
  decomposition of `b`).
* The `[s]_A ≠ 0` derivation from `hws`.

Both require careful manipulation of the `ValueGroupWithZero` quotient
construction (`Mathlib.RingTheory.Valuation.ValuativeRel.Basic:340`).
This is the next concrete sub-target.

The companion structural lemmas needed (likely Mathlib already, but
needs excavation):
* `MulEquiv.symm_strictMono` (or `OrderMulEquiv` properties).
* `MonoidWithZeroHom.bijective_iff_isMulEquiv`.

## Notes

* No root import; leaf-level file.
* No sorries.
* No edits to committed bridge files or Secondary's
  branch-compatibility files.
* No Lane B / Cor 8.32 / Jacobson / T001 / faithful-flatness /
  final-acyclicity content. -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-! ## Surjectivity residual (with explicit witness formula)

The single remaining piece for the full chain to `MulArchimedean` transfer:

```lean
theorem mapValueGroupWithZero_surjective_of_localization
    {A : Type*} [CommRing A] (s : A)
    (w : Spv (Localization.Away s))
    (hws : ¬ w.vle (algebraMap A (Localization.Away s) s) 0) :
    letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
    letI : ValuativeRel A :=
      (comap (algebraMap A (Localization.Away s)) w).toValuativeRel
    Function.Surjective
      (ValuativeExtension.mapValueGroupWithZero A (Localization.Away s))
```

### Proof outline (with explicit witness)

Take `[b]_B ∈ ValueGroupWithZero (Localization.Away s)`. By
`ValueGroupWithZero.ind`, `[b]_B = ValueGroupWithZero.mk b₁ b₂` for
some `b₁ ∈ Localization.Away s` and `b₂ ∈ posSubmonoid (Localization.Away s)`
(i.e., `0 <ᵥ b₂` under `w.toValuativeRel`).

By `IsLocalization.surj` (Mathlib):
* `∃ a₁ ∈ A, k₁ : ℕ, b₁ * (algebraMap s)^k₁ = algebraMap a₁`.
* `∃ a₂ ∈ A, k₂ : ℕ, b₂ * (algebraMap s)^k₂ = algebraMap a₂`.

(With `a₂ ∈ A` having `0 <ᵥ algebraMap a₂` in B, hence `0 <ᵥ a₂` in A
under `comap w`'s ValuativeRel — so `a₂ ∈ posSubmonoid A`.)

The **explicit witness** for surjectivity:
* `a := a₁ * s^k₂ ∈ A`.
* `c := a₂ * s^k₁` with `c ∈ posSubmonoid A` (since `a₂ ∈ posSubmonoid A`
  by above and `s^k₁ ∈ posSubmonoid A` from `hws` via `comap`).

Computation:
* `algebraMap a · b₂ = algebraMap (a₁ * s^k₂) · b₂ = algebraMap a₁ ·
  algebraMap s^k₂ · b₂ = algebraMap a₁ · algebraMap a₂ = algebraMap (a₁ * a₂)`.
* `b₁ · algebraMap c = b₁ · algebraMap (a₂ * s^k₁) = b₁ · algebraMap s^k₁ ·
  algebraMap a₂ = algebraMap a₁ · algebraMap a₂ = algebraMap (a₁ * a₂)`.

Both equal `algebraMap (a₁ * a₂)`, so `mk (algebraMap a) (mapPosSubmonoid c) =
mk b₁ b₂` by `ValueGroupWithZero.mk_eq_mk` (via `vle_refl` from equal
representatives). Then `mapValueGroupWithZero_mk` gives
`mapValueGroupWithZero (mk a c) = mk (algebraMap a) (mapPosSubmonoid c) = mk b₁ b₂`. ✓

### Why this file does NOT prove the residual directly

The proof requires:
* Careful manipulation of `IsLocalization.surj` to extract `(a₁, k₁)` and
  `(a₂, k₂)` from `b₁` and `b₂`.
* `posSubmonoid A` membership for `c = a₂ * s^k₁` (combining `a₂ ∈
  posSubmonoid A` with `s^k₁ ∈ posSubmonoid A` from `hws`).
* `ValueGroupWithZero.sound` application with the equality of representatives.

This is multi-step Mathlib-level manipulation. The next concrete sub-target
is the surjectivity proof above, which when combined with
`mapValueGroupWithZero_strictMono` and `strictMonoHom_inverse_of_bijective`
(below) closes the full chain to `MulArchimedean.comap` and thence
`hArch_loc`. -/

/-- **Strict-mono hom `VG(B) →* VG(A)` from a strict-mono surjection
the OTHER way**.

Given a strictly monotonic surjective monoid hom `g : VG(A) →*
VG(B)` (the typical localization case), construct a strictly monotonic
monoid hom `f : VG(B) →* VG(A)` going the opposite direction.

**Construction**: under the strict mono surjection `g`, `g` is
bijective (strict mono ⟹ inj; surj by hypothesis), so `g.toEquiv` has
an inverse. The inverse is monoid-multiplicative (since `g` is) and
strictly monotonic (since `g` is, and the inverse of a strict mono
bijection is strict mono).

**Use case**: combined with the residual
`mapValueGroupWithZero_bijective_of_localization` (documented above),
this produces the `B → A` strict-mono hom needed for
`mulArchimedean_localization_comap_via_strictMono_hom`.

**Status**: this is structural infrastructure — should exist in
Mathlib in some form; if not, this is a clean self-contained
construction. -/
theorem strictMonoHom_inverse_of_bijective
    {G H : Type*} [LinearOrder G] [LinearOrder H]
    [CommMonoid G] [CommMonoid H]
    (g : G →* H) (hg_strictMono : StrictMono g)
    (hg_surj : Function.Surjective g) :
    ∃ f : H →* G, StrictMono f := by
  have hg_bij : Function.Bijective g := ⟨hg_strictMono.injective, hg_surj⟩
  -- Inverse function via Function.invFun (avoids Equiv coercion issues).
  let invFn : H → G := Function.invFun g
  have hinv_left : ∀ x : H, g (invFn x) = x := fun x =>
    Function.rightInverse_invFun hg_surj x
  have hinv_mul : ∀ x y : H, invFn (x * y) = invFn x * invFn y := by
    intro x y
    apply hg_strictMono.injective
    rw [hinv_left, g.map_mul, hinv_left, hinv_left]
  have hinv_one : invFn 1 = 1 := by
    apply hg_strictMono.injective
    rw [hinv_left, g.map_one]
  refine ⟨{ toFun := invFn, map_one' := hinv_one, map_mul' := hinv_mul }, ?_⟩
  intro x y hxy
  show invFn x < invFn y
  by_contra h_not
  push_neg at h_not
  have h_g_le := hg_strictMono.monotone h_not
  rw [hinv_left, hinv_left] at h_g_le
  exact absurd h_g_le (not_le.mpr hxy)

end ValuationSpectrum
