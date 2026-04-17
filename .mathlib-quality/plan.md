# Development Plan: Close the Completion Ideal Properness Claim

**Target residual** (the last blocker for `tateAcyclicity` Part 1):
```lean
∀ (q : Ideal (Localization.Away C.base.s)), q ≠ ⊤ →
  Ideal.map C.base.coeRingHom q ≠ (⊤ : Ideal (presheafValue C.base))
```

## Mathematical strategy

**Core argument (approximation + closedness)**:

Suppose `1 ∈ Ideal.map coeRingHom q` in `presheafValue C.base`. Then:
`1 = Σᵢ aᵢ · coeRingHom(bᵢ)` for some finite k, `aᵢ ∈ presheafValue`, `bᵢ ∈ q`.

By density of `coeRingHom`'s image (completion), each `aᵢ = lim aᵢ,ₙ` with `aᵢ,ₙ ∈ coeRingHom(Loc.Away s)`.
So `aᵢ ≈ coeRingHom(αᵢ,ₙ) + εᵢ,ₙ` where `εᵢ,ₙ → 0`.

Substituting:
```
1 - coeRingHom(Σᵢ αᵢ,ₙ · bᵢ) = Σᵢ εᵢ,ₙ · coeRingHom(bᵢ) → 0.
```

By `coeRingHom`'s uniform-inducing property, `Σᵢ αᵢ,ₙ · bᵢ → 1` in `Loc.Away s`.

Each `Σᵢ αᵢ,ₙ · bᵢ ∈ q` (since `bᵢ ∈ q`, ideal closed under linear combinations).

**If `q` is closed in `Loc.Away s`**, then `1 ∈ q`, contradicting `q ≠ ⊤`.

So the missing ingredient is: **any proper ideal of `Loc.Away C.base.s` is closed** in the Huber localization topology.

## Wedhorn content

**Wedhorn Prop 6.17** (p. 50 of 1910.05934v1.pdf): Let `A` be a complete Tate ring and `M` a complete topological `A`-module with a countable fundamental system of open neighborhoods of `0`. Then `M` is noetherian if and only if every submodule of `M` is closed.

Already formalized as `Wedhorn.isClosed_ideal_of_noetherian` in `NoetherianTateModules.lean:383`, but it requires **CompleteSpace** — which `Loc.Away s` does NOT have (only its completion `presheafValue` does).

**Our workaround**: argue at the COMPLETION level.

## Revised strategy

Transfer everything to the completion:

1. Lift `q` to `q̄ := Ideal.map coeRingHom q` in `presheafValue`.
2. `q̄` is closed in `presheafValue` (by Wedhorn Prop 6.17 on `presheafValue`, which IS complete).
3. Show `q̄ ≠ ⊤`.

But this is circular — we want `q̄ ≠ ⊤` precisely.

## Alternative: closedness of `q` in `Loc.Away s` via embedding

Use that `Loc.Away s` embeds into `presheafValue` via `coeRingHom`, and `coeRingHom⁻¹(q̄)` is closed (preimage of closed under continuous). If `coeRingHom⁻¹(q̄) = q`, then `q` is closed.

`coeRingHom⁻¹(q̄)` = `{x ∈ Loc.Away s | coeRingHom x ∈ Ideal.map coeRingHom q}`. This contains `q` but is not obviously equal.

For the equality `coeRingHom⁻¹(q̄) = q`, we need: `coeRingHom x ∈ Ideal.map coeRingHom q ⇒ x ∈ q`. This is essentially injectivity of the map `Loc.Away s/q → presheafValue/q̄`.

Hmm, this is yet another "faithful flatness" claim.

## Cleanest path: use Krull intersection + topological closure

**Key insight**: `presheafValue C.base`'s topology restricts to `Loc.Away C.base.s`'s topology (via `coeRingHom` being uniform inducing). So `q̄ ∩ coeRingHom(Loc.Away s)` in `presheafValue` pulls back to... hmm.

Actually there's a cleaner route via:

### Approach: Use the Wedhorn Prop 6.17 directly on `presheafValue`.

**Setup**:
1. `presheafValue C.base` is a Tate ring (proved: `presheafValue_isTateRing`).
2. `presheafValue C.base` with its pair `presheafValue_pairOfDefinition_concrete` has noetherian `A₀` (requires `[IsNoetherianRing (locSubring ...)]`, which we have).
3. Apply `Wedhorn.isClosed_ideal_of_noetherian` to `presheafValue C.base` with `P := presheafValue_pairOfDefinition_concrete`.
4. Conclude: every ideal of `presheafValue C.base` is CLOSED.

This includes `Ideal.map coeRingHom q`. Closed ideal that contains `1`? Only if it equals `⊤`. So closedness doesn't directly prove it's ≠ ⊤.

**Hmm same issue.**

## The REAL route: `coeRingHom` is injective + q closed in Loc.Away

**Actually we don't need q closed in Loc.Away s**. We need the step:

> `coeRingHom(x_n) → 1 ⇒ x_n → 1` in `Loc.Away s`.

This IS uniform inducing. Then `x_n → 1` with each `x_n ∈ q` gives `1 ∈ closure(q)`. If `q` is closed, `1 ∈ q`, contradiction.

So we DO need `q` closed in `Loc.Away s`. But `Loc.Away s` isn't complete.

**Wedhorn Prop 6.17 for non-complete Tate rings?** The standard statement requires completeness. But for SPECIFIC ideals arising from `Ideal.map algebraMap p` (with `p` closed in A), closedness DOES hold.

### Direct argument

**Claim**: `Ideal.map (algebraMap A (Loc.Away s)) p` is CLOSED in `Loc.Away s` for any prime `p` of A with `s ∉ p`.

**Proof**:
1. By Wedhorn Prop 6.17 on A (complete Tate, noetherian): `p` is closed in `A`.
2. `algebraMap A (Loc.Away s)` is continuous (by definition of `algebraMap_continuous_loc`).
3. `Loc.Away s / Ideal.map algebraMap p ≃ (A/p)[1/s]` (first isomorphism theorem).
4. `(A/p)[1/s]` is a localization of `A/p`, which is a domain (p prime). So T₂.
5. Ideals with T₂ quotients are closed.

This is the direct argument! Let me flesh out the plan.

## Plan

### [T-IDEAL-1] Prove `Ideal.map algebraMap_loc p` is closed in `Loc.Away s`

For `p : Ideal A` prime (no Huber hypothesis needed), the extension `Ideal.map (algebraMap A (Loc.Away s)) p` is closed in `Loc.Away s` (with its loc topology) iff the quotient `Loc.Away s / Ideal.map algebraMap p` is T₂ as a topological ring.

For `p` prime, the quotient is `Frac(A/p) × Frac(A/p)⁻¹[s]`-ish structure. T₂ follows from general ring-theoretic facts.

**Alternative (cleaner)**: use that closed ideals correspond to Hausdorff quotients, and quotients of T₂ noetherian rings are T₂ iff the ideal is closed.

Actually we may use a more direct approach:

```
Ideal.map coeRingHom q = closure (coeRingHom '' q)
```

In a uniform space, the map `coeRingHom : Loc.Away → presheafValue` extends to an ISOMETRIC EMBEDDING (for the completion). The image of a closed set under an embedding is closed in the image's topology (which equals the subspace topology). Then the ideal generated by this image in the completion is... hmm, not necessarily the closure.

### [T-IDEAL-2] Direct proof: `Ideal.map coeRingHom q = ⊤ → q = ⊤`.

Using approximation + closedness. Structure:

```lean
theorem map_coeRingHom_ne_top (D : RationalLocData A)
    [IsNoetherianRing (locSubring D.P D.T D.s)]
    -- ... other Tate hypotheses
    {q : Ideal (Localization.Away D.s)} (hq_ne : q ≠ ⊤)
    (hq_closed : IsClosed (q : Set (Localization.Away D.s))) :
  Ideal.map D.coeRingHom q ≠ ⊤
```

Proof:
1. Suppose `1 ∈ Ideal.map coeRingHom q`.
2. `1 = Σᵢ aᵢ · coeRingHom(bᵢ)` for `aᵢ ∈ presheafValue D`, `bᵢ ∈ q` (finitely many).
3. Approximate `aᵢ → coeRingHom(αᵢ)` via density.
4. Show `Σᵢ αᵢ · bᵢ → 1` in `Loc.Away s` via uniform-inducing.
5. Each `Σᵢ αᵢ · bᵢ ∈ q`. By closedness, `1 ∈ q`, contradicting `q ≠ ⊤`.

### [T-IDEAL-3] Instantiate for our specific q

Our q in the Cor 8.32 chain is `Ideal.map (algebraMap A (Loc.Away C.base.s)) p` for p prime of A with C.base.s ∉ p.

Show q ≠ ⊤ (immediate from p ≠ ⊤, localization doesn't collapse proper ideals when s ∉ p).

Show q closed in `Loc.Away s`:
- Quotient `Loc.Away s / q ≃ (A/p)[1/s̄]` where `s̄` is image of s.
- `(A/p)[1/s̄]` is a localization of the integral domain `A/p`, hence embeds into `Frac(A/p)`.
- T₂ since the ring is an integral domain with the induced topology... need to check.

Actually for T₂ we need the specific topology to be Hausdorff. The Huber topology might not make the quotient T₂ directly.

**Simpler approach**: use Wedhorn Prop 6.17 on A itself to show p closed in A. Then use that `algebraMap` preserves closed ideals under some hypotheses.

**Cleanest**: transfer the closedness claim to A using noetherian structure.

## Tickets

### [T-IDEAL-1] Approximation lemma for coeRingHom

Setup + approximation statement:
```lean
theorem one_mem_map_implies_limit
    (D : RationalLocData A)
    (q : Ideal (Localization.Away D.s))
    (h : (1 : presheafValue D) ∈ Ideal.map D.coeRingHom q) :
  ∃ (x : ℕ → Localization.Away D.s),
    (∀ n, x n ∈ q) ∧ Filter.Tendsto x Filter.atTop (nhds 1)
```

Uses density + uniform inducing. Estimated 60-100 lines.

### [T-IDEAL-2] Closed ideals in Loc.Away via noetherian structure

Specifically for ideals of the form `Ideal.map algebraMap p`:
```lean
theorem isClosed_ideal_map_algebraMap_of_prime
    (p : Ideal A) [hp : p.IsPrime] (s : A) (hs : s ∉ p) :
  IsClosed (Ideal.map (algebraMap A (Localization.Away s)) p : 
            Set (Localization.Away s))
```

Uses `A/p` being a domain and the quotient structure. Estimated 80-120 lines.

### [T-IDEAL-3] Combine: `Ideal.map coeRingHom (Ideal.map algebraMap p) ≠ ⊤`

Composition of T-IDEAL-1 + T-IDEAL-2. Unconditional closure of T-IDEAL-PROPER residual. Estimated 50-80 lines.

### [T-IDEAL-FINAL] Plug into productRestriction_injective_tate and close tateAcyclicity Part 1

Replace the conditional `productRestriction_injective_tate_via_coeRingHom_preserves_proper` with an unconditional theorem. Then reroute tateAcyclicity Part 1. Estimated 30-50 lines.

## Total estimate

~300-400 lines. Single session feasible IF approach works.

## Risk

- T-IDEAL-2 (closedness of `Ideal.map algebraMap p`): may require more analytical infrastructure than anticipated. Specifically, the T₂ topology on the quotient depends on specific structure of Loc.Away s's topology.

Fallback: use a different route (e.g., Wedhorn 6.17 on presheafValue applied to `Ideal.map coeRingHom q`, giving closedness, then arguing `⊤` can't be the lift of proper ideal via the flatness we have).

## References

- Wedhorn Prop 6.17 (closed ideals in complete noetherian Tate rings): p. 50.
- Krull intersection theorem: Mathlib.RingTheory.Ideal.Maximal.
- Uniform completion: Mathlib.Topology.UniformSpace.Completion.
