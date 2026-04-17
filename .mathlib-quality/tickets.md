# Ticket Board — Close Completion Ideal Properness Claim

## Summary
- Total: 4 tickets.
- Open: 4 | In Progress: 0 | Done: 0.
- See `plan.md` for strategy.

## Tickets

### [T-IDEAL-1] Approximation lemma for coeRingHom
- **Status**: open
- **File**: new section in `Adic spaces/Cor832.lean` or new file.
- **Depends on**: none (uses existing completion infrastructure).
- **Parallel**: yes.
- **Description**: Prove that if `1 ∈ Ideal.map D.coeRingHom q`, then there's a sequence in `q` converging to `1` in `Loc.Away D.s`. Uses density of `coeRingHom`'s image + uniform-inducing property.
- **Est. lines**: 60-100.
- **Proof approach**: 
  - From `1 = Σᵢ aᵢ · coeRingHom(bᵢ)` with `bᵢ ∈ q`.
  - For each aᵢ, use density to approximate `aᵢ,ₙ = coeRingHom(αᵢ,ₙ) + εᵢ,ₙ` with `εᵢ,ₙ → 0`.
  - Build `xₙ := Σᵢ αᵢ,ₙ · bᵢ ∈ q`.
  - Show `coeRingHom(xₙ) → 1` in `presheafValue`, hence `xₙ → 1` in `Loc.Away` by uniform-inducing.

### [T-IDEAL-2] `Ideal.map algebraMap p` closed in `Loc.Away s`
- **Status**: open
- **File**: new section or new file.
- **Depends on**: none.
- **Parallel**: yes.
- **Description**: For `p` prime of A with `s ∉ p`, show `Ideal.map (algebraMap A (Loc.Away s)) p` is closed in `Loc.Away s` with its Huber topology.
- **Est. lines**: 80-120.
- **Proof approach**:
  - Show quotient `Loc.Away s / Ideal.map algebraMap p ≃ (A/p)_s`.
  - Since `A/p` is a domain and `s̄ ≠ 0`, `(A/p)_s` is a domain.
  - For a ring with T₂ quotient topology, ideals are closed (standard).
  - Alternatively: use Wedhorn Prop 6.17 on A (complete, noetherian), get p closed. Then argue algebraMap is "close" to closed-map preserving.

### [T-IDEAL-3] Combined: `Ideal.map coeRingHom q ≠ ⊤` for q from prime of A
- **Status**: open
- **File**: `Cor832.lean`.
- **Depends on**: T-IDEAL-1, T-IDEAL-2.
- **Parallel**: no.
- **Description**: Combine T-IDEAL-1 (approximation) with T-IDEAL-2 (closedness) to show: for `p : Ideal A` prime with `D.s ∉ p`, `Ideal.map D.coeRingHom (Ideal.map algebraMap p) ≠ ⊤`.
- **Est. lines**: 50-80.
- **Result**: Discharges the residual hypothesis `coeRingHom preserves proper ideals` for ideals of the specific form `Ideal.map algebraMap p`.

### [T-IDEAL-FINAL] Plug into Cor 8.32 chain and close tateAcyclicity Part 1
- **Status**: open
- **File**: `Cor832.lean`, `LaurentRefinement.lean`.
- **Depends on**: T-IDEAL-3.
- **Parallel**: no.
- **Description**: Use T-IDEAL-3 to produce unconditional `productRestriction_injective_tate_clean`. Then replace `tateAcyclicity` Part 1's use of `restrictionMapHom_injective` with the new unconditional closer.
- **Est. lines**: 30-50.
- **Result**: `tateAcyclicity` Part 1 UNCONDITIONALLY CLOSED. Major milestone.

## Execution

Phase A (parallel): T-IDEAL-1 + T-IDEAL-2 (independent).
Phase B (serial): T-IDEAL-3 → T-IDEAL-FINAL.

Total: ~220-350 lines. Single session feasible if T-IDEAL-2 works cleanly.

## Risk

**T-IDEAL-2 is the crux**. If closedness of `Ideal.map algebraMap p` in `Loc.Away s` requires deeper analytical infrastructure (e.g., Huber topology Hausdorffness specifically), we may need to:
- Use Wedhorn Prop 6.17 on A (already proved) + a closedness-preservation result.
- Or: use a completely different approach via `Ideal.map coeRingHom` on `presheafValue` using completeness there.
