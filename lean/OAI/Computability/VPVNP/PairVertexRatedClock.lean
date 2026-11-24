import OAI.Computability.VPVNP.PairVertexSelectedClock
import OAI.Computability.VPVNP.PairVertexOrdinalLiveCosts
import OAI.Computability.VPVNP.LiveVirtualPairCursorBoundary

/-! # A single length threshold for the native selected root and its jobs -/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM Compression CompressorRecords CursorNetwork CursorBounds Filter LiveProgram
open PairSimulation VertexImage NativeOperands

set_option exponentiation.threshold 10000 in
/-- The native geometry, cache initialization and active DFS clock estimates
hold simultaneously before the coefficient realization or branch is chosen.
Each job receives the same private allowance as in the measured ordinal row. -/
theorem eventually_rated_root_clock {K : Type*} [_root_.Field K] {S : BlockSchedule K}
    (D : FixedProgramDiagonal.Program) (B : S.Templates) (u : PairExponents B.growthConstant)
    (haddr : max S.laneBits 5 ≤ D.addressFactor) (C : ℕ) :
    ∀ᶠ n : ℕ in atTop, 2048 ≤ n ∧ S.baseDegree ≤ n ∧ Fintype.card B.Entry ≤ n ∧
      (∀ t ≤ work (NativeCache.args D.constants) D.numerator D.denominator (D.geometry n)+76,
        t+slotDegree S+187 ≤ 44+n^3) ∧
      ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn C) (A : Type*) [CommRing A]
        (f : B.Entry → A) (ok : B.IsSolution f),
        let X := V.scanState
        let T := blockCount (u.θ : ℝ) n
        let E := B.execute f ok T le_rfl X
        B.growthConstant^T ≤ n ∧ ∀ z : E.Choices,
          let Y := E.finalState z
          let chain := E.termChain (B.records f ok T le_rfl X) z
          Y.maxWireWidth ≤ n ∧ ∀ v : Y.network.Site,
            chain.occurrences (fun _ => 1) v ≤ n ∧
            ∀ (half : Y.network.Half v) t,
              t ≤ work (NativeCache.args D.constants) D.numerator D.denominator (D.geometry n)+76 →
              t+slotDegree S+187+(15+21*S.baseDegree+5*(NodeArguments.packed Y v half).length)+
                (15+n^43)*chain.occurrences (fun _ => 1) v+7*Fintype.card B.Entry+46 ≤ n^9999 := by
  have slots : 2^(S.degreeExponent 0) ≤ slotDegree S :=
    (Finset.le_sup (f := fun j : Fin (S.steps+1) => 2^S.degreeExponent j) (Finset.mem_univ 0)).trans
      (le_max_right _ _)
  filter_upwards [eventually_ordinal_geometry B u D.constants D.numerator D.denominator
    D.addressFactor (slotDegree S) haddr,
    eventually_active_clock B u D.constants D.numerator D.denominator D.addressFactor haddr
      (slotDegree S) slots]
    with n geo budget
  refine ⟨geo.1,geo.2.1,geo.2.2.1,geo.2.2.2.1 (D.geometry n).H,?_⟩
  intro hn V A inst f ok
  dsimp only
  rw [V.scanState_pairInput]
  let labels := laneLabels _ _ V.lanes
  have schedule := geo.2.2.2.2 labels V.dimension le_rfl A f ok
  have clock := budget labels V.dimension le_rfl A f ok
  refine ⟨clock.1,?_⟩
  intro z
  refine ⟨(schedule z).1,fun v => ⟨(schedule z).2 v,?_⟩⟩
  intro half t ht
  exact clock.2 z v half (D.geometry n).H t (n ^ 43) ht
    (Nat.pow_le_pow_right (by omega) (by decide : (43 : ℕ) ≤ 9000))

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
