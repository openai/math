import OAI.Computability.VPVNP.CompressorPrefixLevelScale
import OAI.Computability.VPVNP.CompressorBlockShrinkPrefixFits
import OAI.Computability.VPVNP.CompressorRecordRefreshAdmitted
import OAI.Computability.VPVNP.CompressorSelectedTermWorker

/-!
# Motif selector word and clock bounds at reachable boundaries

The shrinking and refresh selectors use different native tables. Both accept
a fixed clock determined by the input length and the templates. The refresh
bound also covers the width cells emitted by the chosen continuation.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.PrefixLevelScale

open Compression CursorBounds Filter DescriptorSpace

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

/-- Fixed word-width contribution of the refresh selector for the schedule's expander and motif
tie order. -/
def refreshConstant := PortRefresh.termConstant S.graph (Nat.two_pow_pos _)
  (S.port_bound.connected_and_pos S.port_order).1 B.refresh (RefreshBlockPlan.order B)

/-- Uniform width and clock arithmetic used in the selected refresh run. -/
theorem eventually_refresh (b : ℕ) (hb : 1 ≤ b) : ∀ᶠ n : ℕ in atTop,
    ∀ (R : Type*) [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f) {g : ℕ}
      (X : State S.portExponent (S.portExponent + g)),
      let p := Refresh.dyadicRefreshPass X S.graph (Nat.two_pow_pos _)
        (S.port_bound.connected_and_pos S.port_order).1 B.refresh S.port_order S.degree_bounds.2
        (f ∘ Sum.inr) ((B.solution_iff f).mp hf).2
      ∀ (choice : p.step.Choice), X.maxWireWidth ≤ n → (p.next choice).maxWireWidth ≤ n →
        let w := wordBits b n
        let s := RefreshBlockPlan.shape B
        refreshConstant B + 4 * Nat.clog 2 (X.maxWireWidth + 1) ≤ w ∧
          TermWorker.budget B.refresh s.ties (s.ports * s.dH) w X.maxWireWidth ≤
            SelectedTermWorker.clock B w ∧
          (p.next choice).maxWireWidth < 2 ^ w := by
  let K := max (refreshConstant B) (SelectedTermWorker.fitConstant B)
  filter_upwards [DemandPreparation.eventually_live_word_fits b hb K 4 1 1,
    CursorRAM.eventual_word_room b hb PolynomiallyBounded.id] with n hfit room
  intro R _ f hf g X p choice input output w s
  have hw : K + 4 * Nat.clog 2 (X.maxWireWidth + 1) ≤ w :=
    hfit _ (by simpa using input)
  have native := SelectedTermWorker.budget_le (.refresh X : PassOrigin B f hf p)
    ((Nat.add_le_add_right (le_max_right (refreshConstant B) _) _).trans hw)
  exact ⟨(Nat.add_le_add_right (le_max_left _ _) _).trans hw, native, output.trans_lt room⟩

/-- Apply the actual shrinking prefix bounds directly to a partial semantic
execution at its current graph. -/
theorem eventually_shrink (b : ℕ) (hb : 1 ≤ b) : ∀ᶠ n : ℕ in atTop,
    ∀ (R : Type*) [CommRing R] (i : Fin S.steps) {g b' l' : ℕ}
      (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
      (E : StateExecution R b' l' X),
      Within (initialPositions b n) n E → ∀ (base blocks : ℕ)
      (level : Fin (BlockProgram.layout B base (initialPositions b n) blocks).levels),
      let L := BlockProgram.layout B base (initialPositions b n) blocks
      let w := wordBits b n
      endAddress L < 2 ^ w → ∀ cap, ShrinkBranch.prefixClock B b n ≤ cap →
        ShrinkBranch.PrefixFits B X (packedIncidence L w level.val (DemandRAM.oldCount X))
          (tableBase L level.val (0 : Fin 6)) (Fin.ofNat _ 10) cap := by
  filter_upwards [ShrinkBranch.eventually_prefixFits B b hb] with n fit
  intro R _ i g b' l' X E live
  exact fit i X live.current.1 live.current.2

end CompressorRecords.PrefixLevelScale

end

end VPVNP
end Computability
end OAI
