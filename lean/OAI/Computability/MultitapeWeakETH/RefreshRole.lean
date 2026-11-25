import OAI.Computability.MultitapeWeakETH.RefreshGuard
import OAI.Computability.VPVNP.PairRefreshTraversalMapBody

/-! # The complete local refresh action on independent bit tapes -/

namespace OAI.Computability.MultitapeWeakETH.RefreshOperands

open IntegerMultiplication Code VPVNP BurstRAM Compression Compression.Refresh Compression.DegreeRefresh
open CompressorRecords PortRefresh OperandInputs PhaseRecipe PairSimulation LocalHistory NodeArguments
open RefreshMapOperands DescriptorSpace NewSlots MotifBlocks MotifConversion MotifSelector StackInterpreter
open scoped Fin.CommRing
noncomputable section

set_option maxRecDepth 6000
set_option maxHeartbeats 2400000

variable {A k : Type} [Codec A] [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
local notation "D" => 2^S.portExponent
local notation "H" => 2^S.expanderExponent
local notation "hE" => Nat.two_pow_pos S.expanderExponent
local notation "hC" => And.left (S.port_bound.connected_and_pos S.port_order)

/-- On both successful and rejected refresh calls, the tape program agrees with the
native traversal's emitted list, including its test of the two diagonal ties. -/
theorem refresh_role {hist : ℕ} (order : B.Entry ≃ Fin hist) (read : A × Bits.Word → Bits.Word) (hr : Poly read) :
    ∃ run : Query A → Option (List Tally), Poly run ∧ ∀ {w g : ℕ} (ctx : A) (L : Layout) (i n : ℕ)
      (X : State S.portExponent (S.portExponent+g))
      (choice : DyadicRefreshChoice (a₀:=S.degreeExponent 0) (g:=g) X S.graph hE hC B.refresh)
      (p : (X.Base × BitWord g) × Fin (2^S.portExponent)) (old : X.network.Half (oldSite X p))
      (new : (dyadicRefreshNext X S.graph hE hC B.refresh S.port_order S.degree_bounds.2 choice).network.Half
        (promotedSites p)) (C : LevelRecipe.Context w) (cap : ℕ),
      let Y := dyadicRefreshNext X S.graph hE hC B.refresh S.port_order S.degree_bounds.2 choice
      let bs := packed X (oldSite X p) old
      let cs := packed Y (promotedSites p) new
      (∀ j : BurstRAM.Word w, read (ctx,wordBits j) = wordBits (C.memory j.val)) →
      RefreshPayloadHistory.Data B L i n X choice C.memory →
      C.state.val = levelStart L i → (C.pub 2).val = levelStart L (i+1) →
      (C.pub 0).val = (sites X.baseIndex (bitWordFinEquiv g) p).val → 2^g < 2^w →
      D < 2^w → X.maxWireWidth ≤ cap → Y.maxWireWidth ≤ cap → cap < 2^w →
      bs.length ≤ 2^w → cs.length ≤ 2^w →
      run (encode ctx C bs cs cap) = (TraversalPlan.emitted B order X choice p old new).map
        (List.map (tally ∘ Fin.val)) := by
  choose eval ep exec using compile_expr read hr
  let number (e : (parameterData B.refresh).Entry) := (order (.inr e)).val
  obtain ⟨lookup,cost,correct⟩ := refresh_entry B read hr number
  refine ⟨fun x => bif guard eval B x then lookup x else none,
    Poly.choose (guard_poly eval ep B) cost (Code.Poly.const none),?_⟩
  intro w g ctx L i n X choice p old new C cap Y bs cs rd stored state succ site lanes degree ow nw fit ob nb
  let x := encode ctx C bs cs cap
  let F := blockSupplyWidths (splitSlots X) (bitWordFinEquiv S.portExponent) (splitWidths X) S.graph hE hC B.refresh choice
  let U := packedIncidence L w i (X.positions*D)
  let V := packedIncidence L w (i+1) (Y.positions*2^(S.degreeExponent 0))
  let s := RefreshBlockPlan.shape B
  have args := describes s X p S.graph.toSlotGraph S.port_order S.degree_bounds.2 F U V C stored.geometry
    state succ site lanes
  have test := diagonal_test X p S.graph.toSlotGraph S.port_order S.degree_bounds.2 F old new
    (input s) C U V _ _ _ args stored.old.actual stored.new.actual stored.stored.segments degree eval x
    (fun e => exec e ctx C bs cs cap rd) rfl ob nb (by simpa only [x,encode,tally_length] using ow) (ow.trans_lt fit)
  let val : ℤ := portDiagonal (oldPortMatching (splitSlots X) (bitWordFinEquiv S.portExponent))
    (groupedWidths (bitWordFinEquiv S.portExponent) (splitWidths X)) p.1 p.2 (oldHalf X p old)
    (segments X p S.graph.toSlotGraph S.port_order S.degree_bounds.2 F new)
  have diag : guard eval B x = decide (val = (1:ℤ)) := test
  have found := correct ctx L i n X choice p old new C cap rd stored state succ site lanes degree ow nw fit ob nb
  change (bif guard eval B x then lookup x else none) = _
  rw [diag]
  unfold TraversalPlan.emitted
  by_cases good : val = (1:ℤ)
  · rw [decide_eq_true good,Bool.cond_true,ite_eq_left good]
    exact found.trans (by simp only [Option.map_map,List.map_map,Function.comp_def,number]; rfl)
  · rw [decide_eq_false good,Bool.cond_false,ite_eq_right good,Option.map_none]

end
end OAI.Computability.MultitapeWeakETH.RefreshOperands
