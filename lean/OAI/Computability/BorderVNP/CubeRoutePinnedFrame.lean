import OAI.Computability.BorderVNP.CubeRouteScheduledWriters
import OAI.Computability.BorderVNP.RoutingISASignedTaskArena
import OAI.Computability.BorderVNP.PackedHistoryRoutingFrame

/-! # Routing-array pointers in the ordinary signed boot bank -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP BurstRAM TeamContraction TeamContraction.ProcessorSlots Packing RoutingOutputs

/-- The five scheduler pointers supplied by the fixed scalar bank. The count is produced later by the two writers. -/
structure TablePointers (tab : TableLayout) (mem : ℕ → ℕ) : Prop where
  records : mem (tab.frame+12) = tab.records
  widths : mem (tab.frame+16) = tab.widths
  offsets : mem (tab.frame+17) = tab.offsets
  used : mem (tab.frame+18) = tab.used
  ordinals : mem (tab.frame+20) = tab.ordinals

/-- Install the routing and task operands in the caller's public bank. The geometry and packet
encoders subsequently supply their own ordinary fields. -/
noncomputable def _root_.OAI.Computability.BorderVNP.RoutingISA.SignedTaskArena.Layout.routeBank {w : ℕ} (l : SignedTaskArena.Layout)
    (frame : ℕ) (other : Arg → Word w) (j : Arg) : Word w :=
  (l.bootOperand frame j.val).elim (other j) (TeamTapeInputEmit.word w)

variable {w : ℕ}

/-- At the five scheduler pointer positions the complete public argument bank has the
actual cube-arena values, even after the geometry and reference-packet encoders. -/
theorem pinnedTablePointers (arena : SignedTaskArena.Layout) (B : PacketOperands) (frame count : ℕ)
    (other : Arg → Word w) (origin edges cells : ℕ) (m : Memory w)
    (room : arena.cube.stop < 2^w) :
    let pub := B.bank (core (arena.routeBank frame other) origin edges cells)
    (∀ j ∈ [12,16,17,18,20], m (frame+j) = pub (Fin.ofNat 32 (j+1))) →
      TablePointers (arena.cube.table frame count) (readings m) := by
  intro pub hw
  let tab := arena.cube.table frame count
  have endRoom : arena.cube.pairBase < 2^w := by
    have low : arena.cube.pairBase ≤ arena.cube.stop := by
      unfold CubeArena.Layout.stop CubeArena.Layout.cellBank
      omega
    exact low.trans_lt room
  have fit : tab.records < 2^w ∧ tab.widths < 2^w ∧ tab.offsets < 2^w ∧ tab.used < 2^w ∧ tab.ordinals < 2^w := by
    dsimp only [tab,CubeArena.Layout.table,TableLayout.reserve]
    dsimp only [CubeArena.Layout.pairBase,TableLayout.reserveEnd] at endRoom
    omega
  have atArg (j : ℕ) (hj : j ∈ [12,16,17,18,20]) (ptr : ℕ)
      (key : arena.bootOperand frame (j+1) = some ptr) (bound : ptr < 2^w) :
      readings m (frame+j) = ptr := by
    have h := congrArg Fin.val (hw j hj)
    have lo : 7 ≤ (Fin.ofNat 32 (j+1)).val := by simp at hj; rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide
    have hi : (Fin.ofNat 32 (j+1)).val ≤ 21 := by simp at hj; rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide
    change (m (frame+j)).val = _
    rw [h,show pub _ = core (arena.routeBank frame other) origin edges cells (Fin.ofNat 32 (j+1)) from
      B.bank_passthrough _ _ lo hi]
    have no : core (arena.routeBank frame other) origin edges cells (Fin.ofNat 32 (j+1)) =
        arena.routeBank frame other (Fin.ofNat 32 (j+1)) := by
      simp at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> rfl
    have val : (Fin.ofNat 32 (j+1)).val = j+1 := Nat.mod_eq_of_lt (by simp at hj; omega)
    rw [no,SignedTaskArena.Layout.routeBank,val,key]
    exact Nat.mod_eq_of_lt bound
  exact ⟨atArg 12 (by decide) _ rfl fit.1,atArg 16 (by decide) _ rfl fit.2.1,
    atArg 17 (by decide) _ rfl fit.2.2.1,atArg 18 (by decide) _ rfl fit.2.2.2.1,
    atArg 20 (by decide) _ rfl fit.2.2.2.2⟩

/-- The allocated startup's complete pin/profile computation preserves all five encoded
pointers in the genuine reached RAM. -/
theorem pinnedTablePointers_of_profile {d : ℕ} (task : SignedTaskArena.Layout) (start : StartupArena)
    (team : Fin start.teams) (slot count : ℕ) (p : ReferencePacket w d) (other : Arg → Word w)
    (origin edges cells : ℕ) (guess : ℕ → Bool) {f : BroadcastFrame} {advice : AdviceLayout}
    {bits : List Bool} {bank : Bank w} {saved after : Memory w} (room : task.cube.stop < 2^w) :
    let B := start.operands team slot p
    let pub := B.bank (core (task.routeBank start.frame other) origin edges cells)
    B.Fits w → ∀ {F : Pins.ProcessorFields B.layout}, JointHeader.BootHeaderState F f advice p pub bits bank saved →
      (∀ j < start.next, after j = Pins.preparedMemory B.layout guess saved B.layout.count j) →
        TablePointers (task.cube.table start.frame count) (readings after) := by
  intro B pub fitted F boot resident
  have base : (pub 0).val = start.frame := B.frameBase_word _ fitted
  have kept := (PackedHistoryCircuit.resident_frames start team slot p guess base boot resident).1
  apply pinnedTablePointers task B start.frame count other origin edges cells after room
  intro j hj
  have hj' : j < 31 := by simp at hj; omega
  simpa only [base] using kept ⟨j,hj'⟩

/-- Only the five indicated addresses are needed when a later native pass overwrites other core fields. -/
theorem TablePointers.transfer {tab : TableLayout} {m m' : ℕ → ℕ} (p : TablePointers tab m)
    (keep : ∀ j ∈ [12,16,17,18,20], m' (tab.frame+j) = m (tab.frame+j)) : TablePointers tab m' :=
  ⟨(keep 12 (by decide)).trans p.records,(keep 16 (by decide)).trans p.widths,
    (keep 17 (by decide)).trans p.offsets,(keep 18 (by decide)).trans p.used,(keep 20 (by decide)).trans p.ordinals⟩

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
