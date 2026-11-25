import OAI.Hierarchy.DescentResetLocalRosterPrice
import OAI.Hierarchy.DescentResetRankFunctions
import OAI.Hierarchy.DescentResetActualSourcePull

namespace OAI
/-! # Original cable key and source-slot programs of the public reset calendar -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentResetLocalRoster DescentSIMDLookup
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "height" => GroupStage.depthBound D n f g

local notation "oldH" => input.placement.degree+2
local notation "r" => B.reset.k-B.terminals.commonDepth
local notation "Y" => (2^B.reset.n:ℕ)
local notation "payload" => (2^(S.groupWidth k tail i+k-B.terminals.commonDepth)+1)*oldH*2^k
local notation "links" => max Y (2^height)
local notation "instructions" => max (Fintype.card (DescentCommonPalette.rotor B.reset.graph).Edge) (2^(height+1))

theorem key_count_at_date :
    DescentResetParentCodec.capCount oldH r Y payload input.placement.cap links instructions =
      keyCount D k n height input.placement.cap (programCount ctl.board height) := by
  have brd:=same_count B.reset.graph ctl.board B.dimension B.graph height
  unfold programCount DescentResetCableSlots.cableCap at brd
  unfold keyCount programCount DescentResetCableSlots.cableCap
  rw [brd,B.commonDepth,B.keyWidth,B.dimension,input.branch,Nat.add_sub_cancel_left]

/-- Both digit widths are public. All six ordinal and charge bounds needed by
the native source queries follow from the measured capacity of the old stage. -/
theorem key_rooms :
    let cap:=input.placement.cap
    let b:=fieldBits (2^g*cap)
    let t:=originalBits D k n height cap (programCount ctl.board height) g
    B.next.placement.cap<2^b ∧ B.next.placement.degree+1<2^b ∧ B.raw.cap≤2^b ∧
    B.next.placement.cap<2^t ∧ B.next.placement.degree+1<2^t ∧
      DescentResetParentCodec.capCount oldH r Y payload cap links instructions≤2^t := by
  dsimp only
  simp only [B.next_capacity,B.next.branch,B.capacity,key_count_at_date]
  have bf:=Nat.le_pow_clog (by decide : 1<2) (max 5 (2^g*input.placement.cap+2))
  have tf:=Nat.le_pow_clog (by decide : 1<2)
    (max (max 5 (2^g*input.placement.cap+1))
      (keyCount D k n height input.placement.cap (programCount ctl.board height)))
  unfold fieldBits originalBits
  omega

theorem signed_digit_room :
    max (B.next.placement.degree+1) (B.next.placement.cap+1)<2^(fieldBits (2^g*input.placement.cap)) := by
  rw [B.next.branch,B.next_capacity]
  unfold fieldBits
  have bf:=Nat.le_pow_clog (by decide : 1<2) (max 5 (2^g*input.placement.cap+2))
  omega

theorem before_at_date :
    wordBefore B=publicBefore D k n height (S.groupWidth k tail i) input.placement.cap (programCount ctl.board height) := by
  have brd:=same_count B.reset.graph ctl.board B.dimension B.graph height
  unfold programCount DescentResetCableSlots.cableCap at brd
  unfold wordBefore publicBefore programCount DescentResetCableSlots.cableCap
  rw [brd,B.commonDepth,B.keyWidth,B.dimension,input.branch,Nat.add_sub_cancel_left]

theorem slot_at_date (j : Fin (totalLocal B)) :
    slotGate B j=publicSourceSlot D k n height input.placement.cap (programCount ctl.board height)
      (publicSlots ctl.board height k input.placement.cap) j.val := by
  have brd:=same_count B.reset.graph ctl.board B.dimension B.graph height
  unfold programCount DescentResetCableSlots.cableCap at brd
  unfold slotGate publicSourceSlot programCount DescentResetCableSlots.cableCap
  generalize atJ : j.val = j₀
  rw [local_roster_exact B]
  unfold stemsCount
  rw [brd,B.commonDepth,B.keyWidth,B.dimension,input.branch,Nat.add_sub_cancel_left]

theorem code_calendar {W₀ W₂ : MarkedWorld F d P bits} {z₀ D₀ j z₂ D₂ : ℕ}
    {first : Reached W₀ G q ε S k 0 z₀ D₀ w hist} {last : Reached W₂ G q ε S k j z₂ D₂ w hist}
    (a : Chronology.Path first input) (suffix : Chronology.Path input last)
    (calendar : List ℕ) (issued : (a.append suffix).capFactors=calendar) (cap₀ : first.placement.cap=256) :
    let cap:=(calendar.take i).prod*256
    let code:=programCount ctl.board height
    wordBefore B=publicBefore D k n height (S.groupWidth k tail i) cap code ∧
    ∀j : Fin (totalLocal B),slotGate B j=publicSourceSlot D k n height cap code (publicSlots ctl.board height k cap) j.val := by
  intro cap code
  have agreed : input.placement.cap=cap:=by
    rw [a.capacity_prefix suffix calendar issued,cap₀,Nat.sub_zero]
  exact ⟨by rw [before_at_date,agreed],fun j=>by rw [slot_at_date,agreed]⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
