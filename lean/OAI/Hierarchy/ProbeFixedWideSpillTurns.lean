import OAI.Hierarchy.ProbeFixedWideSpillRank
import OAI.Hierarchy.ProbeFixedWideSpillOffsets
import OAI.Hierarchy.ProtocolRAMDateSpillTurnPage
import OAI.Hierarchy.TaggedWideProgramRates

namespace OAI
/-! # The original native calendar's per-date five-field boards -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native CoreBoard AdaptiveProbe
open ThreeFlat.RAM PhysicalProcedure
open HistoryRoles RoleProgram
open scoped Classical BigOperators Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width bits datedROM terminalROM terminalWork rankFirst turnFirst : ℕ)
local notation "T" => (events v.mesh).length
local notation "native" => v.wideTerminal h width bits terminalROM terminalWork
local notation "w" => wordBits h (2^v.W) copies
variable (oldStart newStart leftOnly rightOnly : Fin (events v.mesh).length→ℕ)

def wideSpillTurnStride :=
  let t:=native
  (RoleROM.bank 0 t.board.old).size+(RoleROM.bank 0 t.board.edges).size+4*2^t.romBits+
    30*t.turns+5*(t.sites*t.seats)+7

def wideSpillTurnPage (j : Fin T) : DateSpill.TurnPage v.widePacketDegree :=
  let start:=turnFirst+j.val*v.wideSpillTurnStride h width bits terminalROM terminalWork
  let sides:=v.wideSpillOffsetSides h width bits datedROM terminalROM terminalWork
    (oldStart j) (newStart j) (leftOnly j) (rightOnly j)
  ⟨start,native,v.wideSpillPage h width bits rankFirst j.val,sides.1,sides.2⟩

local notation "panel" j => v.wideSpillTurnPage h width bits datedROM terminalROM terminalWork rankFirst
  turnFirst oldStart newStart leftOnly rightOnly j

def wideSpillTurnsProgram := ProcedureBank.program T (Fin.cases (scan w 0 0 (.lit 0)) (fun j=>(panel j).program w))
def wideSpillTurnsTicks := 4+∑j:Fin T,(panel j).ticks

/-- The four runtime role tables affect code operands and use a common physical extent. -/
def wideSpillTurnsEnd (_datedROM terminalROM terminalWork _rankFirst turnFirst : ℕ)
    (_oldStart _newStart _leftOnly _rightOnly : Fin (events v.mesh).length→ℕ) :=
  turnFirst+T*v.wideSpillTurnStride h width bits terminalROM terminalWork

theorem wide_spill_turn_cheap :
    CheapCode (v.wideSpillTurnsProgram h width bits datedROM terminalROM terminalWork rankFirst turnFirst
      oldStart newStart leftOnly rightOnly) := by
  let parts : Fin (T+1)→Procedure w := Fin.cases (scan w 0 0 (.lit 0)) (fun j=>(panel j).program w)
  have allowed : ∀i,CheapCode (parts i) :=
    @Fin.cases T (fun i=>CheapCode (parts i)) (@scan_cheap w 0 0 (.lit 0))
      (fun j=>@DateSpill.TurnPage.cheap v.widePacketDegree (panel j) w)
  exact @WideCPU.bank_cheap w T parts @allowed

theorem wide_spill_turn_end (j : Fin T) :
    (panel j).stop≤turnFirst+(j.val+1)*v.wideSpillTurnStride h width bits terminalROM terminalWork := by
  have bound:=(panel j).window.stop_le
  change (panel j).window.stop≤_
  change (panel j).window.stop≤(panel j).first+
    (RoleROM.bank 0 (native).board.old).size+(RoleROM.bank 0 (native).board.edges).size+
    4*2^(native).romBits+30*(native).turns+5*((native).sites*(native).seats)+7 at bound
  simpa only [wideSpillTurnPage,wideSpillTurnStride,Nat.succ_mul,Nat.add_assoc] using bound

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
