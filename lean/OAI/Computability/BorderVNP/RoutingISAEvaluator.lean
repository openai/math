import OAI.Computability.BorderVNP.RoutingISABoot
import OAI.Computability.BorderVNP.RoutingISAAdvice
import OAI.Computability.BorderVNP.RoutingISABroadcastProof
import OAI.Computability.BorderVNP.PackedDirectoryISA
import OAI.Computability.BorderVNP.TransmissionPins
import OAI.Computability.BorderVNP.TransmissionISA
import OAI.Computability.BorderVNP.DiagonalTallyRAMSerialize
import OAI.Computability.BorderVNP.DiagonalResidueRAMStage
import OAI.Computability.BorderVNP.RoutingISAInverse

/-! # Linking the signed diagonal evaluator's word instructions

The header reader leaves the saved branch bit at the address in register 9.
The unit branch tests all exterior words and the advised distinguished pin.
The evaluation branch performs the public placement, delivery and routing
passes before preparing owned-cell arguments and tallying their exponents.
The residue entry circuit is invoked once by team zero.

The assembler takes static finite instruction fragments for the description
transforms. Each one is inserted into the single instruction table. The
lemmas in this file concern this linkage and its native branch semantics.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM

/-- Only the team holding the matrix pins evaluates the final entry. -/
def leadEntry : Code := .block [
  readFrame 59 62 63 0, .constant 58 0, .ifEq 59 58 DiagonalResidueRAM.stagedReader .nop]

/-- The unit has no private choices. The whole exterior assignment is zero
and the distinguished team's column pin must equal the advised column. -/
def unit : Code := .seq unitLinks checkIdentityPins

/-- Public intervals become physical table entries; each team checks its
unused positions and both relay legs before receiving its local bit inputs. -/
def route : Code := .block [scheduleTable, checkPadding, checkRelays, transmitRanges]

/-- The evaluation path, in order of the concrete read and write dependencies.
The instruction fragments compute epoch placements, cube groups and transmission
intervals, local packet and cell arguments, and the verified occurrence records. -/
def evaluate (epochs groups arguments occurrences : Code) : Code := .block [
  preparePins, epochs, Packing.Directory.ISA.program, groups, route, arguments,
  callOwnedCells, occurrences, DiagonalTallyRAM.complete, leadEntry]

/-- Load the branch word saved by the broadcast scan, then take its unique
branch. The preceding reference scan has already checked the word is Boolean. -/
def select (eval : Code) : Code := .seq (.load 10 9) (.ifEq 10 0 unit eval)

/-- Assemble all fixed code and the public initialization into one word program. -/
def assemble (frame epochs groups arguments occurrences : Code) : Code := .block [
  bootFrame, readLiteralAdvice, frame, readBroadcast, select (evaluate epochs groups arguments occurrences)]

/-- The one physical memory read preceding the branch, including its actual value. -/
def branchRead {w : ℕ} (addr : ℕ) (m : Memory w) : TeamRAM.Event w :=
  ⟨.ordinary (some (addr,none)), [m addr], [], .plus⟩

/-- On the saved broadcast, running the selector amounts to two fixed unsigned
ticks followed by precisely the selected branch. This preserves the full trace,
including every private choice made in the evaluation branch. -/
theorem select_iff {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    (f : BroadcastFrame) (eval : Code) (s : Bank w) (m : Memory w)
    (stable : f.Stable (readings s)) {es t mt} :
    Runs pub macros (select eval) s m es t mt ↔
      ∃ rest, es = branchRead f.dst m :: tick w :: rest ∧
        Runs pub macros (if (m f.dst).val = 0 then unit else eval)
          (Function.update s 10 (m f.dst)) m rest t mt := by
  have dst : (s 9).val = f.dst := stable.2.2.2.2.2.2.2.2.2.1
  have zero : (s 0).val = 0 := stable.1
  have first := Runs.load pub macros 10 9 s m
  rw [dst] at first
  let z := Function.update s 10 (m f.dst)
  have guard : z 10 = z 0 ↔ (m f.dst).val = 0 := by
    simp only [z,Function.update_self,Function.update_of_ne (by decide : (0 : Reg) ≠ 10)]
    rw [←Fin.val_inj,zero]
  constructor
  · intro run
    obtain ⟨u,mu,fs,gs,rfl,load,branch⟩ := Runs.seq_iff.mp run
    obtain ⟨rfl,rfl,rfl⟩ := load.unique_of_deterministic rfl first
    obtain ⟨rest,rfl,body⟩ := CellDispatch.eq_split branch
    exact ⟨rest,rfl,by simpa only [←guard] using body⟩
  · rintro ⟨rest,rfl,run⟩
    exact first.seq (Runs.ifEq (by simpa only [←guard] using run))

/-- The linked table has no early accept instruction if all its static
description-transform fragments return normally. -/
theorem assemble_withoutAccept {frame epochs groups arguments occurrences : Code}
    (hf : frame.withoutAccept = true) (he : epochs.withoutAccept = true)
    (hg : groups.withoutAccept = true) (ha : arguments.withoutAccept = true)
    (ho : occurrences.withoutAccept = true) :
    (assemble frame epochs groups arguments occurrences).withoutAccept = true := by
  have boot : bootFrame.withoutAccept = true := by decide
  have advice : readLiteralAdvice.withoutAccept = true := by decide
  have broadcast : readBroadcast.withoutAccept = true := by decide
  have pin : preparePins.withoutAccept = true := by decide
  have dirs : Packing.Directory.ISA.program.withoutAccept = true := by decide
  have routed : route.withoutAccept = true := by decide
  have cells : callOwnedCells.withoutAccept = true := by decide
  have tally : DiagonalTallyRAM.complete.withoutAccept = true := by decide
  have lead : leadEntry.withoutAccept = true := by decide
  have one : unit.withoutAccept = true := by decide
  simp only [assemble, select, evaluate, Code.block, Code.withoutAccept,
    boot,advice,broadcast,pin,dirs,routed,cells,tally,lead,one,hf,he,hg,ha,ho,Bool.and_self]

/-- Every accepting execution of the assembled fixed opcode table follows its
prescribed stages from program counter zero, with its exact choice tape. -/
theorem execute_iff {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {frame epochs groups arguments occurrences : Code}
    (hf : frame.withoutAccept = true) (he : epochs.withoutAccept = true)
    (hg : groups.withoutAccept = true) (ha : arguments.withoutAccept = true)
    (ho : occurrences.withoutAccept = true) {s : Bank w} {m bits es} :
    let c := assemble frame epochs groups arguments occurrences
    TeamRAM.execute (c.program.fetch pub macros) ⟨0,s⟩ m bits = some es ↔
      (∃ t mt, Runs pub macros c s m es t mt) ∧ es.map TeamRAM.Event.choices = bits :=
  Code.execute_iff_runs (assemble_withoutAccept hf he hg ha ho)

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
