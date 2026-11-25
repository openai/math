import OAI.Computability.BorderVNP.CellGadgetEmit
import OAI.Computability.BorderVNP.CellRecordEmit
import OAI.Computability.BorderVNP.CellPacketTypedDecoder
import OAI.Computability.BorderVNP.CellPrivateProcedure
import OAI.Computability.BorderVNP.CellCQFCost
import OAI.Computability.BorderVNP.CellSparseCompiled

/-! # Fixed private translation from sparse typed packets to the cell evaluator

The initial packet holds one copy of each original site table and contains
no generator program. The deterministic private machine resolves the public
box references, constructs the repeated-site and profile checks, and prints
the specialized compact validator. Its input and output registers are
separate from the external wire bank.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram

/-- The compiler bounds a profile's selector width by the number of stored
terms. Every profile generated from a crossing decomposition satisfies this bound. -/
def checkedProgram (D : Directory) (k : ℕ) : Stmt :=
  .seq (.loop (.lit k) (.fixed .guess))
    (.seq D.clipProfiles.recordGuards (.seq (sweep (factorBody 0) D.blocks 0) D.countGuards))

/-- On the paper's profile encodings, the checked program equals the full signed validator. -/
theorem checkedProgram_eq (D : Directory) (k : ℕ) (h : D.ProfileWidths) :
    checkedProgram D k = D.program k := by
  rw [checkedProgram,D.clipProfiles_eq h]
  rfl

/-- Real procedure constructing every signed site-box fragment in scan order. -/
noncomputable def factorSweep : Statement Typed.directory (fun D => sweep (factorBody 0) D.blocks 0) :=
  Local.sweepStmt .signed (Procedure.identity Typed.directory)
    (Procedure.constant Typed.directory Local.paramsCode (0,0,0))

/-- Real procedure that prints the gadget-identifier range check with the actual
number of reported positions. -/
noncomputable def rangeSweep : Statement Typed.directory Directory.rangeGuard := by
  let count := (Procedure.listLength Typed.naturals []).comp getReports
  exact Local.sweepStmt .range (Procedure.identity Typed.directory)
    (count.pair (Procedure.constant Typed.directory (prodCode Nat.bits Nat.bits) (0,0)))

/-- The private guessing prefix depends only on the binary wire-count field. -/
noncomputable def guessPrefix : Statement Nat.bits (fun k => .loop (.lit k) (.fixed .guess)) :=
  loopStmt (litAddr (Procedure.identity Nat.bits)) (constStmt Nat.bits (.fixed .guess))

/-- All physical validity and sign checks on the isolated typed directory. -/
noncomputable def checkStmt : Statement Typed.directory (fun D =>
    .seq D.clipProfiles.recordGuards (.seq (sweep (factorBody 0) D.blocks 0) D.countGuards)) :=
  seqStmt getRecordGuards (seqStmt factorSweep
    (seqStmt rangeSweep (subtotalGuardsStmt (Procedure.identity Typed.directory))))

/-- Native deterministic code constructs the complete compact validator on
the actual typed registers. All loop bounds and offsets depend on the data. -/
noncomputable def programStmt : Statement Typed.input (fun x => checkedProgram x.2 x.1) :=
  seqStmt (guessPrefix.comp (Procedure.first Nat.bits Typed.directory))
    (checkStmt.comp (Procedure.second Nat.bits Typed.directory))

/-- Full physical procedure, starting on the sparse wire packet itself. -/
noncomputable def compiler : Procedure (fun x : ℕ × Directory => bits x.2 x.1) id
    (fun x => CellMacro.Generator.serialized 8 (checkedProgram x.2 x.1)) :=
  programStmt.comp Native.decoder

end CellSparse.Packet.Emit

namespace CellPrivate

open CellSparse CellMacro.Generator ExactQuantumFactoring.BitStackProgram
open VPVNP.RAMTape

/-- One fixed finite stack procedure consumes the packet and returns the
chronological serialized program on the output register. -/
noncomputable def translate : Fragment IO :=
  (PrivateProcedure.call Packet.Emit.compiler IO.row).seq (Fragment.moveWord .row .out)

/-- Actual per-input private time, including both moves between clean stack banks. -/
noncomputable def translateClock (D : Directory) (k : ℕ) : ℕ :=
  Packet.Emit.compiler.cost (k,D) + 8*(Packet.bits D k).length +
    16*(serialized 8 (Packet.Emit.checkedProgram D k)).length + 18

/-- Starting from a well-formed sparse cell packet, the actual finite translator
returns the complete requested program and retains all external wire values. -/
theorem translate_run (D : Directory) (k : ℕ) (ext : List Bool) (widths : D.ProfileWidths) :
    ∃ t ≤ translateClock D k, translate.Runs t (io (Packet.bits D k) ext [])
      (io [] ext (serialized 8 (D.program k))) := by
  let out := serialized 8 (Packet.Emit.checkedProgram D k)
  let s := io (Packet.bits D k) ext []
  have hc := Packet.Emit.compiler.ticks_cost (k,D)
  obtain ⟨t,ht,hr⟩ := PrivateProcedure.call_runs Packet.Emit.compiler IO.row hc s rfl
  have hrow : Function.update s IO.row out = io out ext [] := by
    funext p
    cases p <;> rfl
  change (PrivateProcedure.call Packet.Emit.compiler IO.row).Runs t s (Function.update s IO.row out) at hr
  rw [hrow] at hr
  obtain ⟨u,hu,hm⟩ := Fragment.moveWord_run (src:=IO.row) (dst:=IO.out) (by decide) (io out ext []) rfl
  have hout : Function.update (Function.update (io out ext []) IO.row []) IO.out out = io [] ext out := by
    funext p
    cases p <;> rfl
  change (Fragment.moveWord IO.row IO.out).Runs u (io out ext [])
    (Function.update (Function.update (io out ext []) IO.row []) IO.out out) at hm
  rw [hout] at hm
  refine ⟨t+u, ?_, ?_⟩
  · change t ≤ Packet.Emit.compiler.cost (k,D) + 8*(Packet.bits D k).length+8*out.length+12 at ht
    change u ≤ 2*(4*out.length+3) at hu
    change t+u ≤ Packet.Emit.compiler.cost (k,D) + 8*(Packet.bits D k).length + 16*out.length + 18
    omega
  · have h := Fragment.runs_seq _ _ hr hm
    simpa only [translate,s,out,Packet.Emit.checkedProgram_eq D k widths] using h

end CellPrivate

end BorderVNP
end Computability
end OAI
