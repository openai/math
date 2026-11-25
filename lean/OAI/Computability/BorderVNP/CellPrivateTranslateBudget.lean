import OAI.Computability.BorderVNP.CellPrivateTranslate
import OAI.Computability.BorderVNP.CellEmitStatementCost

/-! # Operational cost decomposition for the fixed private packet translator

This decomposition charges the true finite-stack runs on the actual input. It
does not substitute a composed worst-case polynomial for the costs of its
individual small local tables.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram

/-- The four data-dependent private passes, each on the isolated typed directory. -/
noncomputable def passMeters (D : Directory) : ℕ :=
  getRecordGuards.meter D + factorSweep.meter D + rangeSweep.meter D +
    (subtotalGuardsStmt (Procedure.identity Typed.directory)).meter D

/-- The three sequencing operations between the four directory passes add only
a fixed linear factor. -/
theorem meter_checkStmt (D : Directory) : checkStmt.meter D ≤ 10^36*passMeters D := by
  let totals := subtotalGuardsStmt (Procedure.identity Typed.directory)
  let count := seqStmt rangeSweep totals
  let signed := seqStmt factorSweep count
  have h₁ := meter_seqStmt rangeSweep totals D
  have h₂ := meter_seqStmt factorSweep count D
  have h₃ := meter_seqStmt getRecordGuards signed D
  change count.meter D ≤ _ at h₁
  change signed.meter D ≤ _ at h₂
  change checkStmt.meter D ≤ _ at h₃
  change _ ≤ 10^36*(getRecordGuards.meter D+factorSweep.meter D+rangeSweep.meter D+totals.meter D)
  omega

/-- The guessed wire count is a single binary word. Both the source and the
fixed address-layout padding are included in the actual printer cost. -/
theorem meter_guessPrefix (k : ℕ) :
    guessPrefix.meter k ≤ 10^41*(k.bits.length+layoutSize (.lit 0)+(CellMacro.Generator.serialized 8 (.fixed .guess)).length+1) := by
  have h := meter_loopStmt (litAddr (Procedure.identity Nat.bits)) (constStmt Nat.bits (.fixed .guess)) k
  have hl := meter_litAddr (Procedure.identity Nat.bits) k
  have hi := Procedure.meter_identity Nat.bits k
  have hc := meter_constStmt Nat.bits (.fixed .guess) k
  exact h.trans (by omega)

/-- Printing the top-level program adds the binary guessing prefix and projects
the typed directory once. -/
theorem meter_programStmt (D : Directory) (k : ℕ) :
    programStmt.meter (k,D) ≤ 10^51*(passMeters D + guessPrefix.meter k + (Typed.input (k,D)).length+1) := by
  let p := Procedure.first Nat.bits Typed.directory
  let q := Procedure.second Nat.bits Typed.directory
  have hs := meter_seqStmt (guessPrefix.comp p) (checkStmt.comp q) (k,D)
  have hp := Procedure.meter_comp guessPrefix p (k,D)
  have hq := Procedure.meter_comp checkStmt q (k,D)
  have h₁ := Procedure.meter_first Nat.bits Typed.directory (k,D)
  have h₂ := Procedure.meter_second Nat.bits Typed.directory (k,D)
  have h₃ := meter_checkStmt D
  change p.meter (k,D) ≤ _ at h₁
  change q.meter (k,D) ≤ _ at h₂
  change (guessPrefix.comp p).meter (k,D) ≤ 6*(p.meter (k,D)+guessPrefix.meter k) at hp
  change (checkStmt.comp q).meter (k,D) ≤ 6*(q.meter (k,D)+checkStmt.meter D) at hq
  change _ ≤ 10^51*(passMeters D + guessPrefix.meter k + (prodCode Nat.bits Typed.directory (k,D)).length+1)
  exact hs.trans (by omega)

/-- The typed decoder's actual charge is uniformly quadratic in the literal
wire packet length, including the complete decoded tuple. -/
theorem meter_decoder : ∃ C : ℕ, ∀ (D : Directory) (k : ℕ),
    Native.decoder.meter (k,D) ≤ C*((bits D k).length+1)^2 := by
  obtain ⟨C,hC⟩ := Native.decoder_quadratic
  refine ⟨2*C+3,fun D k => ?_⟩
  have hc := Native.decoder.cost_le_bound (k,D)
  have hl := Native.decoder.output_length_le (k,D)
  change _ ≤ Native.decoder.bound.eval (bits D k).length at hc
  change (Typed.input (k,D)).length ≤ (bits D k).length + Native.decoder.bound.eval (bits D k).length at hl
  rw [hC] at hc hl
  change Native.decoder.cost (k,D)+(bits D k).length+(Typed.input (k,D)).length+1 ≤ _
  have h : (bits D k).length+1 ≤ ((bits D k).length+1)^2 := by nlinarith
  nlinarith

end CellSparse.Packet.Emit

namespace CellPrivate

open CellSparse ExactQuantumFactoring.BitStackProgram

/-- All remaining compiler charges are the four explicit sparse passes. Packet
decoding is quadratic and the guessing-prefix fields contribute linearly. -/
theorem translateClock_le_passes : ∃ C : ℕ, ∀ D k,
    translateClock D k ≤ C*(Packet.Emit.passMeters D + ((Packet.bits D k).length+1)^2 + k.bits.length+1) := by
  obtain ⟨A,hA⟩ := Packet.Emit.meter_decoder
  let pad := Packet.Emit.layoutSize (.lit 0) + (CellMacro.Generator.serialized 8 (.fixed .guess)).length
  refine ⟨10^96*(A+pad+2),fun D k => ?_⟩
  have ht : translateClock D k ≤ 32*Packet.Emit.compiler.meter (k,D) := by
    simp only [translateClock,Procedure.meter,id_eq]
    omega
  have h := Procedure.meter_comp Packet.Emit.programStmt Packet.Native.decoder (k,D)
  have hp := Packet.Emit.meter_programStmt D k
  have hg := Packet.Emit.meter_guessPrefix k
  have hd := hA D k
  have hz := Packet.Native.decoder.words_le_meter (k,D)
  change _ ≤ 6*(Packet.Native.decoder.meter (k,D)+Packet.Emit.programStmt.meter (k,D)) at h
  change (Packet.bits D k).length + (Packet.Typed.input (k,D)).length + 1 ≤ Packet.Native.decoder.meter (k,D) at hz
  change Packet.Emit.guessPrefix.meter k ≤ 10^41*(k.bits.length+Packet.Emit.layoutSize (.lit 0)+
    (CellMacro.Generator.serialized 8 (.fixed .guess)).length+1) at hg
  have hg' : Packet.Emit.guessPrefix.meter k ≤ 10^41*(k.bits.length+pad+1) := by simpa [pad,Nat.add_assoc] using hg
  let s := Packet.Emit.passMeters D + ((Packet.bits D k).length+1)^2 + k.bits.length+1
  have hs : ((Packet.bits D k).length+1)^2 ≤ s := by dsimp [s]; omega
  have hs' : 1 ≤ s := by dsimp [s]; omega
  have hA' := Nat.mul_le_mul_left A hs
  have hpad := Nat.mul_le_mul_left pad hs'
  change translateClock D k ≤ 10^96*(A+pad+2)*s
  change _ ≤ 6*(Packet.Native.decoder.meter (k,D)+Packet.Emit.programStmt.meter (k,D)) at h
  change Packet.Emit.compiler.meter (k,D) ≤ _ at h
  have hp' : Packet.Emit.passMeters D + k.bits.length+1 ≤ s := by dsimp [s]; omega
  nlinarith only [ht,h,hp,hg',hd,hz,hs,hs',hA',hpad,hp']

end CellPrivate

end BorderVNP
end Computability
end OAI
