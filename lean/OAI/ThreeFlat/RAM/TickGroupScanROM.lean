import OAI.ThreeFlat.RAM.TickGroupScanSetup
import OAI.ThreeFlat.RAM.TickChunkProgram
import OAI.ThreeFlat.RAM.TickCheckedBank

namespace OAI
/-! # The native program for the history scan phase -/

namespace ThreeFlat.RAM.TickGroupScanBank

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr TickGroupScanSetup TickIntervalCursor
open TickChunkCheck Diagonal.TickGroupIntervals ChunkRequests TickBitRelation
open scoped Classical Fin.CommRing

variable {w k p r : ℕ} {F : Type*} [Semiring F]

/-- Old and new refer to the external chunk pins. The cached pointers select
the old and new halves of the actual group proposal in shared auxiliary. -/
structure Plan extends Addresses where
  reqStart : ℕ
  oldPtr : ℕ
  newPtr : ℕ
  old : ℕ
  new : ℕ

def layout (A : Plan) (lo g : ℕ) : Layout := ⟨lo,lo+A.bits,A.mapBase,g⟩

@[simp] theorem size (A : Plan) (lo g : ℕ) : chunkSize (layout A lo g) = A.bits :=
  Nat.add_sub_cancel_left ..

def expr (w k : ℕ) (A : Plan) := TickRequestStream.program A.reqStart
  (TickChunkRule.atRow w k A.mapBase A.oldPtr A.newPtr)

abbrev Labels (w k : ℕ) (A : Plan) := Fin 13 ⊕ (Fin 27 ⊕ Fin (TickCheckedBank.count (expr w k A)))

theorem binds_le (w k : ℕ) (A : Plan) : (expr w k A).binds ≤ 260 := by
  have bound : (TickChunkRule.atRow w k A.mapBase A.oldPtr A.newPtr).binds ≤ 40 :=
    ruleExpr_binds w k true (layout A 0 0) A.oldPtr A.newPtr
  have step := TickRequestStream.program_binds A.reqStart (TickChunkRule.atRow w k A.mapBase A.oldPtr A.newPtr)
  change (TickRequestStream.program A.reqStart (TickChunkRule.atRow w k A.mapBase A.oldPtr A.newPtr)).binds ≤ _
  omega

theorem labels_le (w k : ℕ) (A : Plan) : Fintype.card (Labels w k A) ≤ 927 := by
  have bound := binds_le w k A
  simp only [Labels,Fintype.card_sum,Fintype.card_fin,TickCheckedBank.count,Term.labels_eq]
  omega

def boot (A : Plan) (P : Labels w k A ↪ Fin p) (i : Fin 13) := P (.inl i)
def cursor (A : Plan) (P : Labels w k A ↪ Fin p) (i : Fin 27) := P (.inr (.inl i))
def checked (A : Plan) (P : Labels w k A ↪ Fin p) : Fin (TickCheckedBank.count (expr w k A)) ↪ Fin p :=
  ⟨fun i => P (.inr (.inr i)),fun _ _ h => Sum.inr.inj (Sum.inr.inj (P.injective h))⟩

def checkEntry (A : Plan) (P : Labels w k A ↪ Fin p) :=
  TickGenerateTable.driver (expr w k A) (TickCheckedBank.generatePC (expr w k A) (checked A P)) 0

def emit (A : Plan) (P : Labels w k A ↪ Fin p)
    (regs : Fin 15 ↪ Fin r) (gen : Fin (4+(expr w k A).binds) ↪ Fin r)
    (chk : Fin 37 ↪ Fin r) (next : Fin p) : Labels w k A → Instr w p r k
  | .inl i => TickGroupScanSetup.emit A.toAddresses (boot A P) regs (cursor A P 0) i
  | .inr (.inl i) => TickIntervalCursor.rows (cursor A P) regs (checkEntry A P) i
  | .inr (.inr i) => TickCheckedBank.emit (expr w k A) (A.reqStart : Word w)
      (A.reqStart+8*A.bits : ℕ) (A.old : Word w) (A.new : Word w) (checked A P) gen chk next i


end ThreeFlat.RAM.TickGroupScanBank

end OAI
