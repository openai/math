import OAI.ThreeFlat.RAM.TickFrontROM
import OAI.ThreeFlat.RAM.TickCheckedBank
import OAI.ThreeFlat.RAM.TickAuxRequestROM
import OAI.ThreeFlat.RAM.TickRequestStream

namespace OAI
/-! # Continuing history-branch control flow inside the native tick ROM -/

namespace ThreeFlat.RAM.TickHistoryCore

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr Diagonal.TickChronology
open TickFrontROM
open scoped Fin.CommRing

variable {w k p r : ℕ}

abbrev Labels (e : Term w k 1) := (Fin 7 × Fin 10) ⊕
    (Fin (TickCheckedBank.count e) ⊕ ((Bool × Fin 4) ⊕ (Fin 14 ⊕ Fin 1)))

def checked (e : Term w k 1) (P : Labels e ↪ Fin p) :
    Fin (TickCheckedBank.count e) ↪ Fin p :=
  ⟨fun i => P (.inr (.inl i)),fun _ _ h => Sum.inl.inj (Sum.inr.inj (P.injective h))⟩

def chunk (e : Term w k 1) (P : Labels e ↪ Fin p) : Fin 14 ↪ Fin p :=
  ⟨fun i => P (.inr (.inr (.inr (.inl i)))),fun _ _ h => by simpa using P.injective h⟩

def test (e : Term w k 1) (P : Labels e → Fin p) (ev : Bool) (i : Fin 4) :=
  P (.inr (.inr (.inl (ev,i))))

def returned (e : Term w k 1) (P : Labels e → Fin p) := P (.inr (.inr (.inr (.inr 0))))

def enter (e : Term w k 1) (P : Labels e → Fin p) (ph : Phase) := P (.inl (phaseNo ph,0))

def resumeAux (e : Term w k 1) (P : Labels e ↪ Fin p) :=
  TickGenerateTable.driver e (TickCheckedBank.generatePC e (checked e P)) 0

/-- The stage walker jumps back to resumeAux after decoding the selected raw
histogram and filling the scratch controls. The group scan returns one unit
after verifying its chunk. The weighted path terminates at the field return.
All other history ticks go through the ordinary chunk comparison. -/
def emit (a reqStart : ℕ) (regions : TickIdentity.Regions)
    (dest header : Fin 4 → Word w) (P : Labels (TickRequestStream.program reqStart (TickAuxRequestGen.row (k:=k) header)) ↪ Fin p)
    (regH : Fin 5 ↪ Fin r) (regAux : Fin (4+(TickRequestStream.program reqStart (TickAuxRequestGen.row (k:=k) header)).binds) ↪ Fin r)
    (regCheck : Fin 37 ↪ Fin r) (testReg : Fin 2 ↪ Fin r) (cmpReg : Fin 7 ↪ Fin r)
    (navigation scan evaluation : Fin p) :
    Labels (TickRequestStream.program reqStart (TickAuxRequestGen.row (k:=k) header)) → Instr w p r k :=
  let e := TickRequestStream.program reqStart (TickAuxRequestGen.row (k:=k) header)
  fun label => match label with
  | .inl (ph,i) => TickControlHeader.emit (fun j => P (.inl (ph,j))) regH dest
      (TickControlHeader.markerAddr (phase ph) regions.oldAux regions.newAux) navigation i
  | .inr (.inl i) => TickCheckedBank.emit e reqStart (reqStart+8*a : ℕ)
      regions.oldAux regions.newAux (checked e P) regAux regCheck (test e P false 0) i
  | .inr (.inr (.inl (false,i))) =>
      TickMarkerSwitch.emitOn (test e P false) testReg (header 0) (Phase.scan.tag : Word w) scan
        (chunk e P (TickIdentity.compare w regions.oldChunk regions.newChunk a).first) i
  | .inr (.inr (.inl (true,i))) =>
      TickMarkerSwitch.emitOn (test e P true) testReg (header 0) (Phase.evaluate.tag : Word w)
        evaluation (returned e P) i
  | .inr (.inr (.inr (.inl i))) =>
      (TickIdentity.compare w regions.oldChunk regions.newChunk a).emit (chunk e P) cmpReg Fin.elim0
        (test e P true 0) i
  | .inr (.inr (.inr (.inr _))) => .accept

theorem labels_le (reqStart : ℕ) (header : Fin 4 → Word w) :
    Fintype.card (Labels (TickRequestStream.program reqStart (TickAuxRequestGen.row (k:=k) header))) ≤ 1400 := by
  have expr := TickRequestStream.program_binds reqStart (TickAuxRequestGen.row (k:=k) header)
  have row := TickAuxRequestGen.row_binds (k:=k) header
  simp only [Labels,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,TickCheckedBank.count,Term.labels_eq]
  omega

end ThreeFlat.RAM.TickHistoryCore

end OAI
