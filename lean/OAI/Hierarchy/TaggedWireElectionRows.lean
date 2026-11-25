import OAI.Hierarchy.TaggedWireBranchRead
import OAI.Hierarchy.ProbeSelectedPacketWidths

namespace OAI
/-! # The signed packet row is fixed by the pre-choice election -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.WireTelescope
open ProtocolRAM ProtocolRAM.Calendar ProtocolRAM.PurchaseStage
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat.Diagonal.MotifOuterTerms
open Tagged Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open scoped Classical BigOperators Fin.CommRing
namespace ChosenPackets.Row
variable {F : Type} [Field F] {S H r : ℕ}

def retype (P : Placed F S) (letters : H=P.data.terms) (copies : ℕ) : Row F S H copies :=
  letters.symm ▸ Row.packet P copies

def passive (H : ℕ) (zero : r=0) : Row F S H r := zero.symm ▸ Row.skipped H

theorem input_retype (P : Placed F S) (letters : H=P.data.terms) (copies : ℕ) :
    (retype P letters copies).input=P.wants copies := by subst H;rfl

theorem output_retype (P : Placed F S) (letters : H=P.data.terms) (copies : ℕ) (j : Histogram (Fin H) copies) :
    (retype P letters copies).output j=P.offers (cast (congrArg (fun h=>Histogram (Fin h) copies) letters) j) := by
  subst H
  rfl

theorem entry_retype (P : Placed F S) (letters : H=P.data.terms) (copies : ℕ) (j : Histogram (Fin H) copies) :
    HEq ((retype P letters copies).entry j) (P.signed copies (cast (congrArg (fun h=>Histogram (Fin h) copies) letters) j)) := by
  subst H
  rfl

theorem input_passive (zero : r=0) : (passive (F:=F) (S:=S) H zero).input=0 := by subst r;rfl
theorem output_passive (zero : r=0) (j : Histogram (Fin H) r) : (passive (F:=F) (S:=S) H zero).output j=0 := by subst r;rfl
end ChosenPackets.Row

namespace CalendarTape.HistogramFormat
open ChosenPackets
variable {F X : Type} [Field F] {W q d S : ℕ} {C : Chart W q d}
variable (D : HistogramFormat C X) (a : Attempt) (x : X) (m : Memory W)
local notation "b" => enabledBatch (C.layout a) (ProtocolRAM.Calendar.repair C a)
local notation "snap" => HistogramShelf.snapshot C a m
local notation "I" => Fin (C.layout a).candidates
local notation "elected" => fun i:I=>(b).selected snap (i.val:Word W)

/-- The finite menu, the frozen stock and the catalogue layout determine
this row before its counter is supplied by any branch. -/
def electedRow (view : D.observed a x m) (menu : ∀i:I,elected i→Placed F S)
    (arity : ∀i hi,(menu i hi).data.terms=((b).termCount.read snap ((b).packet.eval snap (i.val:Word W))).val)
    (i : I) : Row F S (D.letters a x i) (D.copies a x i) :=
  if hi:elected i then Row.retype (menu i hi) ((view.1 i).trans (arity i hi).symm) _
  else Row.passive _ ((view.2 i).trans (ite_eq_right hi))

theorem electedRow_source (view : D.observed a x m) (menu : ∀i:I,elected i→Placed F S)
    (arity : ∀i hi,(menu i hi).data.terms=((b).termCount.read snap ((b).packet.eval snap (i.val:Word W))).val)
    (i : I) (hi : elected i) :
    (D.electedRow a x m view menu arity i).input=(menu i hi).wants (b).copies := by
  have copies : (C.raw a).batch.copies = (b).copies := rfl
  simpa only [electedRow,dite_eq_left hi,Row.input_retype,view.2 i,ite_eq_left hi] using
    congrArg (menu i hi).wants copies

theorem electedRow_dormant (view : D.observed a x m) (menu : ∀i:I,elected i→Placed F S)
    (arity : ∀i hi,(menu i hi).data.terms=((b).termCount.read snap ((b).packet.eval snap (i.val:Word W))).val)
    (i : I) (hi : ¬elected i) (j : Histogram (Fin (D.letters a x i)) (D.copies a x i)) :
    (D.electedRow a x m view menu arity i).input=0 ∧ (D.electedRow a x m view menu arity i).output j=0 := by
  exact ⟨by rw [electedRow,dite_eq_right hi];exact Row.input_passive _,
    by rw [electedRow,dite_eq_right hi];exact Row.output_passive _ _⟩
end CalendarTape.HistogramFormat

end Hierarchy.WireTelescope

end
end OAI
