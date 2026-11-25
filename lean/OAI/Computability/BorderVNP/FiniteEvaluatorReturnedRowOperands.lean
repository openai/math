import OAI.Computability.BorderVNP.FiniteEvaluatorGeometryFields
import OAI.Computability.BorderVNP.FiniteEvaluatorMergedEmitted
import OAI.Computability.BorderVNP.CellTeamGeometryCharge
import OAI.Computability.BorderVNP.CellPacketSupplementalProducerRows

/-! # The finite scalar cell's actual word counts and seven-word launch operands -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native.FiniteFields

open Crossing Packing Packing.Inherited FrozenTape CellSparse Packet CellAddresses CellAddressPhysical
open CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork FinalReports FiniteEvaluator RoutingISA
open scoped Classical BigOperators

variable {a m n C k w d entries : ℕ} {σ O : Type} [Fintype σ]
    (F : Fields a m n C d k w σ) (boxes : Fin a → List (Source.Box O)) (entry : Fin entries → Fin a)
    (arena stride gap desc g digits : ℕ)
    {D : ℕ} {P A : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → A) (number : A ≃ Fin C) (state : N.Site → Site)
    (sid : N.Site ↪ Fin a) (edges : N.Edge ↪ Fin m) (ports : P ↪ Fin n)
local notation "placedCell" => number ∘ cell
local notation3 (prettyPrint := false) "widths" => fun v => (state v).size
local notation3 (prettyPrint := false) "rowSite" c => Merged.site N cell c sid edges ports state

/-- Reindexing the cell names changes none of the native merged work, incoming, or
total widths; both enumerations are compared to the same natural slot number. -/
theorem numbered_bank_words (c : A) :
    guessedSize N placedCell (number c)+siteSize N placedCell (number c) widths = (rowSite c).work ∧
    suppliedSize N placedCell (number c) = (rowSite c).incoming := by
  let code := number.toEmbedding.trans Fin.valEmbedding
  have numeric := Merged.CellKey.bankSizes N placedCell Fin.valEmbedding (number c) state
  have original := Merged.CellKey.bankSizes N cell code c state
  exact ⟨congrArg₂ (·+·) (numeric.1.symm.trans original.1) (numeric.2.1.symm.trans original.2.1),
    numeric.2.2.symm.trans original.2.2⟩

variable {x : σ → Bool} (physical : Represents N (number ∘ cell) (fun v => (state v).size) sid edges ports F x)
    (sizeFit : ∀ c, guessedSize N (number ∘ cell) c+siteSize N (number ∘ cell) c (fun v => (state v).size)+
      suppliedSize N (number ∘ cell) c < 2^w)
    {cap h t : ℕ} {R B U V : Type} (S : Schema R B) (L : Schema U V)
    (sh : ∀ r, (S.tags r).length ≤ cap) (lh : ∀ r, (L.tags r).length ≤ cap)
    (sx : Pins R B h → Bool) (ly : Pins U V t → Bool) (cells : Fin a → Fin C) (off box : Fin a → ℕ)
local notation3 (prettyPrint := false) "args" => operand F boxes entry arena stride gap desc g digits (x:=x)
local notation3 (prettyPrint := false) "dir" => History.directory S L boxes sh lh (priv g digits) (rep g digits)
  args sx ly cells off box

include physical sizeFit in
/-- The actual transposed finite-field report emitter writes precisely the named
cell's private work count and its bit-major scalar count positions. -/
theorem directory_named (c : A) (room : (rowSite c).size+digits*g ≤ 2^w) :
    (dir).privateWires (number c).castSucc=(rowSite c).work ∧
      (dir).reports (number c).castSucc=Reports.fields (rowSite c).size g digits := by
  obtain ⟨work,input⟩ := numbered_bank_words N cell number state sid edges ports c
  have size := congrArg₂ (·+·) work input
  change _ = (rowSite c).size at size
  have info := directory_real F boxes entry arena stride gap desc g digits N placedCell state sid edges ports
    physical sizeFit S L sh lh sx ly cells off box (number c) (size ▸ room)
  exact ⟨info.1.trans work,info.2.trans (congrArg (fun n => Reports.fields n g digits) size)⟩

end CellPacketGeometry.History.Native.FiniteFields

namespace FiniteEvaluator.Merged

open Crossing Packing Packing.Inherited CellSparse Packet CellPacketGeometry CellPacketGeometry.SiteWords
open RoutingISA RoutingISA.CellPacket RoutingISA.CellPacket.Supplement RoutingISA.TypedTaskBuilder
open scoped Classical

variable {D C s e p slots : ℕ} {P A Orig : Type} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → A) (number : A ≃ Fin C)
    (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin e) (portID : P ↪ Fin p) (state : N.Site → Site)
    (owners : Fin s → Fin C) (aligned : ∀ v, owners (siteID v)=number (cell v))
    (D₀ : SiteWords.Directory (Fin slots) Orig (C+1)) (places : ℕ → Placed Orig)
    (shape : TypedBatch.SourceShape (fun c : Fin (C+1) => places c.val) D₀)
    (fs : Orig → List Factor) (g digits : ℕ) (c : A)
local notation3 (prettyPrint := false) "row" => site N cell c siteID edgeID portID state

include shape aligned in
/-- After the physical task scan chooses this global cell number, the rebasing of
the descriptor, external, scratch and burst pointers preserves the exact sparse
directory and work count consumed by the finite validator. The single directory
readback is the canonical row supplied by the terminal geometry return. -/
theorem produced_row_operands (l : CellControlRows.Layout) (mem : ℕ → ℕ) (geom : ℕ → ℕ)
    (i : ℕ) (ordinal : globalCell l.toLayout mem i=(number c).val)
    (orig : (places (number c).val).factors=fs)
    (actual : (D₀.placed (number c).castSucc 0 (fun _ => 0) fs 0 0 0 0 0 []).directory =
      FinalCell.directory (fun j => (owners j).val) N (fun v => (number (cell v)).val)
        siteID edgeID portID state (number c).val (D₀.reports (number c).castSucc))
    (fields : D₀.privateWires (number c).castSucc=(row).work ∧
      D₀.reports (number c).castSucc=Reports.fields (row).size g digits) :
    let owned := Batch.produced l mem places geom (fun _ => []) i
    owned.placed.directory=Placement.packet N cell c siteID edgeID portID state (Reports.fields (row).size g digits) ∧
      owned.placed.privateWires=(row).work := by
  have h := shape.privateWires (number c).castSucc
  have same : (places (number c).val).directory =
      (D₀.placed (number c).castSucc 0 (fun _ => 0) fs 0 0 0 0 0 []).directory := by
    change CellSparse.Directory.mk ((places (number c).val).boxes.map (Source.factors (places (number c).val).factors))
      (places (number c).val).rows (places (number c).val).reports = _
    rw [orig,show (places (number c).val).boxes = _ from shape.boxes (number c).castSucc,
      show (places (number c).val).rows = _ from shape.records (number c).castSucc,
      show (places (number c).val).reports = _ from shape.reports (number c).castSucc]
    rfl
  have source := (same.trans actual).trans (CellKey.packet_directory N cell c siteID
    (number.toEmbedding.trans Fin.valEmbedding) (fun j => (owners j).val) (fun v => congrArg Fin.val (aligned v))
    edgeID portID state (D₀.reports (number c).castSucc)).symm
  rw [fields.2] at source
  change (places (globalCell l.toLayout mem i)).directory = _ ∧ (places (globalCell l.toLayout mem i)).privateWires = _
  rw [ordinal]
  exact ⟨source,h.trans fields.1⟩

end FiniteEvaluator.Merged

end BorderVNP
end Computability
end OAI
