import OAI.Computability.BorderVNP.FiniteEvaluatorCellKeyDirectory
import OAI.Computability.BorderVNP.FiniteEvaluatorMergedHostScore
import OAI.Computability.BorderVNP.CellPacketGeometryHistoryFinal

/-! # The genuine geometry-emitted field validator in the numeric owned-cell table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History

open Crossing Shortening CellSparse Packet Packing Packing.Inherited FrozenTape LiveWords SiteWords
open FiniteEvaluator FiniteEvaluator.Merged RoutingISA
open scoped Classical

variable {a C cap d t : ℕ} {R B U V E Orig A : Type}
    (S : Schema R B) (L : Schema U V) (boxes : Fin a → List (Source.Box Orig))
    (sh : ∀ r, (S.tags r).length ≤ cap) (lh : ∀ r, (L.tags r).length ≤ cap)
    (priv : Fin (C+1) → E) (rep : Fin (C+1) → List (List E)) (args : E → ℕ)
    (x : Pins R B d → Bool) (y : Pins U V t → Bool) (cells : Fin a → Fin C) (off box : Fin a → ℕ)
local notation3 "G₀" => directory S L boxes sh lh priv rep args x y cells off box

variable {D n p : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → A) (number : A ≃ Fin C) (siteID : N.Site ↪ Fin a) (edgeID : N.Edge ↪ Fin n)
    (portID : P ↪ Fin p) (state : N.Site → Site)
local notation3 "code" => number.toEmbedding.trans Fin.valEmbedding
local notation3 "key" => fun v => (number (cell v)).val
local notation3 "s₀" c => Merged.site N cell c siteID edgeID portID state

/-- The true sparse geometry compiler writes the merged validator of the
original field cell, even when that cell is named by an arbitrary semantic
type. Its literal box roster, immutable history records, rebased bindings
and bit-major report addresses are read in native row order. -/
theorem emitted_validator {F : Type*} [Fintype F] (c : A) (digits H : ℕ)
    (slot : Orig → ℕ) (fs : Orig → List Factor) (pub desc ext scratch burst : ℕ)
    (input : Fin (s₀ c).incoming → Bool) (claim : Fin (Fintype.card F) → Fin digits → Bool)
    (named : ∀ v, cells (siteID v)=number (cell v))
    (historical : S.Image x (siteID.trans Fin.valEmbedding) state)
    (final : L.Section y (siteID.trans Fin.valEmbedding) (FinalCell.binding N key siteID edgeID portID state))
    (table : ∀ i, (boxes i).map (Source.factors fs)=FinalCell.slots siteID (fun v => (state v).boxes) i)
    (bitBase : ∀ v, off (siteID v)=CellAddresses.siteBase N key (key v) siteID (fun z => (state z).size) ⟨v,rfl⟩)
    (boxBase : ∀ v, box (siteID v)=FinalCell.firstBox siteID (fun j => (cells j).val) state v)
    (privateWidth : (G₀).privateWires (number c).castSucc=(s₀ c).work)
    (report : (G₀).reports (number c).castSucc=Reports.fields (s₀ c).size (Fintype.card F) digits) :
    TypedBatch.cellInput ((G₀).placed (number c).castSucc H slot fs pub desc ext scratch burst
      (List.ofFn input++FiniteScalarRounds.stream F claim))=Merged.validator (s₀ c) digits input claim := by
  have body := placed_directory S L boxes sh lh priv rep args x y cells off box N key siteID edgeID portID state
    (number c) H slot fs pub desc ext scratch burst (List.ofFn input++FiniteScalarRounds.stream F claim)
    historical final table bitBase boxBase
  rw [report] at body
  have source := body.trans (CellKey.packet_directory N cell c siteID code (fun j => (cells j).val)
    (fun v => congrArg Fin.val (named v)) edgeID portID state _).symm
  rw [← Merged.report_directory] at source
  unfold TypedBatch.cellInput Merged.validator
  rw [source]
  exact congrArg (fun k => (⟨_,k,List.ofFn input++FiniteScalarRounds.stream F claim⟩ : CompactMachine.CellInput)) privateWidth

end CellPacketGeometry.History

end BorderVNP
end Computability
end OAI
