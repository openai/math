import OAI.Hierarchy.TaggedWireEarnedPhysical
import OAI.Hierarchy.TaggedWireStockOrdinals

namespace OAI
/-! # Transport of native named inventory totals and unordered acquired-row observations -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open AdaptiveProbe ProbeStage CoreBoard LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open scoped Classical BigOperators
variable {h d k S g : ℕ} (π : Equiv.Perm (Fin (2^h))) (name : Site h d k↪Fin S)
local notation "Good" => Commodity (Fin (2^h)) (Stages h d) k
local notation "order" => stockOrder h d k

/-- Reindex all stock rows by the actual measured bank lookup, including physically
distinct directed goods whose chords happen to share endpoints. -/
theorem earned_inventory_width (native : Good≃Fin g) (amount : Fin g→ℕ) :
    (earnedInventory π name).chordWidths (fun i=>amount (((order).symm.trans native) i))=
      (CoreBoard.ordinalGoods π name native).chordWidths amount := by
  change (CoreBoard.ordinalGoods π name order).chordWidths _=_
  rw [CoreBoard.ordinalGoods_width,CoreBoard.ordinalGoods_width]
  apply congrArg (commodityGraph π name).chordWidths
  funext i
  simp only [Function.comp_apply,Equiv.trans_apply,Equiv.symm_apply_apply]

theorem charged_ends_width {E : Type} [Fintype E] (G H : PortGraph (Fin S) E) (amount : E→ℕ)
    (printed : ∀i,0<amount i→(G.tail i=H.tail i ∧ G.head i=H.head i) ∨
      (G.tail i=H.head i ∧ G.head i=H.tail i)) : G.chordWidths amount=H.chordWidths amount := by
  classical
  unfold PortGraph.chordWidths
  apply Finset.sum_congr rfl
  intro i _
  by_cases pos : 0<amount i
  · rcases printed i pos with ⟨l,r⟩|⟨l,r⟩
    · simp only [PortGraph.chordWidth,l,r]
    · rcases lt_trichotomy (H.tail i) (H.head i) with lt|eq|gt
      · simp [PortGraph.chordWidth,l,r,lt,not_lt.mpr lt.le]
      · simp [PortGraph.chordWidth,l,r,eq]
      · simp [PortGraph.chordWidth,l,r,gt,not_lt.mpr gt.le]
  · have zero : amount i=0:=Nat.eq_zero_of_not_pos pos
    simp [PortGraph.chordWidth, zero]

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
