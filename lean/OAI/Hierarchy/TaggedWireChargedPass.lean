import OAI.Hierarchy.TaggedWireDebitShape
import OAI.Hierarchy.TaggedWireStripLoads

namespace OAI
/-! # A complete ordinary-sum repair on the genuine histogram branch domain -/

noncomputable section
namespace Hierarchy.WireTelescope.ChosenPackets
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open AdaptiveProbe ProtocolRAM RepairHistogram
open Computability.VPVNP.BurstRAM
open scoped BigOperators Classical
variable {S n g p w t : ℕ} {A : Type} [Fintype A] {F : Type} [Field F]
variable {letters copies : Fin t→ℕ} (G : PortGraph (Fin S) (Fin g)) (K : PortGraph (Fin S) A)
    (P : PortGraph (Fin S) (Fin p)) (pad : Chord S)
    (batch : ∀j,Row F S (letters j) (copies j)) (tender : ∀j,RowRouting (batch j) (unionRows G P pad))
    (bank : Bank) (cols : Columns) (src : ℕ) (state : BallChoices letters copies→Memory w)
    (stock debits : Fin g→ℕ) (reserved used : A→ℕ) (paid : BallChoices letters copies→Fin p→ℕ)
    (carried : Widths S)

local notation "startWidth" => carried+G.chordWidths stock+K.chordWidths reserved
local notation "nextWidth" => fun c : BallChoices letters copies=>carried+P.chordWidths (paid c)+
  G.chordWidths (RepairHistogram.raw bank cols src n (state c))+K.chordWidths (fun a=>reserved a-used a)

/-- Each row already carries its actual packet and original chronological
hop ordinal. These are the exact signed factors used before capping stock. -/
theorem step
    (source : (∑j,(batch j).input)=G.chordWidths debits+K.chordWidths used)
    (ports : Fin t→ℕ) (slots : (Σj,Fin (ports j))≃Fin n)
    (gain : ∀c j i,(tender j).install.load ((tender j).bits (c j)) (stockRow i)=
      ∑ z, if kind bank cols (state c) (slots ⟨j,z⟩)=some i then installedBits cols (state c) (slots ⟨j,z⟩) else 0)
    (bill : ∀c e,(∑j,(tender j).install.load ((tender j).bits (c j)) (paidRow e))=paid c e)
    (apart : ∀i,G.tail i≠G.head i) (dormant : ∀c e,P.tail e=P.head e→paid c e=0)
    (need : ∀ c i,OuterBank.resourceBits (kind bank cols (state c)) (consumedBits (n:=n) cols (state c)) i=debits i)
    (old : ∀ c i,(state c (bank.base+i.val)).val=stock i)
    (fund : ∀i,debits i≤ stock i) (held : ∀a,used a≤reserved a) (sep : bank.base+g≤ src)
    (room : ∀ c i,stock i+OuterBank.resourceBits (kind bank cols (state c))
      (installedBits (n:=n) cols (state c)) i<2^w) :
    let measured c := stock_read slots (fun j i=>(tender j).install.load ((tender j).bits (c j)) (stockRow i)) bank cols (state c) (gain c)
    let target := target_shape G P pad batch tender bank cols state paid measured bill apart dormant
    let M := mixedMatrix (n:=n) G K P bank cols src state stock debits reserved used paid carried
      (fun j=>(batch j).input) (fun j c=>(tender j).post c) (fun j c=>(tender j).entry c)
      source target need old fund held sep room
    ∀x,(raw F startWidth).coeff x=∑c,SiteMatrix.act (M c) (raw F (nextWidth c)).coeff x := by
  intro measured target M x
  exact mixedMatrix_action (n:=n) G K P bank cols src state stock debits reserved used paid carried
    (fun j=>(batch j).input) (fun j c=>(tender j).post c) (fun j c=>(tender j).entry c)
    source target need old fund held sep room (fun j=>(tender j).entry_sum) x

end Hierarchy.WireTelescope.ChosenPackets

end
end OAI
