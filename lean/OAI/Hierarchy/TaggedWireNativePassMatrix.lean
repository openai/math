import OAI.Hierarchy.TaggedWireRepairStock
import OAI.Hierarchy.TaggedWirePassMatrix

namespace OAI
/-! # The prescribed signed table at the actual committed native stock transition -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ProtocolRAM ProtocolRAM.RepairHistogram AdaptiveProbe
open Computability.VPVNP.BurstRAM
open scoped Classical BigOperators Fin.CommRing

variable {F : Type*} [Field F] {S n g W t : ℕ}
    {J : Fin t → Type} [∀ j,Fintype (J j)]

def mixedMatrix {A E : Type} [Fintype A] [Fintype E]
    (G : PortGraph (Fin S) (Fin g)) (K : PortGraph (Fin S) A) (P : PortGraph (Fin S) E)
    (bank : Bank) (p : Columns) (src : ℕ) (state : (∀j,J j)→Memory W)
    (stock debits : Fin g→ℕ) (reserve consume : A→ℕ) (paid : (∀j,J j)→E→ℕ)
    (carried : Widths S) (demand : Fin t→Widths S) (inst : ∀j,J j→Widths S)
    (tiles : ∀j c,SiteMatrix (State (demand j)) (State (inst j c)) F)
    (sourceShape : (∑j,demand j)=G.chordWidths debits+K.chordWidths consume)
    (targetShape : ∀c,(∑j,inst j (c j)) =
      G.chordWidths (OuterBank.resourceBits (kind bank p (state c)) (installedBits (n:=n) p (state c)))+
        P.chordWidths (paid c))
    (selected : ∀ c e,OuterBank.resourceBits (kind bank p (state c)) (consumedBits (n:=n) p (state c)) e=debits e)
    (before : ∀c,∀i : Fin g,(state c (bank.base+i.val)).val=stock i)
    (fund : ∀ i,debits i≤ stock i) (held : ∀a,consume a≤reserve a) (sep : bank.base+g≤ src)
    (room : ∀c i,stock i+OuterBank.resourceBits (kind bank p (state c))
      (installedBits (n:=n) p (state c)) i<2^W) :
    ∀c : ∀j,J j, SiteMatrix (State (carried+G.chordWidths stock+K.chordWidths reserve))
      (State (carried+P.chordWidths (paid c)+G.chordWidths (RepairHistogram.raw bank p src n (state c))+
        K.chordWidths (fun a=>reserve a-consume a))) F := by
  let h := mixed_shapes (n:=n) G K P bank p src state stock debits reserve consume
    paid carried demand inst sourceShape targetShape selected before fund held sep room
  exact PassMatrix.actual tiles (passive G K carried stock debits reserve consume) h.1 h.2

theorem mixedMatrix_action {A E : Type} [Fintype A] [Fintype E]
    (G : PortGraph (Fin S) (Fin g)) (K : PortGraph (Fin S) A) (P : PortGraph (Fin S) E)
    (bank : Bank) (p : Columns) (src : ℕ) (state : (∀j,J j)→Memory W)
    (stock debits : Fin g→ℕ) (reserve consume : A→ℕ) (paid : (∀j,J j)→E→ℕ)
    (carried : Widths S) (demand : Fin t→Widths S) (inst : ∀j,J j→Widths S)
    (tiles : ∀j c,SiteMatrix (State (demand j)) (State (inst j c)) F)
    (sourceShape : (∑j,demand j)=G.chordWidths debits+K.chordWidths consume)
    (targetShape : ∀c,(∑j,inst j (c j)) =
      G.chordWidths (OuterBank.resourceBits (kind bank p (state c)) (installedBits (n:=n) p (state c)))+
        P.chordWidths (paid c))
    (selected : ∀ c e,OuterBank.resourceBits (kind bank p (state c)) (consumedBits (n:=n) p (state c)) e=debits e)
    (before : ∀c,∀i : Fin g,(state c (bank.base+i.val)).val=stock i)
    (fund : ∀ i,debits i≤ stock i) (held : ∀a,consume a≤reserve a) (sep : bank.base+g≤ src)
    (room : ∀c i,stock i+OuterBank.resourceBits (kind bank p (state c))
      (installedBits (n:=n) p (state c)) i<2^W)
    (tileLaw : ∀j x,(ChordGraph.raw F (demand j)).coeff x=∑c,SiteMatrix.act (tiles j c)
      (ChordGraph.raw F (inst j c)).coeff x)
    (x : ∀s,State (carried+G.chordWidths stock+K.chordWidths reserve) s) :
    (ChordGraph.raw F (carried+G.chordWidths stock+K.chordWidths reserve)).coeff x=
      ∑c : ∀j,J j,SiteMatrix.act (mixedMatrix (n:=n) G K P bank p src state stock debits reserve consume paid carried demand inst tiles
            sourceShape targetShape selected before fund held sep room c)
        (ChordGraph.raw F (carried+P.chordWidths (paid c)+G.chordWidths (RepairHistogram.raw bank p src n (state c))+
          K.chordWidths (fun a=>reserve a-consume a))).coeff x := by
  let h := mixed_shapes (n:=n) G K P bank p src state stock debits reserve consume
    paid carried demand inst sourceShape targetShape selected before fund held sep room
  exact PassMatrix.actual_action tiles (passive G K carried stock debits reserve consume) h.1 h.2 tileLaw x

end Hierarchy.WireTelescope

end
end OAI
