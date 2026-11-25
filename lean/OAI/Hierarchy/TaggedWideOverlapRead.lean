import OAI.Hierarchy.TaggedWirePacketNeighbor
import OAI.Hierarchy.TaggedWideControlOperands
import OAI.Hierarchy.TaggedWidePassiveGate

namespace OAI
/-! The interval length and both shifts are the actual control RAM words even at
vacant roles and between distinct parallel edges. -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.SiteControls
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.CoreBoard.HistoryRoles WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.RAM DescriptorExpr
open Tagged PassiveWindow
open scoped Classical Fin.CommRing

variable {S W D cap : ℕ} {s : Fin S}
variable (m : Memory W) (reg : Word W) {t : ((portGraph S).Port s)→ℕ}
    (o : Parts ((portGraph S).Port s) (Fin D) cap t) (row : Fin D→LocalPrefix.Columns) (low : Fin D→Expr)
    (portion : ((portGraph S).Port s)→ℕ)

/-- The underlying probes contain the explicitly constructed original row
prefix and active counts before testing the interaction of two slots. -/
structure EndpointReads : Prop where
  start : ∀i,((common row i).eval m reg).val=o.base i
  width : ∀i,((row i).width.eval m reg).val=o.width i
  lowAt : ∀i,((low i).eval m reg).val=(o.owner i).elim 0 portion
  peer : ∀i p,o.owner i=some p→0<o.width i→((row i).opposite.eval m reg).val=(PacketNeighbor.other p).val
  vacant : ∀i,o.owner i=none → o.width i=0

theorem EndpointReads.view (H : EndpointReads m reg o row low portion) (i : Fin D) :
    Overlap.slice m reg (interval row low i)=o.view portion i := by
  simp only [Overlap.slice,interval,H.start,H.width,H.lowAt,Parts.view]

variable (pass before after : ((portGraph S).Port s)→ℕ)
    (l : Parts ((portGraph S).Port s) (Fin D) cap fun p=>pass p+before p)
    (r : Parts ((portGraph S).Port s) (Fin D) cap fun p=>pass p+after p)
    (col : Bool→Fin D→LocalPrefix.Columns) (cut : Bool→Fin D→Expr)
    (a : EndpointReads m reg l (col false) (cut false) before)
    (b : EndpointReads m reg r (col true) (cut true) after)

include a b in
/-- A single authenticated length comparison returns the clipped overlap of
the surviving suffixes of the same global half-chord. -/
theorem overlap_words (capFit : cap<2^W)
    (L : ∀i,l.base i+l.width i<2^W) (R : ∀j,r.base j+r.width j<2^W)
    (addFit : ∀i j (side : Bool),lo (l.view before i) (r.view after j)+
      (if side then (r.view after j).low else (l.view before i).low)<2^W) :
    (∀i j,((compile cap col cut (.inr ((i,j),0))).eval m reg).val=(header cap (l.view before i) (r.view after j) (linked pass before after l r i j)).val) ∧
    (∀i j side,((compile cap col cut (.inr ((i,j),if side then 2 else 1))).eval m reg).val=(heads cap (l.view before i) (r.view after j) side).val) := by
  let left (i : Fin D) := interval (col false) (cut false) i
  let right (j : Fin D) := interval (col true) (cut true) j
  constructor
  · intro i j
    have ll : ((left i).start.eval m reg).val+((left i).width.eval m reg).val<2^W := by
      simpa only [left,interval,a.start,a.width] using L i
    have rr : ((right j).start.eval m reg).val+((right j).width.eval m reg).val<2^W := by
      simpa only [right,interval,b.start,b.width] using R j
    change ((Overlap.length (left i) (right j)).eval m reg).val=_
    rw [Overlap.length_value m reg _ _ ll rr,a.view,b.view]
    have bounds:=span_bound (l.view before i) (r.view after j)
    have top : span (l.view before i) (r.view after j)≤cap := bounds.1.trans (l.within i)
    by_cases nz:span (l.view before i) (r.view after j)=0
    · simp [nz,header]
    · have li:0<l.width i:=by have:=bounds.1;change _≤l.width i at this;omega
      have rj:0<r.width j:=by have:=bounds.2;change _≤r.width j at this;omega
      cases h1:l.owner i with
      | none=>have:=a.vacant i h1;omega
      | some p=>
        cases h2:r.owner j with
        | none=>have:=b.vacant j h2;omega
        | some q=>
          have same : (left i).opposite.eval m reg=(right j).opposite.eval m reg ↔ p=q := by
            change (col false i).opposite.eval m reg=(col true j).opposite.eval m reg ↔ _
            rw [←Fin.val_inj,a.peer i p h1 li,b.peer j q h2 rj,Fin.val_inj,PacketNeighbor.other_injective.eq_iff]
          by_cases h:p=q
          · simp [header,linked,h1,h2,h,same,Nat.min_eq_right top]
          · simp [header,linked,h1,h2,h,Ne.symm h,same]
  · intro i j side
    have lv : Overlap.slice m reg (left i)=l.view before i :=
      EndpointReads.view m reg l (col false) (cut false) before a i
    have rv : Overlap.slice m reg (right j)=r.view after j :=
      EndpointReads.view m reg r (col true) (cut true) after b j
    have bound : lo (Overlap.slice m reg (left i)) (Overlap.slice m reg (right j))+
        ((if side then right j else left i).low.eval m reg).val<2^W := by
      rw [lv,rv]
      cases side
      · change lo _ _+((cut false i).eval m reg).val<_
        rw [a.lowAt]
        exact addFit i j false
      · change lo _ _+((cut true j).eval m reg).val<_
        rw [b.lowAt]
        exact addFit i j true
    have value := Overlap.head_value m reg cap (left i) (right j) side capFit bound
    rw [lv,rv] at value
    cases side <;> simpa [compile,heads,left,right] using value

end Hierarchy.ProtocolRAM.SiteControls

end
end OAI
