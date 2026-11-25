import OAI.Hierarchy.TaggedWideOverlapRead
import OAI.Hierarchy.TaggedWideWeightRead

namespace OAI
/-! # The five original control operands read from physical chronological role tables -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.SiteControls
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.CoreBoard.HistoryRoles WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.RAM DescriptorExpr
open Tagged PassiveWindow
open scoped Classical Fin.CommRing BigOperators
variable {S W D cap : ℕ} {s : Fin S}

structure ApertureGeometry (m : Memory W) (reg : Word W) {t : ((portGraph S).Port s)→ℕ}
    (o : Parts ((portGraph S).Port s) (Fin D) cap t) (row : Fin D→LocalPrefix.Columns) : Prop where
  neighbors : PacketTurns.NeighborReads m reg o (fun i=>(row i).width) (fun i=>(row i).opposite)
  owned : ∀i,(o.owner i).isSome=true ↔ 0<o.width i
  total : ∀q,(∑i,(ChordAperture.sizeAt o i q).val)=ChordAperture.room o q
  roomFit : ∀q,ChordAperture.room o q<2^W

open private Overlap.minimum from OAI.Hierarchy.TaggedWideOverlapNative in
private theorem aperture_values (m : Memory W) (reg : Word W) {t : ((portGraph S).Port s)→ℕ}
    (o : Parts ((portGraph S).Port s) (Fin D) cap t) (row : Fin D→LocalPrefix.Columns) (low : Fin D→Expr) (portion : ((portGraph S).Port s)→ℕ)
    (seen : EndpointReads m reg o row low portion) (geo : ApertureGeometry m reg o row)
    (sites : S≤2^W) (capFit : cap<2^W) :
    (∀i j,((aperture cap row (.inl (i,j))).eval m reg).val=(ChordAperture.sizeAt o i j).val) ∧
    (∀i side,((aperture cap row (.inr (.inl (i,side)))).eval m reg).val=(ChordAperture.head o i side).val) ∧
    (∀i,((aperture cap row (.inr (.inr i))).eval m reg).val=ChordAperture.room o i) := by
  have sizes:=weight_read o row m reg geo.neighbors sites geo.owned seen.vacant
  refine ⟨?_,?_,?_⟩
  · intro i j
    have bound : (ChordAperture.sizeAt o i j).val<2^W:=(Nat.le_of_lt_succ (ChordAperture.sizeAt o i j).isLt).trans_lt capFit
    change ((weight _ _).eval m reg).val=_
    rw [sizes,Fin.val_cast_of_lt bound]
  · intro i side
    cases side
    · rfl
    · change ((Overlap.small (.lit cap) (common row i)).eval m reg).val=min cap (o.base i)
      rw [Overlap.minimum,seen.start]
      change min ((cap : Word W).val) (o.base i)=min cap (o.base i)
      rw [Fin.val_cast_of_lt capFit]
  · intro j
    simp only [aperture,LocalPrefix.total_eval,sizes,←Nat.cast_sum,geo.total,Fin.val_cast_of_lt (geo.roomFit j)]

variable (m : Memory W) (reg : Word W) (pass before after : ((portGraph S).Port s)→ℕ)
    (l : Parts ((portGraph S).Port s) (Fin D) cap fun p=>pass p+before p) (r : Parts ((portGraph S).Port s) (Fin D) cap fun p=>pass p+after p)
    (col : Bool→Fin D→LocalPrefix.Columns) (low : Bool→Fin D→Expr)

structure CompiledFields : Prop where
  size : ∀side i j,((compile cap col low (.inl (side,.inl (i,j)))).eval m reg).val=
    (if side then (ChordAperture.sizeAt r i j).val else (ChordAperture.sizeAt l i j).val)
  head : ∀side i b,((compile cap col low (.inl (side,.inr (.inl (i,b))))).eval m reg).val=
    (if side then (ChordAperture.head r i b).val else (ChordAperture.head l i b).val)
  room : ∀side i,((compile cap col low (.inl (side,.inr (.inr i)))).eval m reg).val=(if side then ChordAperture.room r i else ChordAperture.room l i)
  length : ∀i j,((compile cap col low (.inr ((i,j),0))).eval m reg).val=
    (header cap (l.view before i) (r.view after j) (linked pass before after l r i j)).val
  heads : ∀i j side,((compile cap col low (.inr ((i,j),if side then 2 else 1))).eval m reg).val=(PassiveWindow.heads cap (l.view before i) (r.view after j) side).val

theorem compile_fields (a : EndpointReads m reg l (col false) (low false) before)
    (b : EndpointReads m reg r (col true) (low true) after)
    (leftGeo : ApertureGeometry m reg l (col false)) (rightGeo : ApertureGeometry m reg r (col true))
    (sites : S≤2^W) (capFit : cap<2^W) (L : ∀i,l.base i+l.width i<2^W) (R : ∀j,r.base j+r.width j<2^W)
    (addFit : ∀i j (side : Bool),lo (l.view before i) (r.view after j)+
      (if side then (r.view after j).low else (l.view before i).low)<2^W) :
    CompiledFields m reg pass before after l r col low := by
  have left:=aperture_values m reg l _ _ _ a leftGeo sites capFit
  have right:=aperture_values m reg r _ _ _ b rightGeo sites capFit
  have wins:=overlap_words m reg pass before after l r col low a b capFit L R addFit
  refine ⟨?_,?_,?_,wins.1,wins.2⟩
  · intro side i j
    cases side <;> first | exact left.1 i j | exact right.1 i j
  · intro side i shift
    cases side <;> first | exact left.2.1 i shift | exact right.2.1 i shift
  · intro side i
    cases side <;> first | exact left.2.2 i | exact right.2.2 i

end Hierarchy.ProtocolRAM.SiteControls

end
end OAI
