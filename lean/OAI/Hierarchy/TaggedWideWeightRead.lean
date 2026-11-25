import OAI.Hierarchy.TaggedWirePacketNeighbor
import OAI.Hierarchy.TaggedWideControlOperands
import OAI.Hierarchy.TaggedWideChordAperture

namespace OAI
/-! # Native width, start and length fields for each fixed per-site comparison -/

noncomputable section
namespace Hierarchy.ProtocolRAM.SiteControls
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr
open LinearAlgebra.SpectralBooks ChordGraph
open ProbeStage.CoreBoard.HistoryRoles WireTelescope Tagged PassiveWindow
open scoped Classical Fin.CommRing BigOperators

variable {D S W cap : ℕ} {s : Fin S} {t : (portGraph S).Port s→ℕ}
    (o : Parts ((portGraph S).Port s) (Fin D) cap t) (row : Fin D→LocalPrefix.Columns)
    (m : Memory W) (r : Word W)
    (reads : PacketTurns.NeighborReads m r o (fun i=>(row i).width) (fun i=>(row i).opposite))
    (sites : S≤2^W)
    (owned : ∀i,(o.owner i).isSome=true ↔ 0<o.width i)
    (vacant : ∀i,o.owner i=none → o.width i=0)

include reads sites owned vacant in
theorem weight_read (i j : Fin D) :
    (weight (row i) (row j)).eval m r=((ChordAperture.sizeAt o i j).val : Word W) := by
  have same (a b : Fin S) : (a.val:Word W)=(b.val:Word W) ↔ a=b := by
    constructor
    · intro eq
      apply Fin.ext
      simpa [Fin.val_cast_of_lt (a.isLt.trans_le sites),Fin.val_cast_of_lt (b.isLt.trans_le sites)]
        using congrArg Fin.val eq
    · rintro rfl
      rfl
  have widthAt (a : Fin D) : (row a).width.eval m r=(o.width a:Word W) := by
    rw [reads.widthAt]
    cases hit:o.owner a with
    | none=>rw [vacant a hit];simp [PacketNeighbor.amount,hit]
    | some p=>simp [PacketNeighbor.amount,hit]
  have positive (a : Fin D) (p) (h : o.owner a=some p) : 0<o.width a :=
    (owned a).mp (by simp [h])
  have ne (a : Fin D) (p) (h : o.owner a=some p) : (o.width a:Word W)≠0 := by
    have top := reads.fits a
    have pos:=positive a p h
    simp only [PacketNeighbor.amount,h,Option.elim_some] at top
    exact fun e=>by have := congrArg Fin.val e; simp [Fin.val_cast_of_lt top] at this;omega
  cases hi:o.owner i with
  | none=>simp [weight,active,Expr.eval,Comparison.test,widthAt,vacant i hi,ChordAperture.sizeAt,
      ChordAperture.code,hi]
  | some p=>
    cases hj:o.owner j with
    | none=>simp [weight,active,Expr.eval,Comparison.test,widthAt,vacant j hj,ChordAperture.sizeAt,
        ChordAperture.code,hj]
    | some q=>
      have eqPeer : (row i).opposite.eval m r=(row j).opposite.eval m r ↔ p=q := by
        rw [reads.siteAt i p hi (positive i p hi),reads.siteAt j q hj (positive j q hj),same,
          PacketNeighbor.other_injective.eq_iff]
      have code : ChordAperture.code o i j ↔ p=q := by
        constructor
        · rintro ⟨v,left,right⟩
          exact (Option.some.inj (hi.symm.trans left)).trans (Option.some.inj (hj.symm.trans right)).symm
        · intro eq
          exact ⟨p,hi,hj.trans (congrArg some eq.symm)⟩
      have activeAt : (row j).width.eval m r≠0 := by rw [widthAt]; exact ne j q hj
      by_cases eq : p=q
      · have samePeer:=eqPeer.mpr eq
        have sameCode:=code.mpr eq
        simp [weight,active,Expr.eval,Comparison.test,activeAt,samePeer,ChordAperture.sizeAt,sameCode,widthAt i]
      · have diffPeer:=mt eqPeer.mp eq
        have diffCode:=mt code.mp eq
        simp [weight,active,Expr.eval,Comparison.test,activeAt,diffPeer,ChordAperture.sizeAt,diffCode]

end Hierarchy.ProtocolRAM.SiteControls

end
end OAI
