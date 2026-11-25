import OAI.Hierarchy.TaggedWirePacketBanks
import OAI.Hierarchy.TaggedWirePacketGatheredCost

namespace OAI
/-! # The positive original neighbor bucket named by a signed socket -/
noncomputable section
namespace Hierarchy.WireTelescope.PacketNeighbor
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM PacketTurns Tagged
open scoped Classical Fin.CommRing
variable {S D K W out B : ℕ} {s : Fin S} {total : (portGraph S).Port s→ℕ}
variable (parts : PassiveWindow.Parts ((portGraph S).Port s) (Fin D) K total)
    (width nbr : Fin D→Expr) (mem : Memory W) (row : Word W)
    (read : NeighborReads mem row parts width nbr)

theorem vacant_index (target : Fin S)
    (vacant : ∀q p,parts.owner q=some p→0<parts.width q→ other p≠target) :
    index parts target=D := by
  let xs:=List.ofFn (fun q=>word parts q target)
  have miss : 1∉xs := by
    intro used
    obtain ⟨q,h⟩:=List.mem_ofFn.mp used
    obtain ⟨p,own,on,same⟩:=(word_one parts q target).mp h
    exact vacant q p own on same
  simpa only [index,xs,List.length_ofFn] using List.idxOf_eq_length_iff.mpr miss

include read in
theorem key_read (seek : Expr) (target : Fin S) (room : S≤2^W)
    (located : seek.eval mem row=(target.val:Word W)) :
    (selectExpr width nbr seek).eval mem row=(index parts target:Word W) :=
  select_eval parts width nbr seek target mem row read.one room located read.fits read.widthAt read.siteAt

theorem key_positive (p : (portGraph S).Port s) (on : 0<total p) :
    ∃q:Fin D,q.val=index parts (other p) ∧ parts.owner q=some p ∧ 0<parts.width q :=
  found_live parts p on

theorem key_empty (p : (portGraph S).Port s) (empty : total p=0) : index parts (other p)=D := by
  apply vacant_index
  intro q p' own live same
  have eq:=other_injective same
  have bound:=parts.top q p' own
  rw [eq,empty] at bound
  omega

theorem key_fits (seek : Expr) (small : seek.Fits W out)
    (wf : ∀q,(width q).Fits W out) (nf : ∀q,(nbr q).Fits W out) :
    (selectExpr width nbr seek).Fits W out :=
  (Operands.neighbor_fits (n:=0) width nbr wf nf seek small).2

theorem key_work (seek : Expr) (small : seek.work≤B)
    (wf : ∀q,(width q).work≤B) (nf : ∀q,(nbr q).work≤B) :
    (selectExpr width nbr seek).work≤PacketScan.firstWork D (3*B+7) := by
  have cost:=Operands.gathered_sector_work (n:=0) width nbr wf nf seek small
  simp only [Operands.neighborSector,PacketScan.add,Expr.work] at cost
  omega

end Hierarchy.WireTelescope.PacketNeighbor

end
end OAI
