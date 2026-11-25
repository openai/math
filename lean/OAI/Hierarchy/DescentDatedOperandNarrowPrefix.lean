import OAI.Hierarchy.DescentDatedOperandNarrowRead

namespace OAI
/-! # Executing both narrow families from the same original retentive halo directory -/
namespace Hierarchy.DescentDatedSourcePathDirectory
open DescentPackedZip DescentSIMDLookup DescentHaloWalkRAM DescentSharedCableNames
open DescentSixParty.Chronology DescentSharedLeafLookup DescentDatedAddressBook
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D H G M w : ℕ}
local notation "P" => breadth D

def narrowPrefix (B : Banks) (rank : Local.Directory) (base H G M D w : ℕ) : NativePhase w :=
  (allPages B base H G M D w).seq ((Local.job rank H D).atBase (stop base H G M D) w)

theorem narrow_prefix_at_rank (B : Banks) (rank : Local.Directory) (base : ℕ) (R : Fin H → Fin D → Option (Fin H))
    (m : Memory w) (fit : Fits B H P base w)
    (fitRank : Local.Accessible rank H D w (stop base H G M D))
    (seen : Reads B (Gather.reaching R) m) (old : DescentOrdinaryDonorRankDirectory.Reads R rank ((allPages B base H G M D w).image m))
    (room : Local.stop (stop base H G M D) H D<2^w) :
    let atRank:=stop base H G M D
    let final:=Local.stop atRank H D
    let program:=narrowPrefix B rank base H G M D w
    program.Runs m ∧ (∀i,i<base ∨ final ≤ i→program.image m i=m i) ∧
      (∀(p : Fin P) (d : Fin (D+1)),
        Fixed (chart base H G M p d) 1 H G M (Packed.bits P) (program.image m) ∧
        ∀h : Fin H,program.image m ((hostBank base H p d).base+h.val)=
          (value (Gather.reaching R) h p (shortPath d):Word w)) ∧
      ∀p : Fin P, let hdr:=Local.chart (hostEnd base H D) atRank H G M p
        Readable hdr 1 H G M (Packed.bits P) w final ∧ Fixed hdr 1 H G M (Packed.bits P) (program.image m) ∧
          ∀h : Fin H,program.image m ((Local.bank atRank H p).base+h.val)=((Local.token R h p).val:Word w) :=by
  intro atRank final program
  let first:=allPages B base H G M D w
  let second:=(Local.job rank H D).atBase atRank w
  let mid:=first.image m
  let n:=second.image mid
  have low : base≤atRank:=(Nat.le_add_right ..).trans (end_le base H G M D)
  have top : atRank≤final:=Nat.le_add_right ..
  have small:=top.trans_lt room
  have prior:=all_issued B base fit small R m seen
  have ranks:=Local.measured rank atRank fitRank R mid old room
  have path (p : Fin P) (d : Fin (D+1)) :
      Fixed (chart base H G M p d) 1 H G M (Packed.bits P) n ∧
      ∀h : Fin H,n ((hostBank base H p d).base+h.val)=(value (Gather.reaching R) h p (shortPath d):Word w) :=by
    have geo:=geometry base p d small
    have fixed:=saved_header _ geo (prior.2.2 p d).1 (fun i hi=>ranks.2.2 i (.inl hi))
    refine ⟨fixed,?_⟩
    intro h
    have inside:h.val<(hostBank base H p d).size:=h.isLt.trans_le (Nat.le_pow_clog (by decide) _)
    have before:(hostBank base H p d).base+h.val<atRank:=
      (Nat.add_lt_add_left inside _).trans_le (geo.fit (hostBank base H p d) (by simp [chart,Public.header])).2.2
    exact (ranks.2.2 _ (.inl before)).trans ((prior.2.2 p d).2 h)
  refine ⟨NativePhase.seq_runs first second m prior.1 ranks.1,?_,path,?_⟩
  · intro i hi
    exact (ranks.2.2 i (hi.imp_left (fun h=>h.trans_le low))).trans
      (prior.2.1 i (hi.imp_right (fun h=>top.trans h)))
  · intro p
    have shared:=Local.shared base p (0:Fin (D+1)) room n (path p 0).1
    exact ⟨shared.1,shared.2,ranks.2.1 p⟩

theorem narrow_prefix_issued (B : Banks) (rank : Local.Directory) (base : ℕ) (R : Fin H → Fin D → Option (Fin H))
    (m : Memory w) (fit : Fits B H P base w)
    (fitRank : DescentOrdinaryDonorRankDirectory.Fits rank base H P w)
    (seen : Reads B (Gather.reaching R) m) (old : DescentOrdinaryDonorRankDirectory.Reads R rank m)
    (room : Local.stop (stop base H G M D) H D<2^w) :
    let atRank:=stop base H G M D
    let final:=Local.stop atRank H D
    let program:=narrowPrefix B rank base H G M D w
    program.Runs m ∧ (∀i,i<base ∨ final ≤ i→program.image m i=m i) ∧
      (∀(p : Fin P) (d : Fin (D+1)),
        Fixed (chart base H G M p d) 1 H G M (Packed.bits P) (program.image m) ∧
        ∀h : Fin H,program.image m ((hostBank base H p d).base+h.val)=
          (value (Gather.reaching R) h p (shortPath d):Word w)) ∧
      ∀p : Fin P, let hdr:=Local.chart (hostEnd base H D) atRank H G M p
        Readable hdr 1 H G M (Packed.bits P) w final ∧ Fixed hdr 1 H G M (Packed.bits P) (program.image m) ∧
          ∀h : Fin H,program.image m ((Local.bank atRank H p).base+h.val)=((Local.token R h p).val:Word w) :=by
  let high:=stop base H G M D
  have low : base≤high:=(Nat.le_add_right ..).trans (end_le base H G M D)
  have path:=all_issued B base fit ((show high≤Local.stop high H D from Nat.le_add_right ..).trans_lt room) R m seen
  have kept:=saved_directory R rank fitRank old (fun i hi=>path.2.1 i (.inl hi))
  have lift {b : Bank} (h : b.Fits w base) : b.Fits w high:=⟨h.1,h.2.1,h.2.2.trans low⟩
  exact narrow_prefix_at_rank B rank base R m fit
    ⟨lift fitRank.endpoints,lift fitRank.localFit,fitRank.endpointsSize,fitRank.localSize,fitRank.sentinel⟩ seen kept room

end
end Hierarchy.DescentDatedSourcePathDirectory

end OAI
