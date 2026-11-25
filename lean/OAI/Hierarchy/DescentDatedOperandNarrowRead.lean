import OAI.Hierarchy.DescentDatedLocalRankPages

namespace OAI
/-! # The earlier path and private rank share a single original physical broadcast -/
namespace Hierarchy.DescentDatedSourcePathDirectory
open DescentPackedZip DescentSIMDLookup DescentHaloWalkRAM DescentSharedCableNames
open DescentSixParty.Chronology DescentSharedLeafLookup DescentDatedAddressBook
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D H K G M w b : ℕ}
local notation "P" => breadth D

private theorem saved_word {lo : ℕ} {m n : Memory w} (kept : ∀i,i<lo→n i=m i) (B : Bank)
    (fit : B.Fits w lo) {i : ℕ} (inside : i<B.size) : n (B.base+i)=m (B.base+i) :=
  kept _ ((Nat.add_lt_add_left inside _).trans_le fit.2.2)

theorem saved_header (hdr : Header) {out : ℕ} {m n : Memory w}
    (ready : Readable hdr 1 H G M b w out) (fixed : Fixed hdr 1 H G M b m)
    (kept : ∀i,i<out→n i=m i) : Fixed hdr 1 H G M b n :=by
  refine ⟨fun r=>?_,fun r=>?_,fun i x=>?_⟩
  · exact (saved_word kept _ (ready.fit _ (by simp)) ((row H G M r).isLt.trans_le ready.starts)).trans (fixed.start r)
  · exact (saved_word kept _ (ready.fit _ (by simp)) ((row H G M r).isLt.trans_le ready.cuts)).trans (fixed.cut r)
  · have size : repeatAddr i x<(M+1)*2^b :=by
      change i.val*2^b+x.val<_
      exact (Nat.add_lt_add_left x.isLt _).trans_le (by rw [←Nat.succ_mul]; exact Nat.mul_le_mul_right _ i.isLt)
    exact (saved_word kept _ (ready.fit _ (by simp)) (size.trans_le ready.repeats)).trans (fixed.broadcast i x)

theorem saved_directory (R : Fin H → Fin D → Option (Fin H)) (B : Local.Directory) {lo : ℕ} {m n : Memory w}
    (fit : DescentOrdinaryDonorRankDirectory.Fits B lo H P w)
    (old : DescentOrdinaryDonorRankDirectory.Reads R B m) (kept : ∀i,i<lo→n i=m i) :
    DescentOrdinaryDonorRankDirectory.Reads R B n :=
  ⟨fun h p=>(saved_word kept _ fit.endpoints ((Ranks.id h p).isLt.trans_le fit.endpointsSize)).trans (old.visit h p),
   fun h p q=>(saved_word kept _ fit.previous ((Ranks.id h (PairRanks.pair p q)).isLt.trans_le fit.previousSize)).trans (old.prev h p q),
   fun h p q=>(saved_word kept _ fit.suffix ((Ranks.id h (PairRanks.pair p q)).isLt.trans_le fit.suffixSize)).trans (old.suffix h p q),
   fun h=>(saved_word kept _ fit.offset (h.isLt.trans_le fit.offsetSize)).trans (old.offset h),
   fun h p=>(saved_word kept _ fit.reverse ((Ranks.id h p).isLt.trans_le fit.reverseSize)).trans (old.reverse h p),
   fun h p=>(saved_word kept _ fit.localFit ((Ranks.id h p).isLt.trans_le fit.localSize)).trans (old.localValue h p),
   fun h p q=>(saved_word kept _ fit.shared ((Ranks.id h (PairRanks.pair p q)).isLt.trans_le fit.sharedSize)).trans (old.shared h p q)⟩

theorem Local.placed (base : ℕ) (p : Fin P) (space : Local.stop base H D<2^w) :
    (Local.bank base H p).Fits w (Local.stop base H D) ∧ H≤(Local.bank base H p).size :=by
  have index:=Nat.mul_le_mul_right (stride H) p.isLt
  rw [Nat.succ_mul] at index
  have hi:(Local.bank base H p).base+(Local.bank base H p).size≤Local.stop base H D:=by
    change base+p.val*stride H+stride H≤base+P*stride H
    omega
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (hi.trans_lt space),hi⟩,Nat.le_pow_clog (by decide) _⟩

private theorem later_bank {B : Bank} {x y : ℕ} (up : x≤y) (old : B.Fits w x) : B.Fits w y :=
  ⟨old.1,old.2.1,old.2.2.trans up⟩

theorem Local.shared_geometry (pathBase : ℕ) (p : Fin P) (d : Fin (D+1))
    (room : Local.stop (DescentDatedSourcePathDirectory.stop pathBase H G M D) H D<2^w) :
    Readable (Local.chart (hostEnd pathBase H D) (DescentDatedSourcePathDirectory.stop pathBase H G M D) H G M p)
      1 H G M (Packed.bits P) w (Local.stop (DescentDatedSourcePathDirectory.stop pathBase H G M D) H D) :=by
  let base:=DescentDatedSourcePathDirectory.stop pathBase H G M D
  have up : base≤Local.stop base H D:=Nat.le_add_right ..
  have before:=DescentDatedSourcePathDirectory.geometry pathBase p d (up.trans_lt room)
  have after:=Local.placed base p room
  refine ⟨?_,by simpa only [base,Local.chart,Public.header,Nat.mul_one] using after.2,before.starts,before.cuts,before.repeats⟩
  intro bank member
  simp only [Local.chart,Public.header,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl
  · exact after.1
  all_goals apply later_bank up; apply before.fit; simp [DescentDatedSourcePathDirectory.chart,Public.header]

/-- The kept path chart and the new private-rank chart differ only in their
rank bank. Both use the start/cut/broadcast pages physically printed earlier. -/
theorem Local.shared (pathBase : ℕ) (p : Fin P) (d : Fin (D+1))
    (room : Local.stop (DescentDatedSourcePathDirectory.stop pathBase H G M D) H D<2^w) (m : Memory w)
    (fixed : Fixed (DescentDatedSourcePathDirectory.chart pathBase H G M p d) 1 H G M (Packed.bits P) m) :
    let base:=DescentDatedSourcePathDirectory.stop pathBase H G M D
    let hdr:=Local.chart (hostEnd pathBase H D) base H G M p
    Readable hdr 1 H G M (Packed.bits P) w (Local.stop base H D) ∧ Fixed hdr 1 H G M (Packed.bits P) m :=by
  intro base hdr
  exact ⟨Local.shared_geometry pathBase p d room,⟨fixed.start,fixed.cut,fixed.broadcast⟩⟩

theorem Local.source (pathBase : ℕ) (p : Fin P) (R : Fin H → Fin D → Option (Fin H))
    (m : Memory w) (out pitch : ℕ) (mapB : Bank)
    (ready : Readable (Local.chart (hostEnd pathBase H D) (DescentDatedSourcePathDirectory.stop pathBase H G M D) H G M p)
      1 H G M (Packed.bits P) w out)
    (fixed : Fixed (DescentDatedSourcePathDirectory.chart pathBase H G M p (0:Fin (D+1))) 1 H G M (Packed.bits P) m)
    (data : ∀h:Fin H,m ((Local.bank (DescentDatedSourcePathDirectory.stop pathBase H G M D) H p).base+h.val)=((Local.token R h p).val:Word w))
    (mapFit : mapB.Fits w out) (mapRoom : K*chunks G M ≤ mapB.size) (safe : H*chunks G M<2^w)
    (ix : ∀j : Row K G M,m (mapB.base+(row K G M j).val)=(DescentRawCablePanel.DepotRAM.Material.Route.index H pitch j:Word w)) :
    let hdr:=Local.chart (hostEnd pathBase H D) (DescentDatedSourcePathDirectory.stop pathBase H G M D) H G M p
    Source (DescentRawCablePanel.DepotRAM.Material.Route.lift mapB (H*chunks G M) (DescentSharedLeafLookup.source hdr (0:Fin 1)))
      (fun (h : Fin K) (_ : Fin G)=>(DescentRawCablePanel.DepotRAM.Material.Route.receiver H pitch h).elim 0
        (fun v=>Local.token R v p)) M m :=by
  intro hdr
  have mounted : Fixed hdr 1 H G M (Packed.bits P) m:=⟨fixed.start,fixed.cut,fixed.broadcast⟩
  have read:=DescentActorRaster.Headers.broadcast_header out hdr m (fun h=>Local.token R h p) ready mounted data
  exact DescentRawCablePanel.DepotRAM.Material.Route.routed mapB pitch out m _ _ read mapFit mapRoom safe ix

end
end Hierarchy.DescentDatedSourcePathDirectory

end OAI
