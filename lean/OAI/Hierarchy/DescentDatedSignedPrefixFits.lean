import OAI.Hierarchy.DescentDatedSignedReturnRoom

namespace OAI
/-! The precise chronological read window of every native date instruction.
Generated expressions only consult prior or already materialized banks. -/
namespace Hierarchy.DescentDatedAddressBook
open DescentSixParty.Chronology DescentParallelBase DescentSIMDLookup DescentPackedZip DescentPackedColony DescentDyadicSpan
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

private theorem every_job {w:ℕ} (base:ℕ) (js:List SignedPrefix.Job)
    (ok:∀i:Fin js.length,(js[i.val]).Fits (SignedPrefix.start base js i.val) w):SignedPrefix.Fits w js base:=by
  induction js generalizing base with
  | nil=>trivial
  | cons j js ih=>
    exact ⟨ok 0,ih (base+j.width) (fun i=>ok i.succ)⟩

namespace SignedExtent
variable (s:SignedExtent) (I:s.Input) (base:ℕ) {w:ℕ}
private theorem cut_start (j:Fin 21):SignedPrefix.start base (s.jobs I base) j.val=s.cuts base j.castSucc:=by
  fin_cases j <;> rfl

private theorem col_fitted {n rows base w:ℕ} (fn:Fin n→Expr) (fitted:∀i,(fn i).Fits w base):
    (col n rows (fromIndex fn)).Fits base w:=by
  refine ⟨span_ge _,?_⟩
  intro i h
  simpa only [fromIndex,dite_eq_left h] using fitted ⟨i,h⟩

private theorem indexed_fitted (e:Expr) (B:Bank) (sent stop:ℕ) (ptr:e.Fits w stop) (read:B.Fits w stop):
    (indexed e sent B).Fits w stop:=⟨ptr,trivial,trivial,read,ptr⟩

set_option maxHeartbeats 700000 in
theorem prefix_fits (ok:s.Prior I base w) (large:s.roof base+max s.slab s.oldSlab<2^w)
    (peer:(s.peerHeadExpr I base).Fits w (s.peerHeadOut base)):SignedPrefix.Fits w (s.jobs I base) base:=by
  have wide (j:Fin 22):s.cuts base j<2^w:=(Nat.le_add_right ..).trans_lt (s.clock_room base large j)
  have sy (j:Fin 22):s.cuts base j+s.slab<2^w:=(Nat.add_le_add_left (le_max_left ..) _).trans_lt (s.clock_room base large j)
  have so (j:Fin 22):s.cuts base j+s.oldSlab<2^w:=(Nat.add_le_add_left (le_max_right ..) _).trans_lt (s.clock_room base large j)
  have bank (j:Fin 5) (z:s.Socket): (s.rankPage base z j).Fits w (s.localStart base):=
    slice_fits (finProdFinEquiv (s.socketId z,j)) (s.cuts_mono base (by decide:(6:Fin 22)≤7)) (wide 7)
  have materials (z:s.Socket) (f:Fin 11):(s.donorField I base z f).Fits w (s.localStart base):=by
    have md (j:Fin 6):=(ProtocolRAMGeneratedWrite.fits_mono _ (s.cuts_mono base (by decide:(0:Fin 22)≤7)) (ok.material z j))
    have rd (j:Fin 5):(Expr.lookup (s.rankPage base z j) .row).Fits w (s.localStart base):=⟨bank j z,trivial⟩
    have both (i:Fin 5) (j:Fin 6): ((DescentOrdinaryDonorSources.ROM.table (s.peerStart base) s.lowSites s.fieldBits s.lanes).read
        (.lookup (s.rankPage base z i) .row) (I.donor z j)).Fits w (s.localStart base):=by
      have r:=s.donor_room base I z i j 7 le_rfl (ok.material _ _) (wide 7)
      exact ⟨r.apply,r.right,r.shift,r.left⟩
    fin_cases f
    · exact rd 0
    · exact md 0
    · exact rd 1
    · exact md 1
    · exact rd 2
    · exact md 2
    · exact both 3 0
    · exact both 4 1
    · exact md 3
    · exact md 4
    · exact md 5
  have turn (c:s.Consumer) (f:Fin 11):(s.routed I base c f).Fits w (s.returnedStart base):=by
    by_cases axis : c.1.2.val=2
    · simp only [routed,ite_eq_left axis]
      apply DescentColonies.SplitRAM.fits_total
      intro i
      have word:=s.traverse_room base I ok c f i _ le_rfl (so 12)
      exact ⟨word.apply,word.right,word.shift,word.left⟩
    · simp only [routed,ite_eq_right axis]
      trivial
  apply every_job
  intro j
  change Fin 21 at j
  rw [s.cut_start I base j]
  fin_cases j <;> first | trivial | skip
  · exact col_fitted _ (fun f=>s.rank_fitted base I ok (fieldIndex f))
  · apply col_fitted
    intro f
    have map:=s.map_room base _ (le_refl (s.viewBase base)) (wide 2)
    exact indexed_fitted _ _ _ _ ⟨map.normalize,trivial⟩
      (slice_fits f (s.cuts_mono base (by decide:(1:Fin 22)≤2)) (wide 2))
  · apply col_fitted
    intro r
    apply DescentPackedChildNeighbor.SIMD.fitted
    exact s.rank_room base I _ _ 5 le_rfl (ok.path _) (ok.endpoint _) (sy 5)
  · exact col_fitted _ (fun r=>materials _ _)
  · apply col_fitted
    intro r
    let p : Fin (s.sockets*11) × Fin s.lowSites := finProdFinEquiv.symm r
    have map:=s.map_room base _ (s.cuts_mono base (by decide:(2:Fin 22)≤8)) (wide 8)
    exact indexed_fitted _ _ _ _ ⟨map.transpose p.2,trivial⟩ (slice_fits p.1 le_rfl (wide 8))
  · exact col_fitted _ (fun _=>turn _ _)
  · exact ⟨span_ge _,fun _ _=>peer⟩

theorem fits_from_prior (ok:s.Prior I base w) (large:s.roof base+max s.slab s.oldSlab<2^w)
    (peer:(s.peerHeadExpr I base).Fits w (s.peerHeadOut base))
    (hdr:∀x j,((s.layout I base).header x j).Fits w (s.tailStart base))
    (flags:∀z,(s.flags I base z).Fits w (s.tailStart base)):s.Fits I base w:=by
  have room:s.tailStart base<2^w:=(Nat.le_add_right ..).trans_lt (s.clock_room base large 21)
  have words (c:s.Consumer) f:(s.operand I base c f).Fits w (s.tailStart base):=by
    have q:=s.gate_room I base ok c f (flags _) room
    exact ⟨q.apply,q.right,q.shift,q.left⟩
  exact ⟨s.prefix_fits I base ok large peer,hdr,fun _ _ _ _=>words _ _,fun _ _ _ _ _=>words _ _⟩

end SignedExtent
end
end Hierarchy.DescentDatedAddressBook

end OAI
