import OAI.Hierarchy.DescentDatedDenseRankWord
import OAI.Hierarchy.DescentDatedSourcePathStride
import OAI.Hierarchy.DescentOrdinaryRankBanks
import OAI.Hierarchy.DescentSharedLeafImage
import OAI.Hierarchy.DescentSignedPrefixInvoice

namespace OAI
/-! # Broadcast the dense, distinct-host halo rank of a genuine selected four-walk -/
namespace Hierarchy.DescentDatedSourcePathDirectory.Local
open DescentDatedSourcePathDirectory DescentPackedZip DescentSIMDLookup DescentHaloWalkRAM
open DescentSharedCableNames DescentDatedAddressBook DescentSixParty.Chronology DescentPackedFlowBatch
open DescentSharedLeafLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D H G K M w : ℕ}
local notation "P" => breadth D
abbrev Directory := DescentOrdinaryDonorRankDirectory.Banks

def entry (B : Directory) (H : ℕ) (p : Fin P) : Expr :=
  Dense.expr B.endpoints H p

def token (R : Fin H→Fin D→Option (Fin H)) (h : Fin H) (p : Fin P) : Cell (Packed.bits P) :=
  Dense.value (Gather.reaching R) h p

theorem token_dense_at (R : Fin H→Fin D→Option (Fin H)) (h u : Fin H) (p s : Fin P)
    (raw : Gather.select (Gather.reaching R) h p=some u)
    (sorted : DescentSortedRoster.indexed (Gather.reaching R) h s=some u) :
    (token R h p).val=s.val+1 :=Dense.at_sorted _ _ _ _ _ raw sorted

theorem entry_fits (B : Directory) {base : ℕ} (fit : B.endpoints.Fits w base) (p : Fin P) :
    (entry B H p).Fits w base :=Dense.fits _ fit _

theorem entry_work (B : Directory) (H : ℕ) (p : Fin P) :
    (entry B H p).work≤(P+1)*(30+4*P+4*(P*P)) :=Dense.work _ _

def job (B : Directory) (H D : ℕ) : SignedPrefix.Job :=
  .columns (breadth D) H (stride H) (fun i=>if live:i<breadth D then entry B H ⟨i,live⟩ else .lit 0)
def stop (base H D : ℕ) :=base+breadth D*stride H
def bank (base H : ℕ) (p : Fin P) : Bank :=⟨base+p.val*stride H,Nat.clog 2 H⟩
def chart (repeatBase base H G M : ℕ) (p : Fin P) :=
  Public.header repeatBase H G M (Packed.bits P) (bank base H p)

structure Accessible (B : Directory) (H D w base : ℕ) : Prop where
  ep : B.endpoints.Fits w base
  rk : B.localRank.Fits w base
  visits : H*breadth D≤B.endpoints.size
  ranks : H*breadth D≤B.localRank.size
  sentinel : H<2^w

theorem reads (B : Directory) (base : ℕ) (A : Accessible B H D w base) (R : Fin H → Fin D → Option (Fin H))
    (m : Memory w) (old : DescentOrdinaryDonorRankDirectory.Reads R B m) (h : Fin H) (p : Fin P) :
    (entry B H p).eval m (h.val:Word w)=((token R h p).val:Word w) := by
  exact Dense.reads B.endpoints A.ep A.visits A.sentinel m (Gather.reaching R) old.visit h p

theorem measured (B : Directory) (base : ℕ) (A : Accessible B H D w base) (R : Fin H → Fin D → Option (Fin H))
    (m : Memory w) (old : DescentOrdinaryDonorRankDirectory.Reads R B m) (room : stop base H D<2^w) :
    let run:=(job B H D).atBase base w
    run.Runs m ∧ (∀(p : Fin P) (h : Fin H),run.image m ((bank base H p).base+h.val)=((token R h p).val:Word w)) ∧
      (∀i,i<base ∨ stop base H D≤ i → run.image m i=m i) := by
  intro run
  let col:=fun i=>if v:i<P then entry B H ⟨i,v⟩ else (.lit 0:Expr)
  have good (i : ℕ) (hi : i<P) : (col i).Fits w base :=by
    simp only [col,dite_eq_left hi]
    exact entry_fits B A.ep _
  have fits:H≤ stride H:=Nat.le_pow_clog (by decide) _
  have issued:=execute base H (stride H) P col m good room fits
  have frame:=SignedPrefix.Job.any (job B H D) base m ⟨fits,good⟩ room
  refine ⟨issued.1,?_,frame.2⟩
  intro p h
  exact (issued.2.1 p h).trans (by simpa only [col,dite_eq_left p.isLt] using reads B base A R m old h p)

theorem cost (B : Directory) (base H D w : ℕ) :
    let j:=job B H D
    (j.atBase base w).ticks≤j.clocks ((breadth D+1)*(30+4*breadth D+4*(breadth D*breadth D))) ∧
      DescentStaticWordColumn.names (j.atBase base w).program≤j.textSize ((breadth D+1)*(30+4*breadth D+4*(breadth D*breadth D))) :=by
  apply SignedPrefix.Job.invoice
  intro i hi
  simpa only [job,dite_eq_left hi] using entry_work B H (⟨i,hi⟩:Fin (breadth D))

end
end Hierarchy.DescentDatedSourcePathDirectory.Local

end OAI
