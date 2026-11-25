import OAI.Hierarchy.DescentDatedSourcePathStride
import OAI.Hierarchy.DescentDatedSourcePathHeaders
import OAI.Hierarchy.DescentSignedPrefixInvoice
import OAI.Hierarchy.DescentActorHeaderBroadcast
import OAI.Hierarchy.DescentOrdinaryMaterialRoute

namespace OAI
/-! # Emit all old-source addresses once per rack and broadcast only the short result -/
namespace Hierarchy.DescentDatedSourcePathDirectory
open DescentSIMDLookup DescentPackedZip DescentHaloWalkRAM DescentSharedCableNames
open DescentDatedAddressBook DescentSixParty.Chronology DescentPackedFlowBatch
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {D H G K M w : ℕ}
local notation "P" => breadth D
local notation "Q" => P*(D+1)

def pairIndex (p : Fin P) (d : Fin (D+1)) : Fin Q := finProdFinEquiv (p,d)
def columns (B : Banks) (H D i : ℕ) : Expr :=
  if h : i<breadth D*(D+1) then
    let j : Fin (breadth D) × Fin (D+1):=finProdFinEquiv.symm ⟨i,h⟩
    body B H j.1 (shortPath j.2)
  else .lit 0

def hostJob (B : Banks) (H D : ℕ) : SignedPrefix.Job :=
  .columns (breadth D*(D+1)) H (stride H) (columns B H D)
def hostEnd (base H D : ℕ) := base+(breadth D*(D+1))*stride H
def hostBank (base H : ℕ) (p : Fin P) (d : Fin (D+1)) : Bank :=
  ⟨base+(pairIndex p d).val*stride H,Nat.clog 2 H⟩

theorem column_at (B : Banks) (H : ℕ) (p : Fin P) (d : Fin (D+1)) :
    columns B H D (pairIndex p d).val=body B H p (shortPath d) := by
  rw [columns, dite_eq_left (pairIndex p d).isLt]
  change body B H (finProdFinEquiv.symm (finProdFinEquiv (p,d))).1
    (shortPath (finProdFinEquiv.symm (finProdFinEquiv (p,d))).2)=_
  rw [Equiv.symm_apply_apply]

theorem host_issued (B : Banks) (base : ℕ) (fit : Fits B H P base w) (space : hostEnd base H D<2^w)
    (R : Fin H → Fin D → Option (Fin H)) (m : Memory w) (data : Reads B (Gather.reaching R) m) :
    let phase:=(hostJob B H D).atBase base w
    phase.Runs m ∧ (∀p d v,phase.image m ((hostBank base H p d).base+v.val)=
      (value (Gather.reaching R) v p (shortPath d):Word w)) ∧
      (∀i,i<base ∨ hostEnd base H D≤ i → phase.image m i=m i) := by
  have room : H≤ stride H:=Nat.le_pow_clog (by decide) _
  have good (j : ℕ) (yes : j<Q) : (columns B H D j).Fits w base := by
    rw [columns,dite_eq_left yes]
    apply body_fits B fit
  have ran:=execute base H (stride H) Q (columns B H D) m good space room
  have frame:=SignedPrefix.Job.any (hostJob B H D) base m ⟨room,good⟩ space
  refine ⟨ran.1,?_,frame.2⟩
  intro p d v
  exact (ran.2.1 (pairIndex p d) v).trans (by rw [column_at];exact body_at B fit _ m data v p (shortPath d))

theorem host_cost (B : Banks) (H D base w : ℕ) :
    let cost:=(breadth D+1)*(30+4*breadth D+4*(breadth D*breadth D))
    let job:=hostJob B H D
    (job.atBase base w).ticks≤job.clocks cost ∧
      DescentStaticWordColumn.names (job.atBase base w).program≤job.textSize cost := by
  apply SignedPrefix.Job.invoice
  intro i hi
  simp only [columns,dite_eq_left hi]
  exact body_work ..

def token (R : Fin H → Fin D → Option (Fin H)) (v : Fin H) (p : Fin P) (d : Fin (D+1)) :
    Cell (Packed.bits P) :=
  ⟨value (Gather.reaching R) v p (shortPath d),
    (Nat.lt_succ_of_le (value_le _ _ _ _)).trans_le (Nat.le_pow_clog (by decide) (P+1))⟩

/-- The original host map can simultaneously lift the emitted scalar slot to
every active successor group. Partial last words and absent high racks are
handled by the original broadcast ROM and projection, respectively. -/
theorem source (base : ℕ) (p : Fin P) (d : Fin (D+1)) (R : Fin H → Fin D → Option (Fin H))
    (m : Memory w) (out pitch : ℕ) (hdr : DescentSharedLeafLookup.Header) (mapB : Bank)
    (same : hdr.ranks=hostBank base H p d)
    (ready : DescentSharedLeafLookup.Readable hdr 1 H G M (Packed.bits P) w out)
    (fixed : DescentSharedLeafLookup.Fixed hdr 1 H G M (Packed.bits P) m)
    (data : ∀v:Fin H,m ((hostBank base H p d).base+v.val)=(value (Gather.reaching R) v p (shortPath d):Word w))
    (mapFit : mapB.Fits w out) (mapRoom : K*chunks G M≤ mapB.size) (safe : H*chunks G M<2^w)
    (ix : ∀j : Row K G M,m (mapB.base+(row K G M j).val)=(DescentRawCablePanel.DepotRAM.Material.Route.index H pitch j:Word w)) :
    Source (DescentRawCablePanel.DepotRAM.Material.Route.lift mapB (H*chunks G M) (DescentSharedLeafLookup.source hdr (0:Fin 1)))
      (fun (h : Fin K) (_ : Fin G)=>(DescentRawCablePanel.DepotRAM.Material.Route.receiver H pitch h).elim 0
        (fun v=>token R v p d)) M m := by
  have original:=DescentActorRaster.Headers.broadcast_header out hdr m (fun v=>token R v p d) ready fixed
    (fun v=>by rw [same];exact data v)
  exact DescentRawCablePanel.DepotRAM.Material.Route.routed mapB pitch out m _ _ original mapFit mapRoom safe ix

end
end Hierarchy.DescentDatedSourcePathDirectory

end OAI
