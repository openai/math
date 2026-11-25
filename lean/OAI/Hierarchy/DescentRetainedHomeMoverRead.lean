import OAI.Hierarchy.DescentRetainedHomeMover
import OAI.Hierarchy.DescentRetainedTargetPlacementRead

namespace OAI
/-! # Read the filtered previous primitive word after the date's actual target compaction -/
namespace Hierarchy.DescentRetainedHomeMover.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentGL DescentColonies
open DescentSixParty.PackedFlow.Channels DescentResetRetainedSetup DescentSixParty.Chronology
open DescentOrdinaryAtomFieldRAM DescentRetainedControl
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (z : DescentRetainedHomeMover.Layout) {w U : ℕ}
set_option quotPrecheck false
local notation "v" => z.transfer
local notation "s" => z.control
local notation "P" => z.placement
variable (floor : ℕ) (prev : Fin z.transfer.blocks→Bank) (key count inverse : Bank) (which : Fin z.shapes→Option ℕ) (packet : Expr)
local notation "lo" => z.controlBase floor
local notation "mid" => z.bookBase floor
local notation "hi" => z.placementBase floor

def oldStrips (size : 2^((v).high+(v).low)=(v).groups*(v).blocks) (cut : (v).cut≤(v).high+(v).low)
    (L : DescentGL.Layout ((v).high+(v).low)) (X : Fin (v).blocks→Fin (v).hosts→Fin (v).groups→Cell (v).wholeWord)
    (j : Fin (v).channels) (h : Fin (v).hosts) (g : Fin (v).grouped) :=blockValues cut ((v).before size (z.toLayout.priorValues X) j) L h g

def targetInputs (Y : Fin (v).hosts→Fin (v).grouped→Cell (s).rootWidth)
    (rows : Fin (v).channels→Fin (v).hosts→Fin (v).grouped→Cell (v).stripWord)
    (i : Fin ((v).nodes*z.shapes)) (h : Fin (v).hosts) (g : Fin (v).grouped) :=
  let p : Fin (v).nodes×Fin z.shapes:=finProdFinEquiv.symm i
  let ctrl:=filter (D:=z.degree) (L:=(v).donors) (cap:=z.cap) (which p.2) (Y h g)
  z.role p.1 (fun j=>take (v).bits ctrl (rows j h g))

theorem issued (m : Memory w) (r : z.Room floor prev key count inverse packet w)
    (size : 2^((v).high+(v).low)=(v).groups*(v).blocks) (batch : 2^(v).low=(v).gatherLanes*(v).blocks)
    (hg : 0<(v).gatherLanes) (hb : 0<(v).blocks) (hp : 0<(v).previousLanes) (cut : (v).cut≤(v).high+(v).low)
    (pitch : (v).matrixLanes*(v).donors=2^(v).low) (live : 0<(v).matrixLanes) (dec : 0<(v).decodedLanes)
    (root : 0<z.rootLanes) (L : DescentGL.Layout ((v).high+(v).low))
    (elected : m key.base=((DescentExterior.matrixCode L).val:Word w))
    (X : Fin (v).blocks→Fin (v).hosts→Fin (v).groups→Cell (v).wholeWord) (Y : Fin (v).hosts→Fin (v).grouped→Cell (s).rootWidth)
    (capacity : ∀j,(v).hosts*chunks (v).groups (v).previousLanes≤(prev j).size)
    (read : ∀j,Reads (prev j) (X j) (v).previousLanes m) (priorPacket : Source packet Y z.rootLanes m)
    (groups : z.groups*z.blocks=(v).grouped) (name : Fin U→Fin (P).sparse)
    (cnt : m count.base=(U:Word w)) (inv : ∀i:Fin U,m (inverse.base+i.val)=((name i).val:Word w))
    (narrow : U<2^w) (hosts : z.newHosts≤2^w) (saved : U≤ inverse.size) (n : Fin (v).nodes) (x : Fin z.blocks) :
    Source (.lookup (z.bank floor n x) .row)
      (DescentRetainedTargetPlacement.Chart.compact (P) z.batch (z.kept which) name
        (fun i h g=>z.targetInputs which Y (z.oldStrips size cut L X) i h (g.cast groups)) n x)
      z.lanes (z.finalMem floor prev key count inverse which packet m):=by
  obtain ⟨a,b,c,d⟩:=z.bounds floor
  have high:=d.trans_lt r.roof
  have middle:=c.trans_lt high
  have low:=b.trans_lt middle
  have m₁:=(v).moved_any floor (z.prior prev) key m (fun j=>r.previous _) r.saved low
  let moving:=z.movedImage floor prev key m
  have fits:=ProtocolRAMGeneratedWrite.fits_mono _ a r.packetFit
  have win:Source packet Y z.rootLanes moving:=fun j=>(eval_below _ _ m moving r.packetFit (fun u hu=>m₁.2.1 u (.inl hu))).trans (priorPacket j)
  have m₂:=(s).any which lo packet moving fits middle
  have m₃:=DescentOperandFamilyBook.any z.role (v).decodedLanes mid (z.ordered floor prev key which packet m) high
  have before (j : ℕ) (past : j<floor) : z.prepared floor prev key which packet m j=m j:=
    (m₃.2.2.1 j (.inl (past.trans_le (a.trans b)))).trans ((m₂.2.2 j (.inl (past.trans_le a))).trans (m₁.2.1 j (.inl past)))
  let old:=z.oldStrips size cut L X
  have first:=(v).moved_reads floor (z.prior prev) key m (fun j=>r.previous _) r.saved low size batch hg hb hp cut pitch live L elected
    (z.toLayout.priorValues X) (fun j=>capacity _) (fun j=>read _)
  have ordered (t : Fin z.shapes) (j : Fin (v).channels) :
      Source (z.channels floor which t j) (fun h g=>take (v).bits
        (filter (D:=z.degree) (L:=(v).donors) (cap:=z.cap) (which t) (Y h g)) (old j h g)) (v).decodedLanes
        (z.ordered floor prev key which packet m):=by
    obtain ⟨held,amount⟩:=Strip.fits (w:=w) ((v).mixed floor) (v).hosts (v).grouped (v).matrixLanes (v).decodedLanes (v).stripWord j low
    have channel : Source (.lookup ((v).hostBank floor j) .row) (old j) (v).decodedLanes moving:=
      source_column _ _ held _ _ amount (first j)
    exact ((s).issued which lo packet moving fits middle root Y win t (.lookup ((v).hostBank floor j) .row) (.lit 0)
      ⟨held,trivial⟩ trivial (old j) (fun _ _=>0) channel (DescentPrimitiveBirth.zero _)).1
  have queried (i : Fin ((v).nodes*z.shapes)) : Source (z.query floor which i) (z.targetInputs which Y old i)
      (v).decodedLanes (z.prepared floor prev key which packet m):=by
    let q : Fin (v).nodes×Fin z.shapes:=finProdFinEquiv.symm i
    apply (DescentOperandFamilyBook.issued z.role z.role_zero (v).decodedLanes mid q.1 (z.channels floor which q.2)
      (z.ordered floor prev key which packet m) _ (z.channels_fit floor which r.roof q.2) (ordered q.2) high).2
  have bank {B : Bank} (rr : B.Fits w floor) : B.Fits w hi:=⟨rr.1,rr.2.1,rr.2.2.trans (a.trans (b.trans c))⟩
  apply DescentRetainedTargetPlacement.Chart.read (P) (z.batch) hi (z.kept which) (z.query floor which) count inverse
    (z.prepared floor prev key which packet m) r.lanes dec r.blocks (z.query_fit floor which r.roof) (bank r.countFit) (bank r.inverseFit)
    r.roof name ((before _ (by have pos:=r.countFit.1;have bound:=r.countFit.2.2;omega)).trans cnt)
    (fun i=>(before _ ((Nat.add_lt_add_left (i.isLt.trans_le saved) _).trans_le r.inverseFit.2.2)).trans (inv i))
    narrow hosts saved _ _ n x
  intro i
  have recast {G N H a M : ℕ} (size : G=N) (f : Fin H→Fin N→Cell a) (e : Expr)
      (memory : Memory w) (reads : Source e f M memory) :
      Source e (fun h g => f h (g.cast size)) M memory := by
    subst N
    exact reads
  exact recast groups (z.targetInputs which Y old i) _ _ (queried i)

end
end Hierarchy.DescentRetainedHomeMover.Layout

end OAI
