import OAI.Hierarchy.DescentResetActorPlanes
import OAI.Hierarchy.DescentReachedPaidRaster
import OAI.Hierarchy.DescentIssuedOrdinaryRaster
import OAI.Hierarchy.DescentVenueActorMask

namespace OAI
/-! # Both original coalesced actor rows in the padded successor geography -/
namespace Hierarchy.DescentLocalArchiveOrder
open DescentNetworkPartition Computability.BorderVNP.Crossing
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentCompiler DescentStageEdgeReceipt
open DescentCableDonorNames DescentOrdinaryLocalBirth DescentHostDegree DescentHostDirectory DescentOrdinaryDonorHalo
open DescentNetworkPartition Computability.BorderVNP.Crossing DescentSharedCableNames DescentSixParty.StarKeys
open DescentColonies DescentGL DescentWalshTables DescentPacking
open DescentGroupPeerOrder DescentPacking.PackedMatch.Local.Stage DescentSortedHaloRaster DescentHaloWalkRAM DescentSIMDLookup
open DescentScalarVenueMask DescentHostDirectory.SiteDecode DescentOrdinaryLocalBirth DescentSharedCableNames DescentPackedActorMask
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentScalarBookReshape
open scoped Classical Fin.CommRing
set_option quotPrecheck false
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {u q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (arch : Archive W)
local notation "r" => BitDescription.scannedRows he T
local notation "capV" => Fin (S.groupCount i)×cap.V
local notation "sw" => branchWidth G (fun _ : (r).pairs=>T.z) ((r).profile c)
local notation "stepGraph" => rawGraph he T c
local notation "sel" => scanWorld he T c
local notation "next" => (ticket.advance arch).bit
local notation "units" => fun _ : (r).pairs=>T.z
local notation "stageLimit" => fun _ : (r).pairs=>le_refl T.z
local notation "layout" => bestLayout sw
local notation "group" => GadgetNetwork.newSite W.graph (r).pick layout (r).pack

local notation "bookChart" => activeChart ticket
local notation "key" => (bookChart).key he T c
local notation "addr" => MarkedWorld.address sel key (bookChart).hub T.k (gainExponent 20 T.Δ)
local notation "C" => ↥(MarkedWorld.reclaimed sel key (bookChart).hub T.k (gainExponent 20 T.Δ))
local notation "venue" => addr ∘ group

local notation "A" => cap.placement
local notation "deg" => (A).degree
local notation "near" => groupedNear (A).near
local notation "bound" => DescentHaloWalkRAM.breadth deg*2^k
local notation "sites" => (A).site cap.vertex cap.valid.coordinates

local notation "roster" => hostRotor cap.vertex (hostRoster A (cap.vertex.trans Fin.valEmbedding))
local notation "reach" => Gather.reaching roster
local notation "halo" => reachedHalo ticket
local notation "name" => rackName (cap:=cap)

local notation "shelf"=>2^(packExponent 20 deg)+2
local notation "pitch"=>(2^(k+1)-1)*shelf
local notation "used"=>fun p:(r).pairs=>(r).picked (p,0)
local notation "oldID"=>cap.order.trans Fin.valEmbedding
local notation "origin"=>outgoingSlot A oldID S cap.valid (r).pick used
local notation "breadth"=>DescentHaloWalkRAM.breadth deg
local notation "ticketSlots"=>1+(A).cap*6
local notation "moves"=>rotor A (groupRank Fin.valEmbedding (cap.vertex.trans Fin.valEmbedding))

open DescentPaidResidentCount
variable {mb : ℕ}
variable (tokens : DescentColonies.Block k→Fin (1+cap.placement.cap*6)→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→
  DescentScalarVenueMask.Ticket (DescentHaloWalkRAM.breadth cap.placement.degree) (2^(k+1)*(2^(packExponent 20 cap.placement.degree)+2)))
local notation "physical" => DescentScalarVenueMask.fields reach tokens (flags (cap:=cap)) k (gainExponent 20 deg) shelf pitch
local notation "stock" => Descriptors shelf k (A).pos (A).block (ticketParent (he:=he) (T:=T)) (ticketSlot (c:=c) ticket)
  (key∘group) cap.vertex (Function.Embedding.refl _) moves tokens
local notation "oldCensus" => fun x h g=>Census.count A (Equiv.refl _) cap.vertex mb h g x
local notation "bookCounts" => DescentOrdinaryAtomFieldRAM.RoleCounts.priorValue reach oldCensus
local notation "cost" => fun u : W.graph.Site=>((A).records u).length
local notation "dest" => n.destination∘rawInput he T c ((r).state c)

local notation "OH" => Fintype.card cap.V
local notation "OG" => S.groupCount i
local notation "NH" => Fintype.card target.V
local notation "NG" => S.groupCount (i+1)
variable (age : i<S.length) (radix : S.radix=2^k)
local notation "digits" => S.groupDigits age radix
local notation "coord" => DescentPaidResidentCount.occupies target.placement (Equiv.refl _) target.vertex


open DescentOrdinaryRasterReturn DescentActorRaster DescentPackedZip DescentPackedColony
variable {R:ℕ}(newFit:Fintype.card target.V≤R)
local notation "names" => target.vertex.trans (Fin.castLEEmb newFit)


private theorem actual_cast (h:Fin R)(g:Fin NG)(x:DescentColonies.Block k):
    Venue.actual target.placement (Function.Embedding.refl _) names x h g=
    DescentOrdinaryRasterReturn.extend (fun v g=>if ∃u,coord v g x u then (1:Cell 1) else 0) h g:=by
  classical
  unfold Venue.actual DescentOrdinaryRasterReturn.extend DescentPaidResidentCount.occupies
  by_cases hv:h.val<NH
  · simp only [dite_eq_left hv]
    have eq_ (u:n.result.graph.Site):names (target.placement.pos u).2=h ↔
        target.vertex (target.placement.pos u).2=⟨h.val,hv⟩:=by rw [Fin.ext_iff,Fin.ext_iff];rfl
    simp only [eq_,Function.Embedding.refl_apply,Equiv.refl_apply]
    split <;> (rename_i hcase; simp [hcase])
  · have miss:¬∃u:n.result.graph.Site,names (target.placement.pos u).2=h ∧
        (target.placement.pos u).1=g ∧ target.placement.block u=x:=by
      rintro ⟨u,here,_⟩
      have low:(names (target.placement.pos u).2).val<NH:=(target.vertex (target.placement.pos u).2).isLt
      exact hv (here ▸ low)
    rw [dite_eq_right hv]
    exact ite_eq_right miss

def paddedBook {a:ℕ}(raw:Fin pitch→Fin OH→Fin OG→Cell a)(x:DescentColonies.Block k)(h:Fin R)(g:Fin NG):Cell a:=
  DescentOrdinaryRasterReturn.extend (fun v=>DescentScalarBookReshape.book (oldInput age radix raw) x v) h g

include tokens in
theorem paid_return (auth:stock)(precision:(A).wire*((A).z*G.b)*(A).cap<2^mb)(x:DescentColonies.Block k)(h:Fin R)(g:Fin NG):
    paddedBook (cap:=cap) age radix (paidRaster (mb:=mb) ticket tokens) x h g=
      Census.count target.placement (Equiv.refl _) names mb h g x:=by
  rw [padded_count target.placement (Equiv.refl _) target.vertex newFit]
  have count:NH=OH*pitch:=by rw [ticket.hostCount];ring
  by_cases live:h.val<NH
  · have included:h.val<OH*pitch:=count ▸ live
    change DescentOrdinaryRasterReturn.extend _ h g=_
    rw [DescentOrdinaryRasterReturn.extend,dite_eq_left included,DescentOrdinaryRasterReturn.extend,dite_eq_left live]
    exact paid_raster_book ticket tokens age radix auth precision ⟨h.val,live⟩ g x
  · have off:¬h.val<OH*pitch:=count ▸ live
    simp [paddedBook,DescentOrdinaryRasterReturn.extend,live,off]

include tokens in
theorem actor_return (auth:stock)(x:DescentColonies.Block k)(h:Fin R)(g:Fin NG):
    paddedBook (cap:=cap) age radix (actorRaster ticket tokens) x h g=
      Venue.actual target.placement (Function.Embedding.refl _) names x h g:=by
  rw [actual_cast (target:=target) newFit]
  have count:NH=OH*pitch:=by rw [ticket.hostCount];ring
  by_cases live:h.val<NH
  · have included:h.val<OH*pitch:=count ▸ live
    change DescentOrdinaryRasterReturn.extend _ h g=_
    rw [DescentOrdinaryRasterReturn.extend,dite_eq_left included,DescentOrdinaryRasterReturn.extend,dite_eq_left live]
    exact actor_raster_book ticket tokens age radix auth ⟨h.val,live⟩ g x
  · have off:¬h.val<OH*pitch:=count ▸ live
    simp [paddedBook,DescentOrdinaryRasterReturn.extend,live,off]


include ticket age radix tokens in
/-- The actual program transforms both original native sweeps, at arbitrary old and new pitches. -/
theorem raster_sources {H M₀ M w:ℕ}(oldFit:OH≤H)(banks:Sources)(base:ℕ)
    (m:Memory w)(auth:stock)(precision:(A).wire*((A).z*G.b)*(A).cap<2^mb)
    (m₀:0<M₀)(m₁:0<M)(hosts:0<R)(chunksPos:0<chunks NG M)
    (paid:∀(q:Fin pitch) (p:Row H OG M₀),m (banks.paid.base+q.val*(H*chunks OG M₀)+(row H OG M₀ p).val)=
      ((data (DescentOrdinaryRasterReturn.extend (paidRaster (mb:=mb) ticket tokens q)) p).val:Computability.VPVNP.BurstRAM.Word w))
    (alive:∀(q:Fin pitch) (p:Row H OG M₀),m (banks.alive.base+q.val*(H*chunks OG M₀)+(row H OG M₀ p).val)=
      ((data (DescentOrdinaryRasterReturn.extend (actorRaster ticket tokens q)) p).val:Computability.VPVNP.BurstRAM.Word w))
    (count:m banks.count.base=(NH:Computability.VPVNP.BurstRAM.Word w))(countBefore:banks.count.base<base)
    (paidBefore:banks.paid.base+pitch*(H*chunks OG M₀)≤base)
    (actorBefore:banks.alive.base+pitch*(H*chunks OG M₀)≤base)
    (space:DescentOrdinaryRasterReturn.Room (⟨pitch,H,R,NG,2^k,mb,M₀,M⟩:DescentVenueQuantityPlanes.Dims) banks base NH w):
    let d:= (⟨pitch,H,R,NG,2^k,mb,M₀,M⟩:DescentVenueQuantityPlanes.Dims)
    let out:=(DescentOrdinaryRasterReturn.phase d banks base w).image m
    (∀(x:DescentColonies.Block k)(p:Row R NG M),out ((paidBank d base x.val).base+(row R NG M p).val)=
      ((data (fun h g=>Census.count target.placement (Equiv.refl _) names mb h g x) p).val:Computability.VPVNP.BurstRAM.Word w)) ∧
    (∀(x:DescentColonies.Block k)(p:Row R NG M),out ((actorBank d base x.val).base+(row R NG M p).val)=
      ((data (Venue.actual target.placement (Function.Embedding.refl _) names x) p).val:Computability.VPVNP.BurstRAM.Word w)):=by
  intro d out
  have same:OG=NG*2^k:=by simpa using Fintype.card_congr ((digits).trans finProdFinEquiv)
  have number (j:Fin (NG*2^k)):((digits).symm (finProdFinEquiv.symm j)).val=j.val:=by
    change (finProdFinEquiv (finProdFinEquiv.symm j)).val=_
    rw [Equiv.apply_symm_apply]
  have counted:NH=OH*pitch:=by rw [ticket.hostCount];ring
  have convertRows {b:ℕ}(val:Fin pitch→Fin OH→Fin OG→Cell b)(source:Bank)
      (have_:∀(q:Fin pitch) (p:Row H OG M₀),m (source.base+q.val*(H*chunks OG M₀)+(row H OG M₀ p).val)=
        ((data (DescentOrdinaryRasterReturn.extend (val q)) p).val:Computability.VPVNP.BurstRAM.Word w))(q:Fin pitch):
      ∀p:Row H (NG*2^k) M₀,m (source.base+q.val*(H*chunks (NG*2^k) M₀)+(row H (NG*2^k) M₀ p).val)=
        ((data (DescentOrdinaryRasterReturn.extend (oldInput age radix val q)) p).val:Computability.VPVNP.BurstRAM.Word w):=by
    have lifted:=DescentSixParty.ClosedReset.Window.cast_rows (m:=M₀) same (fun j=>(digits).symm (finProdFinEquiv.symm j))
      number (DescentOrdinaryRasterReturn.extend (H:=H) (val q)) m (source.base+q.val*(H*chunks OG M₀)) (have_ q)
    have positionEq:(fun (h:Fin H) (j:Fin (NG*2^k))=>DescentOrdinaryRasterReturn.extend (val q) h ((digits).symm (finProdFinEquiv.symm j)))=
        DescentOrdinaryRasterReturn.extend (oldInput age radix val q):=by funext h j;simp only [DescentOrdinaryRasterReturn.extend,oldInput]
    have loc:source.base+q.val*(H*chunks OG M₀)=source.base+q.val*(H*chunks (NG*2^k) M₀):=
      congrArg (fun groups=>source.base+q.val*(H*chunks groups M₀)) same
    rw [positionEq,loc] at lifted
    exact lifted
  have got:=DescentOrdinaryRasterReturn.issued d banks base m oldFit (counted ▸ newFit) (counted ▸ space) m₀ m₁
    (Nat.two_pow_pos _) hosts chunksPos (oldInput age radix (paidRaster (mb:=mb) ticket tokens))
    (oldInput age radix (actorRaster ticket tokens)) (convertRows _ _ paid) (convertRows _ _ alive)
    (by change m banks.count.base=((OH*pitch : ℕ):Computability.VPVNP.BurstRAM.Word w); exact count.trans (congrArg (fun n : ℕ=>(n:Computability.VPVNP.BurstRAM.Word w)) counted)) (same ▸ paidBefore) (same ▸ actorBefore) countBefore
  constructor
  · intro x p
    have eqData : paddedBook (cap:=cap) age radix (paidRaster (mb:=mb) ticket tokens) x =
        (fun h g=>Census.count target.placement (Equiv.refl _) names mb h g x) :=
      funext fun h=>funext fun g=>paid_return ticket tokens age radix newFit auth precision x h g
    exact (got.1 x p).trans (congrArg (fun t : Fin R→Fin NG→Cell mb=>((data t p).val:Computability.VPVNP.BurstRAM.Word w)) eqData)
  · intro x p
    have eqData : paddedBook (cap:=cap) age radix (actorRaster ticket tokens) x =
        Venue.actual target.placement (Function.Embedding.refl _) names x :=
      funext fun h=>funext fun g=>actor_return ticket tokens age radix newFit auth x h g
    exact (got.2 x p).trans (congrArg (fun t : Fin R→Fin NG→Cell 1=>((data t p).val:Computability.VPVNP.BurstRAM.Word w)) eqData)

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
