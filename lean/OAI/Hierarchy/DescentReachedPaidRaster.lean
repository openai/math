import OAI.Hierarchy.DescentReachedPaidFields
import OAI.Hierarchy.DescentReachedScalarBookRun

namespace OAI
/-! # Native ordinary successor paid-record counts and isolated actor flags -/
namespace Hierarchy.DescentLocalArchiveOrder
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentCompiler DescentStageEdgeReceipt
open DescentCableDonorNames DescentOrdinaryLocalBirth DescentHostDegree DescentHostDirectory DescentOrdinaryDonorHalo
open DescentNetworkPartition Computability.BorderVNP.Crossing DescentSharedCableNames DescentSixParty.StarKeys
open DescentColonies DescentGL DescentWalshTables DescentPacking
open DescentGroupPeerOrder DescentPacking.PackedMatch.Local.Stage DescentSortedHaloRaster DescentHaloWalkRAM DescentSIMDLookup
open DescentScalarVenueMask DescentHostDirectory.SiteDecode DescentOrdinaryLocalBirth DescentSharedCableNames DescentPackedActorMask
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentScalarBookReshape
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
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
local notation "M" => ticket.issued.common_chart he T c ((r).state c)

local notation "bookChart" => activeChart ticket
local notation "key" => (bookChart).key he T c
local notation "addr" => MarkedWorld.address sel key (bookChart).hub T.k (gainExponent 20 T.Δ)
local notation "C" => ↥(MarkedWorld.reclaimed sel key (bookChart).hub T.k (gainExponent 20 T.Δ))
local notation "venue" => addr ∘ group
local notation "stageBits" => physicalBits G W.toWorld (r).pick units stageLimit ((r).profile c) arch.bit.recipe

local notation "A" => cap.placement
local notation "deg" => (A).degree
local notation "near" => groupedNear (A).near
local notation "bound" => (deg+1)^4*2^k
local notation "sites" => (A).site cap.vertex cap.valid.coordinates

local notation "roster" => hostRotor cap.vertex (hostRoster A (cap.vertex.trans Fin.valEmbedding))
local notation "reach" => Gather.reaching roster
local notation "halo" => reachedHalo ticket
local notation "name" => rackName (cap:=cap)

local notation "shelf"=>2^(packExponent 20 deg)+2
local notation "pitch"=>(2^(k+1)-1)*shelf
local notation "raw"=>2^(k+1)*shelf
local notation "used"=>fun p:(r).pairs=>(r).picked (p,0)
local notation "oldID"=>cap.order.trans Fin.valEmbedding
local notation "origin"=>outgoingSlot A oldID S cap.valid (r).pick used
local notation "breadth"=>DescentHaloWalkRAM.breadth deg
local notation "K"=>1+(A).cap*6
local notation "moves"=>rotor A (groupRank Fin.valEmbedding (cap.vertex.trans Fin.valEmbedding))

open DescentPaidResidentCount
variable {mb : ℕ}
variable (tokens : Block k→Fin (1+cap.placement.cap*6)→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→
  Ticket (DescentHaloWalkRAM.breadth cap.placement.degree) (2^(k+1)*(2^(packExponent 20 cap.placement.degree)+2)))
local notation "physical" => DescentScalarVenueMask.fields reach tokens (flags (cap:=cap)) k (gainExponent 20 deg) shelf pitch
local notation "stock" => Descriptors shelf k (A).pos (A).block (ticketParent (he:=he) (T:=T)) (ticketSlot (c:=c) ticket)
  (key∘group) cap.vertex (Function.Embedding.refl _) moves tokens
local notation "oldCensus" => fun x h g=>Census.count A (Equiv.refl _) cap.vertex mb h g x
local notation "counts" => DescentOrdinaryAtomFieldRAM.RoleCounts.priorValue reach oldCensus
local notation "cost" => fun u : W.graph.Site=>((A).records u).length
local notation "dest" => n.destination∘rawInput he T c ((r).state c)

local notation "OH" => Fintype.card cap.V
local notation "OG" => S.groupCount i
local notation "NH" => Fintype.card target.V
local notation "NG" => S.groupCount (i+1)
variable (age : i<S.length) (radix : S.radix=2^k)
local notation "digits" => S.groupDigits age radix
local notation "coord" => DescentPaidResidentCount.occupies target.placement (Equiv.refl _) target.vertex

def paidRaster (l : Fin pitch) (h : Fin OH) (g : Fin OG) : Cell mb :=
  let _ := ticket
  DescentPaidResidentCount.counted bound (A).cap mb (DescentPackedActorMask.target (Packed.bits pitch) _
    (Packed.token (some l)) (encode _ _ (physical h g))) (encode mb bound (counts h g))

def actorRaster (l : Fin pitch) (h : Fin OH) (g : Fin OG) : Cell 1 :=
  let _ := ticket
  if ∃j,physical h g j=Packed.token (some l) then 1 else 0

private def actorLow (a : (stepGraph).Site) : Fin pitch :=
  DescentPackedChildNeighbor.lowDigit ⟨(venue a).val,legal_label ticket (venue a)⟩

private theorem actorLow_val (a : (stepGraph).Site) :
    (actorLow ticket a).val=localNumber k shelf (venue a).val := by
  simp [actorLow,DescentPackedChildNeighbor.lowDigit,localNumber,packedNumber]

theorem actor_coords (a : (stepGraph).Site) (h : Fin NH) (g : Fin NG) (x : Block k) :
    coord h g x (dest a) ↔
      cap.vertex (venue a).val.1.2=(finProdFinEquiv.symm (hostIndex ticket h)).1 ∧
      (venue a).val.1.1=(digits).symm (g,x) ∧
      localNumber k shelf (venue a).val=(finProdFinEquiv.symm (hostIndex ticket h)).2.val := by
  obtain ⟨group_,host⟩:=paid_location ticket age radix a
  have hostAt : finProdFinEquiv (cap.vertex (venue a).val.1.2,actorLow ticket a)=
      hostIndex ticket (target.vertex (target.placement.pos (dest a)).2) := by
    apply Fin.ext
    change _=(target.vertex (target.placement.pos (dest a)).2).val
    rw [host,finProdFinEquiv_apply_val,actorLow_val]
    ring
  have groupAt := (digits).symm_apply_eq.mpr group_
  constructor
  · rintro ⟨hh,hg,hx⟩
    change (target.placement.pos (dest a)).1=g at hg
    rw [hh] at hostAt
    have both:=finProdFinEquiv.eq_symm_apply.mpr hostAt
    exact ⟨congrArg Prod.fst both,groupAt.symm.trans (congrArg (digits).symm (Prod.ext hg hx)),
      (actorLow_val ticket a).symm.trans (congrArg (fun q : Fin OH×Fin pitch=>q.2.val) both)⟩
  · rintro ⟨hh,hg,hl⟩
    have eqPair : (cap.vertex (venue a).val.1.2,actorLow ticket a)=
        finProdFinEquiv.symm (hostIndex ticket h) := Prod.ext hh (Fin.ext ((actorLow_val ticket a).trans hl))
    have eqGroup := group_.trans ((digits).eq_symm_apply.mp hg)
    exact ⟨(hostIndex ticket).injective (hostAt.symm.trans (finProdFinEquiv.eq_symm_apply.mp eqPair)),
      congrArg Prod.fst eqGroup,congrArg Prod.snd eqGroup⟩

theorem actor_at (h : Fin NH) (g : Fin NG) (x : Block k) :
    (∃v,coord h g x v) ↔ ∃a : (stepGraph).Site,
      cap.vertex (venue a).val.1.2=(finProdFinEquiv.symm (hostIndex ticket h)).1 ∧
      (venue a).val.1.1=(digits).symm (g,x) ∧
      localNumber k shelf (venue a).val=(finProdFinEquiv.symm (hostIndex ticket h)).2.val := by
  constructor
  · rintro ⟨v,hv⟩
    obtain ⟨a,rfl⟩:=raw_destination_onto n ((r).state c) v
    exact ⟨a,(actor_coords ticket age radix a h g x).mp hv⟩
  · rintro ⟨a,yes⟩
    exact ⟨_,(actor_coords ticket age radix a h g x).mpr yes⟩

local notation "regroup" => fun f x h g=>DescentScalarBookReshape.book (oldInput age radix f) x (hostIndex ticket h) g

theorem paid_raster_book (auth : stock) (precision : (A).wire*((A).z*G.b)*(A).cap<2^mb)
    (h : Fin NH) (g : Fin NG) (x : Block k) :
    (regroup) (paidRaster (mb:=mb) ticket tokens) x h g=
      Census.count target.placement (Equiv.refl _) target.vertex mb h g x := by
  classical
  let pair:=finProdFinEquiv.symm (hostIndex ticket h)
  change paidRaster ticket tokens pair.2 pair.1 ((digits).symm (finProdFinEquiv.symm (finProdFinEquiv (g,x))))=_
  rw [Equiv.symm_apply_apply]
  by_cases yes : ∃v,coord h g x v
  · obtain ⟨a,ha,hg,hl⟩:=(actor_at ticket age radix h g x).mp yes
    have atSite:=(actor_coords ticket age radix a h g x).mpr ⟨ha,hg,hl⟩
    obtain ⟨h0,h1,h2⟩:=atSite
    have actual:=paid_at_actor ticket tokens auth precision a pair.2 hl
    change paidRaster ticket tokens pair.2 (cap.vertex (venue a).val.1.2) (venue a).val.1.1=_ at actual
    rw [ha,hg] at actual
    rw [actual,←h0,←h1,←h2,live target.placement S target.valid (Equiv.refl _) target.vertex]
  · rw [ghost target.placement (Equiv.refl _) target.vertex mb h g x yes]
    exact paid_blank ticket tokens auth _ _ _ (mt (actor_at ticket age radix h g x).mpr yes)

theorem actor_raster_book (auth : stock) (h : Fin NH) (g : Fin NG) (x : Block k) :
    (regroup) (actorRaster ticket tokens) x h g=if ∃v,coord h g x v then 1 else 0 := by
  classical
  simp only [DescentScalarBookReshape.book,oldInput,Equiv.symm_apply_apply,actorRaster]
  let pair := finProdFinEquiv.symm (hostIndex ticket h)
  have iff_ := (actor_presence ticket tokens auth pair.1 ((digits).symm (g,x)) pair.2).trans
    (actor_at ticket age radix h g x).symm
  by_cases live_ : ∃v,coord h g x v
  · rw [ite_eq_left (iff_.mpr live_),ite_eq_left live_]
  · rw [ite_eq_right (mt iff_.mp live_),ite_eq_right live_]

/-- The same physical reshape serves each label width, including a single
bit that remains set on an isolated actor with zero retained scalars. -/
theorem issued_raster {lanes w b : ℕ} (rowValue : Fin pitch→Fin OH→Fin OG→Cell b)
    (after : Block k→Fin NH→Fin NG→Cell b)
    (correct : ∀x h g,(regroup) rowValue x h g=after x h g)
    (src : Bank) (base out : ℕ) (mem : Memory w) (hm : 0<lanes)
    (fit : DescentScalarBookReshape.Room OH pitch NG (2^k) b lanes w base out src)
    (source : ∀l(p : Row OH OG (lanes*2^k)),
      mem (src.base+l.val*(OH*chunks NG lanes)+(row OH OG (lanes*2^k) p).val)=
        ((data (rowValue l) p).val:Computability.VPVNP.BurstRAM.Word w)) :
    let done:=DescentScalarBookReshape.result OH pitch NG (2^k) b lanes base out src mem
    let blockCells:=(OH*pitch)*chunks NG lanes
    (DescentScalarBookReshape.program OH pitch NG (2^k) b lanes base out w src).Exec mem done
      ((4+10*DescentScalarBookReshape.cells OH pitch NG (2^k) b lanes)+(4+(2^k*blockCells)*54)) ∧
    (∀x(p : Row NH NG lanes),done (DescentScalarBookReshape.dest OH pitch NG lanes out x+
      (row NH NG lanes p).val)=((data (after x) p).val:Computability.VPVNP.BurstRAM.Word w)) ∧
    ∀a,a<base ∨ out+2^k*blockCells≤a→done a=mem a := by
  have same:OG=NG*2^k:=by simpa using Fintype.card_congr ((digits).trans finProdFinEquiv)
  have numeric (g : Fin (NG*2^k)) : ((digits).symm (finProdFinEquiv.symm g)).val=g.val:=by
    change (finProdFinEquiv (finProdFinEquiv.symm g)).val=g.val
    rw [Equiv.apply_symm_apply]
  have input:=fun l=>source_cast same (fun g=>(digits).symm (finProdFinEquiv.symm g)) numeric
    (rowValue l) mem (src.base+l.val*(OH*chunks NG lanes)) (source l)
  obtain ⟨run,read,frame⟩:=DescentScalarBookReshape.run base out src mem
    (oldInput age radix rowValue) hm (Nat.two_pow_pos _) fit input
  refine ⟨run,?_,frame⟩
  have result:=transferred ticket age radix rowValue out _ read
  intro x p
  rw [←funext (fun h=>funext (fun g=>correct x h g))]
  exact result x p

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
