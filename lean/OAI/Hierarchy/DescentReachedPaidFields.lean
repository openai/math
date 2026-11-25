import OAI.Hierarchy.DescentReachedScalarVenue
import OAI.Hierarchy.DescentReachedDonorSlots
import OAI.Hierarchy.DescentPaidResidentLand
import OAI.Hierarchy.DescentPaidResidentCensus

namespace OAI
/-! # The paid census from the issued seven actor venues and predecessor counters -/
namespace Hierarchy.DescentLocalArchiveOrder
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentCompiler DescentStageEdgeReceipt
open DescentCableDonorNames DescentOrdinaryLocalBirth DescentHostDegree DescentHostDirectory DescentOrdinaryDonorHalo
open DescentNetworkPartition Computability.BorderVNP.Crossing DescentSharedCableNames DescentSixParty.StarKeys
open DescentColonies DescentGL DescentWalshTables DescentPacking
open DescentGroupPeerOrder DescentPacking.PackedMatch.Local.Stage DescentSortedHaloRaster DescentHaloWalkRAM DescentSIMDLookup
open DescentScalarVenueMask DescentHostDirectory.SiteDecode DescentOrdinaryLocalBirth DescentSharedCableNames DescentPackedActorMask
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1400000
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
local notation "base" => physicalBits G W.toWorld (r).pick units stageLimit ((r).profile c) arch.bit.recipe

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
local notation "P"=>DescentHaloWalkRAM.breadth deg
local notation "K"=>1+(A).cap*6
local notation "moves"=>rotor A (groupRank Fin.valEmbedding (cap.vertex.trans Fin.valEmbedding))

open DescentPaidResidentCount
variable {mb : ℕ}
variable (tokens : Block k→Fin (1+cap.placement.cap*6)→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Ticket (DescentHaloWalkRAM.breadth cap.placement.degree) (2^(k+1)*(2^(packExponent 20 cap.placement.degree)+2)))
local notation "physical" => DescentScalarVenueMask.fields reach tokens (flags (cap:=cap)) k (gainExponent 20 deg) shelf pitch
local notation "stock" => Descriptors shelf k (A).pos (A).block (ticketParent (he:=he) (T:=T)) (ticketSlot (c:=c) ticket)
  (key∘group) cap.vertex (Function.Embedding.refl _) moves tokens
local notation "oldCensus" => fun x h g=>Census.count A (Equiv.refl _) cap.vertex mb h g x
local notation "counts" => DescentOrdinaryAtomFieldRAM.RoleCounts.priorValue reach oldCensus
local notation "cost" => fun u : W.graph.Site=>((A).records u).length
local notation "dest" => n.destination∘rawInput he T c ((r).state c)

/-- The exact raw actor specifies the emitting chart, even when all charges
at that actor's final site have value zero. -/
theorem paid_at_actor (auth : stock) (precision : (A).wire*((A).z*G.b)*(A).cap<2^mb)
    (a : (stepGraph).Site) (l : Fin pitch) (number_eq : localNumber k shelf (venue a).val=l.val) :
    let h:=cap.vertex (venue a).val.1.2
    let g:=(venue a).val.1.1
    DescentPaidResidentCount.counted bound (A).cap mb (DescentPackedActorMask.target (Packed.bits pitch) _ (Packed.token (some l)) (encode _ _ (physical h g)))
      (encode mb bound (counts h g))=((target.placement.records (dest a)).length:ℕ) := by
  let c₀:=venue a
  have genuine:=reachedHalo_members ticket
  have levels : ∀x,(T.records x).length=cost x:=ticket.sourceCounts
  have eqFiber (x) : dest x=dest a ↔ venue x=c₀ := by
    have raw_eq := (Classical.choose_spec M).1.2 x a
    constructor
    · intro h
      apply Subtype.ext
      exact raw_eq.mp h
    · intro h
      apply raw_eq.mpr
      exact congrArg Subtype.val h
  have balance:=canonical_funds ticket.particles ((r).state c) (dest a)
  have same:=total_on_fiber dest venue (dest a) c₀ eqFiber cost
  rw [show (fun x=>(T.records x).length)=cost from funext levels] at balance
  rw [balance,same]
  let oldread : ∀x,(oldCensus ((A).block x) (cap.vertex ((A).pos x).2) ((A).pos x).1).val=cost x :=
    fun x=>live_nat A S cap.valid (Equiv.refl _) cap.vertex mb precision x
  have vacant (b h g) (absent : ¬∃u,(A).block u=b ∧ cap.vertex ((A).pos u).2=h ∧ ((A).pos u).1=g) :
      oldCensus b h g=0 := by
    apply ghost A (Equiv.refl _) cap.vertex mb h g b
    rintro ⟨v,host,group_,blk⟩
    exact absent ⟨v,blk,host,group_⟩
  exact issued A oldID S cap.valid (r).pick used venue halo genuine.1 genuine.2 c₀ _ _ _ cost
    (fun h=>by have impossible:=congrArg Fin.val h; dsimp [Packed.token] at impossible; omega)
    (old_venue ticket tokens auth c₀ l number_eq) (born_venue ticket tokens auth c₀ l number_eq)
    (fun v=>counted_prior ticket c₀ v cost oldCensus oldread vacant)

/-- Every chronological target group, block and physical host index is read
from the previous group, host and trimmed local field at this actor itself. -/
theorem paid_location (age : i<S.length) (radix : S.radix=2^k) (a : (stepGraph).Site) :
    let v:=dest a
    ((target.placement.pos v).1,target.placement.block v)=S.groupDigits age radix (venue a).val.1.1 ∧
    (target.vertex (target.placement.pos v).2).val=(cap.vertex (venue a).val.1.2).val*pitch+
      localNumber k shelf (venue a).val := by
  obtain rfl:=ticket.sourceRate
  obtain rfl:=eq_of_heq ticket.placement
  obtain ⟨_,_,chart,place,ordinal⟩:=ticket.venueRows
  let rows := BitDescription.scannedRows he cap.placement.stage
  have where_:=place (rows.state c) (activeChart ticket) a
  refine ⟨where_.1,?_⟩
  rw [ordinal]
  dsimp only [Function.comp_apply] at where_ ⊢
  rw [where_.2]
  have key_formula (q₀ : Key (Fin (S.groupCount i) × cap.V)) :
      ((cap.vertex q₀.1.2).val*(2^(k+1)-1)+nodeNumber q₀.2.1.1 q₀.2.1.2)*(2^(packExponent 20 cap.placement.degree)+2)+q₀.2.2 =
      (cap.vertex q₀.1.2).val*((2^(k+1)-1)*(2^(packExponent 20 cap.placement.degree)+2))+
        localNumber k (2^(packExponent 20 cap.placement.degree)+2) q₀ := by
    simp [localNumber,packedNumber,Nat.add_mul,Nat.mul_assoc,Nat.add_assoc]
  exact key_formula _

/-- An accepted actor has unit presence even if its funded length is zero. -/
theorem actor_presence (auth : stock) (h : Fin (Fintype.card cap.V)) (g : Fin (S.groupCount i)) (l : Fin pitch) :
    (∃j,physical h g j=Packed.token (some l)) ↔
    ∃a : (stepGraph).Site,cap.vertex (venue a).val.1.2=h ∧ (venue a).val.1.1=g ∧ localNumber k shelf (venue a).val=l.val := by
  constructor
  · rintro ⟨j,valid⟩
    obtain ⟨⟨d,s⟩,rfl⟩:=finProdFinEquiv.surjective j
    obtain ⟨a,atH,atG,atL,_⟩:=venue_of_hit ticket tokens auth h g l d s valid
    exact ⟨a,atH,atG,atL⟩
  · rintro ⟨a,rfl,rfl,atL⟩
    have members:=reachedHalo_members ticket
    rcases a with u|⟨j,t⟩
    · let label:=venue (.inl u)
      let d:=(halo).slot label ⟨u,members.1 u⟩
      refine ⟨oldAddress (A).cap d,(old_venue ticket tokens auth label l atL d).2 ⟨u,?_,rfl⟩⟩
      exact (donorAt_eq halo label).2 ⟨_,rfl⟩
    · let label:=venue (.inr (j,t))
      let d:=(halo).slot label ⟨W.graph.src ((r).pick (j,0)),members.2 j t⟩
      refine ⟨bornAddress d (finProdFinEquiv (origin j,t)),(born_venue ticket tokens auth label l atL d (origin j) t).2
        ⟨j,?_,rfl,rfl⟩⟩
      exact (donorAt_eq halo label).2 ⟨_,rfl⟩


theorem paid_blank (auth : stock) (h : Fin (Fintype.card cap.V)) (g : Fin (S.groupCount i)) (l : Fin pitch)
    (empty : ¬∃a : (stepGraph).Site,cap.vertex (venue a).val.1.2=h ∧ (venue a).val.1.1=g ∧ localNumber k shelf (venue a).val=l.val) :
    DescentPaidResidentCount.counted bound (A).cap mb (DescentPackedActorMask.target (Packed.bits pitch) _ (Packed.token (some l)) (encode _ _ (physical h g)))
      (encode mb bound (counts h g))=0 := by
  have miss : ∀j,physical h g j≠Packed.token (some l):=fun j hit=>empty ((actor_presence ticket tokens auth h g l).1 ⟨j,hit⟩)
  have no_match (j : Fin (actors bound (A).cap)) :
      ¬(Packed.token (some l) ≠ 0 ∧ physical h g j = Packed.token (some l)) :=
    fun test => miss j test.2
  unfold DescentPaidResidentCount.counted
  rw [DescentPaidResidentCount.seen (D := bound) (cap := (A).cap)
    (Packed.token (some l)) (physical h g) (counts h g)]
  have zero_old (j : Fin bound) := no_match (oldAddress (A).cap j)
  have zero_born (j : Fin (bound * ((A).cap * 6))) := no_match (DescentPaidResidentCount.birthSlot (A).cap j)
  simp only [ite_eq_right (zero_old _), ite_eq_right (zero_born _), Finset.sum_const_zero, Nat.zero_add, Nat.cast_zero]

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
