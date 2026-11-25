import OAI.Hierarchy.DescentReachedDonorSlots
import OAI.Hierarchy.DescentScalarVenueEvidence
import OAI.Hierarchy.DescentScalarActorPublisher
import OAI.Hierarchy.DescentReachedScalarReshape
import OAI.Hierarchy.DescentIssuedDonors

namespace OAI
/-! # Actual old and born tests for the chronological scalar archive -/
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

local notation "shelf"=>2^(packExponent 20 deg)+2
local notation "pitch"=>(2^(k+1)-1)*shelf
local notation "raw"=>2^(k+1)*shelf
local notation "used"=>fun p:(r).pairs=>(r).picked (p,0)
local notation "oldID"=>cap.order.trans Fin.valEmbedding
local notation "origin"=>outgoingSlot A oldID S cap.valid (r).pick used
local notation "K"=>1+(A).cap*6
local notation "moves"=>rotor A (groupRank Fin.valEmbedding (cap.vertex.trans Fin.valEmbedding))

def ticketParent : W.graph.Site⊕((r).pairs×Fin 6)→W.graph.Site
  | .inl u=>u
  | .inr (p,_)=>W.graph.src ((r).pick (p,0))

def ticketSlot (_link : OrdinaryLink cap he T c n target) : W.graph.Site⊕((r).pairs×Fin 6)→Fin K
  | .inl _=>finSumFinEquiv (Sum.inl (0:Fin 1))
  | .inr (p,j)=>finSumFinEquiv (Sum.inr (finProdFinEquiv (origin p,j)))

def flags (h : Fin (Fintype.card cap.V)) (_ : Fin (S.groupCount i)) : Cell 1:=
  if z : ∃v,cap.vertex v=h then ((A).hub z.choose).toNat else 0

private theorem flags_at (z : capV) : decide (flags (cap:=cap) (cap.vertex z.2) z.1 ≠ 0) = (A).hub z.2 := by
  have yes : ∃v,cap.vertex v=cap.vertex z.2 := ⟨_,rfl⟩
  simp only [flags,dite_eq_left yes,cap.vertex.injective yes.choose_spec]
  cases (A).hub z.2 <;> decide

theorem flag_key (label : C) : decide (flags (cap:=cap) (cap.vertex label.val.1.2) label.val.1.1≠0)=(bookChart).hub label.val.1 :=by
  obtain ⟨a,_,ea⟩:=Finset.mem_image.mp label.property
  have top:(key a).1=label.val.1:=by simpa only [Function.comp_apply,show (mergeHub (bookChart).hub T.k (gainExponent 20 T.Δ) (key a)).1=(key a).1 from by unfold mergeHub;split <;> rfl] using congrArg Prod.fst ea
  have known:=ticket.donor_key_hub a
  change (bookChart).hub (key a).1=(A).hub (key a).1.2 at known
  rw [top] at known
  exact (flags_at (cap:=cap) label.val.1).trans known.symm

private theorem key_valid (a : (sel).graph.Site): key a∈keys k shelf:=by
  obtain rfl:=ticket.sourceRate;obtain rfl:=eq_of_heq ticket.placement
  exact (Classical.choose_spec (ticket.issued.common_chart he cap.placement.stage c ((BitDescription.scannedRows he cap.placement.stage).state c))).1.1 a

theorem legal_label (label : C) : label.val∈keys k shelf:=by
  obtain rfl:=ticket.sourceRate;obtain rfl:=eq_of_heq ticket.placement
  obtain ⟨a,_,h⟩:=Finset.mem_image.mp label.property
  rw [←h];exact merged_mem_keys _ _ _ _ (key_valid ticket a)

variable (tokens : Block k→Fin (1+cap.placement.cap*6)→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Ticket (DescentHaloWalkRAM.breadth cap.placement.degree) (2^(k+1)*(2^(packExponent 20 cap.placement.degree)+2)))
local notation "actorsKey"=>(key∘group)
local notation "stock"=>Descriptors shelf k (A).pos (A).block (ticketParent (he:=he) (T:=T)) (ticketSlot (c:=c) ticket) actorsKey cap.vertex (Function.Embedding.refl _) moves tokens

private theorem actual_root (z : capV) (j : Fin deg) (u : capV) (step_ : moves z j=some u) : roster (cap.vertex z.2) j=some (cap.vertex u.2) ∧ u.1=z.1 :=by
  rcases z with ⟨g,h⟩
  rw [rotor_group] at step_;obtain ⟨v,yes,hv⟩:=Option.map_eq_some_iff.mp step_;subst u
  refine ⟨?_,rfl⟩
  simp [hostRotor,yes]

private theorem merged_key (x : (stepGraph).Site) :
    (venue x).val = mergeHub (fun z : capV => (A).hub z.2) k (gainExponent 20 deg) (actorsKey x) := by
  have shape : T.k = k ∧ T.Δ = deg := by
    obtain rfl := ticket.sourceRate
    obtain rfl := eq_of_heq ticket.placement
    exact ⟨rfl,rfl⟩
  have flag : (bookChart).hub (actorsKey x).1 = (A).hub (actorsKey x).1.2 := ticket.donor_key_hub (group x)
  change mergeHub (bookChart).hub T.k (gainExponent 20 T.Δ) (actorsKey x) = _
  refine (congrArg₂ (fun rate degree => mergeHub (bookChart).hub rate (gainExponent 20 degree) (actorsKey x)) shape.1 shape.2).trans ?_
  simp only [mergeHub,flag]

private theorem field_iff (auth : stock) (label : C) (l : Fin pitch) (name : localNumber k shelf label.val=l.val) (d : Fin bound) (s : Fin K) :
    DescentScalarVenueMask.fields reach tokens (flags (cap:=cap)) k (gainExponent 20 deg) shelf pitch (cap.vertex label.val.1.2) label.val.1.1 (finProdFinEquiv (d,s))=Packed.token (some l) ↔
    ∃x,donorAt halo label d=some (ticketParent (he:=he) (T:=T) x) ∧ ticketSlot (c:=c) ticket x=s ∧ venue x=label :=by
  let hu:=fun z:capV=>(A).hub z.2
  have accepted_:=accepted (gain:=gainExponent 20 deg) (A).pos (A).block (ticketParent (he:=he) (T:=T)) actorsKey (ticketSlot (c:=c) ticket) cap.vertex (Function.Embedding.refl _)
    roster moves (fun z j y h=>(actual_root (cap:=cap) z j y h).1) (fun z j y h=>(actual_root (cap:=cap) z j y h).2)
    tokens hu (flags (cap:=cap)) (flags_at (cap:=cap))
    auth (fun x=>key_valid ticket (group x)) label.val (legal_label ticket label) l name d s
  refine accepted_.trans ?_
  have target_ (x : (stepGraph).Site) : mergeHub hu k (gainExponent 20 deg) (actorsKey x)=label.val ↔ venue x=label := by
    exact ⟨fun h => Subtype.ext ((merged_key ticket x).trans h),fun h => (merged_key ticket x).symm.trans (congrArg Subtype.val h)⟩
  constructor
  · rintro ⟨x,atH,atB,atG,atS,atDest⟩;exact ⟨x,(donor_slot ticket label d _).2 ⟨atH,atB,atG⟩,atS,(target_ x).1 atDest⟩
  · rintro ⟨x,dn,atS,atDest⟩;obtain ⟨atH,atB,atG⟩:=(donor_slot ticket label d _).1 dn
    exact ⟨x,atH,atB,atG,atS,(target_ x).2 atDest⟩

theorem old_venue (auth : stock) (label : C) (l : Fin pitch) (name : localNumber k shelf label.val=l.val) (d : Fin bound) :
    DescentScalarVenueMask.fields reach tokens (flags (cap:=cap)) k (gainExponent 20 deg) shelf pitch (cap.vertex label.val.1.2) label.val.1.1 (oldAddress (A).cap d)=Packed.token (some l) ↔
    ∃u,donorAt halo label d=some u ∧ venue (.inl u)=label:=by
  refine (field_iff ticket tokens auth label l name d (finSumFinEquiv (Sum.inl (0:Fin 1)))).trans ?_
  constructor
  · rintro ⟨u|⟨p,j⟩,at_,slot,dest⟩
    · exact ⟨u,at_,dest⟩
    · cases finSumFinEquiv.injective slot
  · rintro ⟨u,at_,dest⟩;exact ⟨Sum.inl u,at_,rfl,dest⟩

theorem born_venue (auth : stock) (label : C) (l : Fin pitch) (name : localNumber k shelf label.val=l.val) (d : Fin bound) (p : Fin (A).cap) (j : Fin 6) :
    DescentScalarVenueMask.fields reach tokens (flags (cap:=cap)) k (gainExponent 20 deg) shelf pitch (cap.vertex label.val.1.2) label.val.1.1 (bornAddress d (finProdFinEquiv (p,j)))=Packed.token (some l) ↔
    ∃z,donorAt halo label d=some (W.graph.src ((r).pick (z,0))) ∧ origin z=p ∧ venue (.inr (z,j))=label:=by
  refine (field_iff ticket tokens auth label l name d (finSumFinEquiv (Sum.inr (finProdFinEquiv (p,j))))).trans ?_
  constructor
  · rintro ⟨u|⟨z,t⟩,at_,slot,dest⟩
    · cases finSumFinEquiv.injective slot
    · have pair:=finProdFinEquiv.injective (Sum.inr.inj (finSumFinEquiv.injective slot))
      have party : t=j := congrArg Prod.snd pair
      subst j
      exact ⟨z,at_,congrArg Prod.fst pair,dest⟩
  · rintro ⟨z,at_,slot,dest⟩;exact ⟨Sum.inr (z,j),at_,by simp [ticketSlot,slot],dest⟩

/-- Every nonzero native venue token belongs to a real old or born actor at
that ordinal. This applies even when a whole host or venue raster is empty. -/
theorem venue_of_hit (auth : stock) (h : Fin (Fintype.card cap.V)) (g : Fin (S.groupCount i))
    (l : Fin pitch) (d : Fin bound) (s : Fin K)
    (hit : DescentScalarVenueMask.fields reach tokens (flags (cap:=cap)) k (gainExponent 20 deg) shelf pitch h g (finProdFinEquiv (d,s))=Packed.token (some l)) :
    ∃x,cap.vertex (venue x).val.1.2=h ∧ (venue x).val.1.1=g ∧ localNumber k shelf (venue x).val=l.val ∧ ticketSlot (c:=c) ticket x=s:=by
  let hu:=fun z:capV=>(A).hub z.2
  obtain ⟨x,vn,gn,ln,sl⟩:=actor_of_hit (A).pos (A).block (ticketParent (he:=he) (T:=T)) actorsKey (ticketSlot (c:=c) ticket) cap.vertex (Function.Embedding.refl _)
    roster moves (fun z j y hw=>(actual_root (cap:=cap) z j y hw).1) (fun z j y hw=>(actual_root (cap:=cap) z j y hw).2)
    tokens hu (flags (cap:=cap)) (flags_at (cap:=cap))
    auth (fun x=>key_valid ticket (group x)) h g l d s hit
  have merged := merged_key ticket x
  have roof : (mergeHub hu k (gainExponent 20 deg) (actorsKey x)).1=(actorsKey x).1:=by unfold mergeHub;split <;> rfl
  have siteEq := (congrArg Prod.fst merged).trans roof
  exact ⟨x,(congrArg (fun z : capV => cap.vertex z.2) siteEq).trans vn,
    (congrArg Prod.fst siteEq).trans gn,(congrArg (localNumber k shelf) merged).trans ln,sl⟩

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
