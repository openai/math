import OAI.Hierarchy.DescentReachedScalarDonor
import OAI.Hierarchy.DescentScalarRoleCounts

namespace OAI
/-! # All occupied and empty donor slots in the native sorted geometry -/
namespace Hierarchy.DescentLocalArchiveOrder
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentCompiler DescentStageEdgeReceipt
open DescentCableDonorNames DescentOrdinaryLocalBirth DescentHostDegree DescentHostDirectory DescentOrdinaryDonorHalo
open DescentNetworkPartition Computability.BorderVNP.Crossing DescentSharedCableNames DescentSixParty.StarKeys
open DescentColonies DescentGL DescentWalshTables DescentPacking
open DescentGroupPeerOrder DescentPacking.PackedMatch.Local.Stage DescentSortedHaloRaster DescentHaloWalkRAM DescentSIMDLookup
open scoped Classical
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
local notation "M" => ticket.issued.measured_chart he T c ((r).state c)

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

theorem donor_slot (label : C) (j : Fin bound) (u : W.graph.Site) :
    donorAt halo label j=some u ↔
      let z : Fin (breadth deg)×Fin (2^k) := finProdFinEquiv.symm j
      DescentSortedRoster.indexed reach (cap.vertex label.val.1.2) z.1=some (cap.vertex ((A).pos u).2) ∧ z.2=(A).block u ∧ ((A).pos u).1=label.val.1.1 :=by
  let host:=cap.vertex label.val.1.2
  let z : Fin (breadth deg)×Fin (2^k):=finProdFinEquiv.symm j
  constructor
  · intro got
    obtain ⟨mem,at_⟩:=(donorAt_eq halo label).mp got
    rw [←at_];exact actual_donor ticket label u mem
  · rintro ⟨seen,blockEq,groupEq⟩
    have data_:=(DescentSortedRoster.indexed_iff reach host z.1 (cap.vertex ((A).pos u).2)).1 seen
    have member:=data_.1
    rw [reached_set (A).near cap.vertex roster (exact_host (cap:=cap)) label.val.1.2] at member
    obtain ⟨v,reachable,eqn⟩:=Finset.mem_map.mp member
    have local_ : ((A).pos u).2∈around (A).near 4 label.val.1.2:=(cap.vertex.injective eqn) ▸ reachable
    have interior : (A).pos u∈around near 4 label.val.1:=by
      rw [show label.val.1=(label.val.1.1,label.val.1.2) from rfl,grouped]
      exact Finset.mem_map.mpr ⟨((A).pos u).2,local_,Prod.ext groupEq.symm rfl⟩
    have site : u∈(halo).member label:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,interior⟩
    let t:Fin (breadth deg)×Fin (2^k):=finProdFinEquiv.symm ((halo).slot label ⟨u,site⟩)
    have physical:=actual_donor ticket label u site
    have td:=(DescentSortedRoster.indexed_iff reach host t.1 (cap.vertex ((A).pos u).2)).1 physical.1
    have same:t=z:=Prod.ext (Fin.ext (td.2.symm.trans data_.2)) (physical.2.1.trans blockEq.symm)
    exact (donorAt_eq halo label).2 ⟨site,finProdFinEquiv.symm.injective same⟩

variable {a K mb : ℕ} (roles : Block k→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell (a*K))
    (ids : ∀u,(arch.bit.recipe u).Node↪Fin K)
    (stored : ∀b h g j,(encode a K).symm (roles b h g) j≠0 ↔ ∃u,cap.placement.block u=b ∧ cap.vertex (cap.placement.pos u).2=h ∧ (cap.placement.pos u).1=g ∧ ∃v,ids u v=j)
    (room : K<2^mb)

include stored room in
theorem counted (label : C) (j : Fin bound) :
    (DescentOrdinaryAtomFieldRAM.RoleCounts.value reach roles mb (cap.vertex label.val.1.2) label.val.1.1 j).val=
      ((donorAt halo label j).map (fun u=>Fintype.card (arch.bit.recipe u).Node)).getD 0 :=by
  let z:Fin (breadth deg)×Fin (2^k):=finProdFinEquiv.symm j
  let host:=cap.vertex label.val.1.2;let g:=label.val.1.1
  cases picked:DescentSortedRoster.indexed reach host z.1 with
  | none=>
    have missing:donorAt halo label j=none:=by
      cases old:donorAt halo label j with
      | none=>rfl
      | some u=>
        have got := (donor_slot ticket label j u).1 old
        cases picked.symm.trans got.1
    simp [DescentOrdinaryAtomFieldRAM.RoleCounts.value,show DescentSortedRoster.indexed reach host z.1=none from picked,missing,host,z]
  | some h=>
    let x:=roles z.2 h g
    change ((DescentSortedRoster.indexed reach host z.1).elim 0 (fun v=>DescentOrdinaryAtomFieldRAM.RoleCounts.count mb (roles z.2 v g))).val=_
    rw [picked];simp only [Option.elim_some]
    cases old:donorAt halo label j with
    | none=>
      have empty : ∀t,(encode a K).symm x t=0:=by
        intro t;by_contra nonzero
        obtain ⟨u,b,hs,gs,_⟩:=(stored z.2 h g t).1 nonzero
        have named:=(donor_slot ticket label j u).2 ⟨picked.trans (congrArg some hs.symm),b.symm,gs⟩
        rw [old] at named;contradiction
      have zero:DescentOrdinaryAtomFieldRAM.RoleCounts.support x=∅:=by ext t;simp [DescentOrdinaryAtomFieldRAM.RoleCounts.support,empty]
      change (DescentOrdinaryAtomFieldRAM.RoleCounts.count mb x).val=0;simp [DescentOrdinaryAtomFieldRAM.RoleCounts.count,zero]
    | some u=>
      have data_:=(donor_slot ticket label j u).1 old
      have atHost : h=cap.vertex ((A).pos u).2:=Option.some.inj (picked.symm.trans data_.1)
      apply DescentOrdinaryAtomFieldRAM.RoleCounts.exact_count (ids u) x _ room
      intro t;rw [stored]
      constructor
      · rintro ⟨y,b,house,group_,node⟩
        have same:y=u:=by
          apply cap.valid.coordinates
          exact Prod.ext (Prod.ext (group_.trans data_.2.2.symm) (cap.vertex.injective (house.trans atHost))) (b.trans data_.2.1)
        subst y;exact node
      · intro node;exact ⟨u,data_.2.1.symm,atHost.symm,data_.2.2,node⟩

theorem counted_prior (label : C) (j : Fin bound) (cost : W.graph.Site→ℕ)
    (prior : Block k→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell mb)
    (read : ∀u,(prior ((A).block u) (cap.vertex ((A).pos u).2) ((A).pos u).1).val=cost u)
    (unused : ∀b h g,(¬∃u,(A).block u=b ∧ cap.vertex ((A).pos u).2=h ∧ ((A).pos u).1=g)→prior b h g=0) :
    (DescentOrdinaryAtomFieldRAM.RoleCounts.priorValue reach prior (cap.vertex label.val.1.2) label.val.1.1 j).val=(donorAt halo label j).elim 0 cost:=by
  let z:Fin (breadth deg)×Fin (2^k):=finProdFinEquiv.symm j;let h:=cap.vertex label.val.1.2
  change ((DescentSortedRoster.indexed reach h z.1).elim 0 (fun v=>prior z.2 v label.val.1.1)).val=_
  cases got:donorAt halo label j with
  | some u=>
    obtain ⟨atH,atB,atG⟩:=(donor_slot ticket label j u).1 got
    let value (o : Option (Fin (Fintype.card cap.V))) := (o.elim 0 (fun v => prior z.2 v label.val.1.1)).val
    refine (congrArg value atH).trans ?_
    refine (congrArg (fun b => (prior b (cap.vertex ((A).pos u).2) label.val.1.1).val) atB).trans ?_
    exact (congrArg (fun g => (prior ((A).block u) (cap.vertex ((A).pos u).2) g).val) atG.symm).trans (read u)
  | none=>
    cases stored:DescentSortedRoster.indexed reach h z.1 with
    | none=>rfl
    | some old=>
      have empty:¬∃u,(A).block u=z.2 ∧ cap.vertex ((A).pos u).2=old ∧ ((A).pos u).1=label.val.1.1:=by
        rintro ⟨u,blockEq,hostEq,groupEq⟩
        have live :=(donor_slot ticket label j u).2 ⟨stored.trans (congrArg some hostEq.symm),blockEq.symm,groupEq⟩
        rw [got] at live;contradiction
      rw [Option.elim_some,unused z.2 old label.val.1.1 empty];rfl

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
