import OAI.ThreeFlat.RAM.HistoryShrinkArchive

namespace OAI
set_option quotPrecheck false
set_option maxErrors 600

namespace ThreeFlat.RAM.HistoryShrinkEmitter
open private pageStart from OAI.ThreeFlat.RAM.HistoryShrinkPlacement
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr Diagonal.TickWorkspace
open HistoryStageBody.Physical HistoryScratch HistoryMotifJoin HistoryGatherBody HistoryRefreshEmitter
open Diagonal.HistoryContraction BitNetwork.Ordered
open scoped BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F] {W p u node x : ℕ} {A : HistoryGatherBody.Layout}

private theorem PhysicalBanks.local_end (banks : PhysicalBanks u A)
    (nodeRoom : node<A.party.V^2) (cap : (A.party.motifs+2)*(A.party.parties+2)*8*32≤A.party.V)
    (loc : Local) (valid : loc.Valid A.party.motifs A.party.parties) :
    pageStart A node loc+A.party.V≤base u 18 := by
  have positive : 0<A.party.V:=banks.wordCount.symm ▸ Nat.two_pow_pos _
  have end_:=HistoryScratch.fits (base:=A.party.arena) nodeRoom cap valid
    (show A.party.V-1<A.party.V by omega)
  change pageStart A node loc+(A.party.V-1)<A.party.arena+A.party.V^4 at end_
  have full : pageStart A node loc+A.party.V≤A.party.arena+A.party.V^4 := by omega
  calc
    _≤_ := full
    _=base u 12+stride u := by rw [banks.arena,banks.wordCount]; rfl
    _≤_ := Diagonal.TickWorkspace.apart (by decide : 12<18)

theorem PhysicalBanks.savedParty (banks : PhysicalBanks u A) (nodeRoom : node<A.party.V^2)
    (cap : (A.party.motifs+2)*(A.party.parties+2)*8*32≤A.party.V)
    (motif : A.party.motif<A.party.motifs) (party : A.party.party<A.party.parties)
    (low : base u 18≤x) (high : x<base u 18+5*volume u) : PartyAway u A.party node x := by
  refine ⟨.inr (.inr ⟨low,high⟩),?_⟩
  intro k bank klt blt len size
  let loc : Local:=⟨A.party.motif+2,A.party.party+2,k,bank⟩
  have ok : loc.Valid A.party.motifs A.party.parties :=
    ⟨Nat.add_lt_add_right motif 2, Nat.add_lt_add_right party 2, klt, blt⟩
  right
  have lim:=banks.local_end nodeRoom cap loc ok
  rw [←banks.wordCount] at size
  exact ((Nat.add_le_add_left size (pageStart A node loc)).trans lim).trans low

namespace SiteSlot
variable (Z : SiteSlot F W p A) (node : ℕ) (id : ((Fin 3→Bool)→F)→ℕ) (input : Memory W)
local notation "first" => Z.init input
local notation "atArm" => Z.arms.entry node id first

/-- A single raw incidence suffices to advance the saved headers. The selected
pair is the numerical physical publisher instantiated on this arm's own input. -/
structure ArmSpaceAt (u : ℕ) (j : Fin A.party.parties) : Prop where
  header : 3+5*A.demandCap+4*A.supplyCap≤A.party.V
  width : ∀ i,Z.arms.select j.val=some i → ∀ q k,
    k<HistoryGatherExecution.cap A q → (Z.arms.plan i).width q k≤A.party.V
  result : ∀ i,Z.arms.select j.val=some i →
    (Z.arms.plan i).gatherBase=HistoryPartyPair.atPair (withParty A j.val).party node 2
  size : ∀ i,Z.arms.select j.val=some i → (Z.arms.plan i).gatherCount≤A.party.V
  pair : ∀ i,Z.arms.select j.val=some i → ∀ a,
    PartyAway u (withParty A j.val).party node a → Z.arms.pairOut i a=atArm j.val a

omit [Field F] [Fintype F] in
theorem ArmSpace.atParty (arm : Z.ArmSpace node id input u) (j : Fin A.party.parties) :
    Z.ArmSpaceAt node id input u j :=
  ⟨arm.header,arm.width j,arm.result j,arm.size j,arm.pair j⟩

omit [Field F] [Fintype F] in
theorem advance_scratch (banks : PhysicalBanks u A) (nodeRoom : node<A.party.V^2)
    (cap : (A.party.motifs+2)*(A.party.parties+2)*8*32≤A.party.V) (motif : A.party.motif<A.party.motifs)
    (j : Fin A.party.parties) (row : Z.ArmSpaceAt node id input u j)
    (vacant : Z.arms.select j.val=none→VacantRoom (withParty A j.val) node id (atArm j.val))
    (low : base u 18≤x) (high : x<base u 18+5*volume u) :
    Z.arms.advance node id (atArm j.val) j.val x=atArm j.val x := by
  let J:=withParty A j.val
  have safe:= (banks.withParty j.val).savedParty nodeRoom cap motif j.isLt low high
  cases on:Z.arms.select j.val with
  | none=>
    have keep:=vacant_away (banks.withParty j.val) id (atArm j.val) (vacant on) cap motif j.isLt x safe
    simpa only [ArmRows.advance,ArmRows.pairOutAt,ArmRows.mapOutAt,on,vacantPass] using keep
  | some i=>
    have size:=row.header
    have portCount : 1+A.demandCap+A.supplyCap≤A.party.V := by omega
    have area:=Nat.mul_le_mul_right A.party.V portCount
    have positive : 0<A.party.V:=banks.wordCount.symm ▸ Nat.two_pow_pos _
    have growth : A.party.V^2≤A.party.V^4 := Nat.pow_le_pow_right positive (by decide)
    have boundary:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 17<18)
    have end_ : HistoryGatherExecution.portsEnd J≤base u 18 := by
      change A.temp+(1+A.demandCap+A.supplyCap)*A.party.V≤_
      rw [banks.gather]
      rw [banks.wordCount] at area growth ⊢
      rw [pow_two] at growth
      change base u 17+(volume u)^4≤_ at boundary
      omega
    have small : J.temp+A.party.V≤HistoryGatherExecution.portsEnd J := by
      change A.temp+A.party.V≤A.temp+(1+A.demandCap+A.supplyCap)*A.party.V
      exact Nat.add_le_add_left (by
        have h:=Nat.mul_le_mul_right A.party.V (show 1≤1+A.demandCap+A.supplyCap by omega)
        simpa only [one_mul] using h) _
    have map : HistoryGatherExecution.output J (Z.arms.plan i) (Z.arms.pairOut i) x=Z.arms.pairOut i x := by
      apply HistoryGatherExecution.output_away
      · right
        rw [HistoryGatherExecution.header_size]
        change J.temp+(3+5*A.demandCap+4*A.supplyCap)≤x
        omega
      · intro q k lim
        have frame:=(HistoryGatherExecution.aperture J q k lim).2
        have w:=row.width i on q k lim
        change HistoryGatherBody.srcBase J q k+A.party.V≤_ at frame
        exact .inr (((Nat.add_le_add_left w _).trans frame).trans (end_.trans low))
      · rw [row.result i on]
        exact safe.page 2 2 (by decide) (by decide) _ (banks.wordCount ▸ row.size i on)
    simpa only [ArmRows.advance,ArmRows.pairOutAt,ArmRows.mapOutAt,on] using map.trans (row.pair i on x safe)

omit [Field F] [Fintype F] in
theorem entry_scratch (banks : PhysicalBanks u A) (nodeRoom : node<A.party.V^2)
    (cap : (A.party.motifs+2)*(A.party.parties+2)*8*32≤A.party.V) (motif : A.party.motif<A.party.motifs)
    (k : ℕ) (bound : k≤A.party.parties)
    (row : ∀ j : Fin A.party.parties,j.val<k → Z.ArmSpaceAt node id input u j)
    (vacant : ∀ j : Fin A.party.parties,j.val<k → Z.arms.select j.val=none→VacantRoom (withParty A j.val) node id (atArm j.val))
    (low : base u 18≤x) (high : x<base u 18+5*volume u) : atArm k x=first x := by
  have iteration (s : ℕ) (size : s≤k) : atArm s x=first x := by
    induction s with
    | zero=>rfl
    | succ s ih=>
      let j : Fin A.party.parties:=⟨s,by omega⟩
      have before : j.val<k:=by change s<k;omega
      have advance : atArm (s+1)=Z.arms.advance node id (atArm s) s := by
        simp only [ArmRows.entry,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
      rw [advance]
      exact (Z.advance_scratch node id input banks nodeRoom cap motif j (row j before) (vacant j before)
        low high).trans (ih (by omega))
  exact iteration k le_rfl

omit [Field F] [Fintype F] in
theorem private_prefix (banks : PhysicalBanks u A) (nodeRoom : node<A.party.V^2)
    (cap : (A.party.motifs+2)*(A.party.parties+2)*8*32≤A.party.V) (motif : A.party.motif<A.party.motifs)
    (k : ℕ) (bound : k≤A.party.parties)
    (row : ∀ j : Fin A.party.parties,j.val<k → Z.ArmSpaceAt node id input u j)
    (vacant : ∀ j : Fin A.party.parties,j.val<k → Z.arms.select j.val=none→VacantRoom (withParty A j.val) node id (atArm j.val))
    (i : Fin 9) : atArm k (A.privateStarts+i.val)=first (A.privateStarts+i.val) := by
  have big : 9≤A.party.V:=by nlinarith only [cap,Nat.zero_le (A.party.motifs*A.party.parties)]
  rw [banks.wordCount] at big
  apply Z.entry_scratch node id input banks nodeRoom cap motif k bound row vacant
  · rw [banks.privateStarts];omega
  · rw [banks.privateStarts];have:=i.isLt;omega

omit [Field F] [Fintype F] in
/-- A completed slot preserves the old-child prefix through its nine-word private
header, all raw parties, and the actual finishing join. -/
theorem child_prefix_end (banks : PhysicalBanks u A) (live : Z.Live node id input)
    (arms : Z.ArmSpace node id input u) (i : ℕ) (index : i<A.party.V) :
    Z.endState node id input (A.nodePorts.starts+i)=input (A.nodePorts.starts+i) := by
  let a:=A.nodePorts.starts+i
  have C:=live.geometry.capacity
  have low : base u 18≤a:=by dsimp [a];rw [banks.childStarts];omega
  have high : a<A.privateStarts := by
    have bound:=index
    rw [banks.wordCount] at bound
    dsimp only [a]
    rw [banks.childStarts,banks.privateStarts]
    omega
  have ceil : a<base u 18+5*volume u:=by rw [banks.privateStarts] at high;omega
  have initial : first a=input a:=by
    have off : ¬(A.privateStarts≤a ∧ a<A.privateStarts+9):=by omega
    change HistoryMotifJoin.headerImage _ A.privateStarts 9 input a=_
    simp [HistoryMotifJoin.headerImage,fillSegment,off]
  have store:=Z.entry_scratch node id input banks C.nodeBound C.sectors (C.motif rfl) A.party.parties le_rfl
    (fun j _=>ArmSpace.atParty Z node id input arms j) (fun j _=>live.vacant j) low ceil
  apply Eq.trans _ (store.trans initial)
  apply finish_away A true node (atArm A.party.parties) Z.children Z.wire id banks live.geometry a (.inr low)
  · intro j
    right
    change pageStart A node (parentLocal A true j.val) + A.party.V ≤ a
    exact (banks.local_end C.nodeBound C.sectors _ (parentLocal_valid A true node _ Z.children id C j)).trans low
  · intro j
    right
    rw [childLoc A true node (atArm A.party.parties) j 3]
    exact (banks.local_end C.nodeBound C.sectors _ (childLocal_valid A true node _ Z.children id C j 3)).trans low

end SiteSlot
end
end ThreeFlat.RAM.HistoryShrinkEmitter

namespace ThreeFlat.RAM.HistoryShrinkEmitter.SiteRun
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr HistoryMotifJoin
open HistoryStageBody.Physical HistoryScratch
open scoped Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F] {W p u : ℕ} {A : HistoryGatherBody.Layout}
  (Z : SiteRun F W p A) (node : ℕ) (id : ((Fin 3→Bool)→F)→ℕ) (first : Memory W)
local notation "atSlot" => Z.entry node id first

omit [Field F] [Fintype F] in
/-- The old-node child table remains available at every chronological motif, using
only physical certificates for the slots already executed. -/
theorem child_prefix (banks : PhysicalBanks u A) (k : ℕ) (bound : k≤A.party.motifs)
    (live : ∀ j : Fin A.party.motifs,j.val<k → (Z.slot j.val (atSlot j.val)).Live node id (atSlot j.val))
    (arms : ∀ j : Fin A.party.motifs,j.val<k → (Z.slot j.val (atSlot j.val)).ArmSpace node id (atSlot j.val) u)
    (i : ℕ) (size : i<A.party.V) :
    atSlot k (A.nodePorts.starts+i)=first (A.nodePorts.starts+i) := by
  have preserved (s : ℕ) (le : s≤k) : atSlot s (A.nodePorts.starts+i)=first (A.nodePorts.starts+i) := by
    induction s with
    | zero=>rfl
    | succ s ih=>
      let j : Fin A.party.motifs:=⟨s,by omega⟩
      have earlier : j.val<k:=by change s<k;omega
      have next : atSlot (s+1)=Z.takeSlot node id (atSlot s) s := by
        simp only [entry,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
      rw [next]
      exact ((Z.slot s (atSlot s)).child_prefix_end node id (atSlot s) (banks.withMotif s) (live j earlier)
        (arms j earlier) i size).trans (ih (by omega))
  exact preserved k le_rfl

omit [Field F] [Fintype F] in
theorem child_prefix_value (banks : PhysicalBanks u A) (k : ℕ) (bound : k≤A.party.motifs)
    (live : ∀ j : Fin A.party.motifs,j.val<k → (Z.slot j.val (atSlot j.val)).Live node id (atSlot j.val))
    (arms : ∀ j : Fin A.party.motifs,j.val<k → (Z.slot j.val (atSlot j.val)).ArmSpace node id (atSlot j.val) u)
    (input : Memory W) (oldCap : ℕ) (fits : oldCap+1≤A.party.V)
    (initial : first=fillSegment A.nodePorts.starts (oldCap+1)
       (fun a=>(childWidth A.nodePorts oldCap (HistoryPartyBatchExec.numeric input) a:Word W)) input)
    (i : Fin (oldCap+1)) :
    atSlot k (A.nodePorts.starts+i.val)=
      (childWidth A.nodePorts oldCap (HistoryPartyBatchExec.numeric input) (A.nodePorts.starts+i.val):Word W) := by
  rw [Z.child_prefix node id first banks k bound live arms i.val (i.isLt.trans_le fits),initial]
  have inside : A.nodePorts.starts≤A.nodePorts.starts+i.val ∧
      A.nodePorts.starts+i.val<A.nodePorts.starts+(oldCap+1):=⟨Nat.le_add_right _ _,Nat.add_lt_add_left i.isLt _⟩
  simp only [fillSegment,ite_eq_left inside]

end
end ThreeFlat.RAM.HistoryShrinkEmitter.SiteRun

namespace ThreeFlat.RAM.HistoryShrinkEmitter.SiteSlot

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr Diagonal.TickWorkspace
open HistoryStageBody.Physical HistoryMotifJoin HistoryScratch HistoryRefreshEmitter
noncomputable section
variable {F : Type} [Field F] [Fintype F] {W u p : ℕ} {A : HistoryGatherBody.Layout}
variable (Z : SiteSlot F W p A) (node : ℕ) (id : ((Fin 3→Bool)→F)→ℕ) (input : Memory W)
local notation "first" => Z.init input
local notation "atArm" => Z.arms.entry node id first

/-- The physical archive, including the row's permanent control words, as well
as the two scratch prefix ranges used by the following selected party. -/
def prefixWords (k : ℕ) : Prop :=
  ∀ a,OutsideNode u node a ∨ (base u 18≤a ∧ a<base u 18+5*volume u) →
    atArm k a=first a

structure IssuedArm (j : Fin A.party.parties) : Prop where
  space : Z.ArmSpaceAt node id input u j
  vacant : Z.arms.select j.val=none → VacantRoom (withParty A j.val) node id (atArm j.val)
  elected : ∀ i,Z.arms.select j.val=some i →
    Elected node id (withParty A j.val) (Z.arms.plan i) (atArm j.val) (Z.arms.pairOut i)
      (Z.arms.pairCost i) (Z.children i) (Z.wire i)

omit [Field F] [Fintype F] in
private theorem advance_outside (banks : PhysicalBanks u A)
    (capacity : (A.party.motifs+2)*(A.party.parties+2)*8*32≤A.party.V)
    (motif : A.party.motif<A.party.motifs)
    (j : Fin A.party.parties) (row : Z.IssuedArm (u:=u) node id input j)
    {a : ℕ} (safe : OutsideNode u node a) :
    Z.arms.advance node id (atArm j.val) j.val a=atArm j.val a := by
  cases on:Z.arms.select j.val with
  | none=>
    have off:=vacant_outsideNode (banks.withParty j.val) id (atArm j.val) (row.vacant on)
      capacity motif j.isLt a safe
    simpa only [ArmRows.advance,ArmRows.pairOutAt,ArmRows.mapOutAt,on,vacantPass] using off
  | some i=>
    let loc : Local:=⟨A.party.motif+2,j.val+2,2,2⟩
    have valid : loc.Valid A.party.motifs A.party.parties := by
      change A.party.motif + 2 < A.party.motifs + 2 ∧ j.val + 2 < A.party.parties + 2 ∧
        (2 : ℕ) < 8 ∧ (2 : ℕ) < 32
      exact ⟨Nat.add_lt_add_right motif 2, Nat.add_lt_add_right j.isLt 2, by decide, by decide⟩
    have page : (Z.arms.plan i).gatherBase=
        atWord (base u 12) (volume u) A.party.motifs A.party.parties node loc 0 := by
      rw [row.space.result i on]
      change atWord A.party.arena A.party.V A.party.motifs A.party.parties node loc 0=_
      rw [banks.arena,banks.wordCount]
    have keep:=gather_outside_node (withParty A j.val) (Z.arms.plan i) (Z.arms.pairOut i) safe
      banks.gather banks.wordCount (banks.wordCount ▸ row.space.header)
      (fun q k lim=>banks.wordCount ▸ row.space.width i on q k lim) loc valid
      (banks.wordCount ▸ capacity) page (banks.wordCount ▸ row.space.size i on)
    have prev:=row.space.pair i on a ((banks.withParty j.val).partyAway capacity motif j.isLt a safe)
    simpa only [ArmRows.advance,ArmRows.mapOutAt,ArmRows.pairOutAt,on] using keep.trans prev

omit [Field F] [Fintype F] in
theorem issued_prefix_words (banks : PhysicalBanks u A) (nodeRoom : node<A.party.V^2)
    (capacity : (A.party.motifs+2)*(A.party.parties+2)*8*32≤A.party.V)
    (motif : A.party.motif<A.party.motifs)
    (issue : ∀ j : Fin A.party.parties,Z.prefixWords (u:=u) node id input j.val →
      Z.IssuedArm (u:=u) node id input j) (k : ℕ) (size : k≤A.party.parties) :
    Z.prefixWords (u:=u) node id input k := by
  induction k with
  | zero=>intro a _;rfl
  | succ k ih=>
    let j : Fin A.party.parties:=⟨k,by omega⟩
    have prev:=ih (by omega)
    have recd:=issue j prev
    intro a keep
    have step : atArm (k+1)=Z.arms.advance node id (atArm k) k := by
      simp only [ArmRows.entry,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [step]
    refine Eq.trans ?_ (prev a keep)
    rcases keep with outside|scratch
    · exact Z.advance_outside node id input banks capacity motif j recd outside
    · exact Z.advance_scratch node id input banks nodeRoom capacity motif j recd.space recd.vacant
        scratch.1 scratch.2

omit [Field F] [Fintype F] in
/-- Execute the scan in physical order when several parties elected by one
incident share this site. Every selected source is read in the memory left by
its predecessor. Both prefix tables and the original archive remain available. -/
theorem issued_live (banks : PhysicalBanks u A) (nodeRoom : node<A.party.V^2)
    (capacity : (A.party.motifs+2)*(A.party.parties+2)*8*32≤A.party.V)
    (motif : A.party.motif<A.party.motifs) (hdr : 3+5*A.demandCap+4*A.supplyCap≤A.party.V)
    (room : A.privateStarts+9<2^W)
    (protected_ : HistoryPartyBatchExec.Protected (privateHeader A W) input A.privateStarts 9)
    (issue : ∀ j : Fin A.party.parties,Z.prefixWords (u:=u) node id input j.val →
      Z.IssuedArm (u:=u) node id input j)
    (final : Z.prefixWords (u:=u) node id input A.party.parties →
      (∀ i,role A (atArm A.party.parties) i.val=(Z.arms.index i).val) ∧
      Chart A true node (atArm A.party.parties) Z.children Z.wire id) :
    Z.Live node id input ∧ Z.ArmSpace node id input u := by
  have words := Z.issued_prefix_words node id input banks nodeRoom capacity motif issue
  have rows (j : Fin A.party.parties) := issue j (words j.val (Nat.le_of_lt j.isLt))
  have arms : Z.ArmSpace node id input u :=
    ⟨hdr,fun j=>(rows j).space.width,fun j=>(rows j).space.result,fun j=>(rows j).space.size,
      fun j=>(rows j).space.pair⟩
  obtain ⟨role,chart⟩:=final (words _ le_rfl)
  have vacant:=fun j=>(rows j).vacant
  exact ⟨⟨room,protected_,fun j=>(rows j).elected,vacant,
    Z.later node id input banks chart.capacity arms vacant,role,chart⟩,arms⟩

end
end ThreeFlat.RAM.HistoryShrinkEmitter.SiteSlot

namespace ThreeFlat.RAM.HistoryShrinkEmitter
open private large_stride from OAI.ThreeFlat.RAM.HistoryShrinkPlacement
open Computability.VPVNP.BurstRAM PhysicalPinsExpr Diagonal.TickWorkspace NavigationNodeRows HistoryGatherBody
open HistoryStageBody.Physical HistoryPartyBatchExec HistoryMotifJoin
open scoped Fin.CommRing
noncomputable section
variable {u : ℕ} {A : HistoryGatherBody.Layout} {m : Memory (16*u^10)}
local notation "W₁" => 16*u^10
local notation "V₁" => volume u

/-- Issue the actual old half-width prefix from the retained ordered vector
and S13 cache. The singleton refresh uses the same two bank words. -/
theorem child_starts_archive {s : Layer} (data : LayerData s) (j : Fin s.count)
    (banks : PhysicalBanks u A) (ports : A.nodePorts=nodes u) (age : 16≤u) (big : 128≤V₁)
    (nodeBound : s.first+j.val<V₁^2) (positive : 0<s.childCount) (few : s.childCount≤V₁)
    (b : Banks) (bNodes : b.nodes=base u 44)
    (current : numeric m (base u 18)=s.first+j.val+1)
    (dir : HistoryStageSetup.DirectoryRow b s j m) (read : data.Reads (numeric m))
    (cells : data.Footprint (fun i=>base u 19≤ i ∧ i<2^W₁) (numeric m))
    (ids : ∀ k : Fin s.childCount,data.child j k<V₁^2) :
    (HistoryNodePorts.phase W₁ A.nodePorts s.childCount).Exec m
      (fillSegment A.nodePorts.starts (s.childCount+1)
        (fun a=>(childWidth A.nodePorts s.childCount (numeric m) a:Word W₁)) m)
      (4+(s.childCount+1)*(2*(HeaderScan.closed (w:=W₁) (childPrefix A.nodePorts s.childCount)).binds+4)) := by
  let id:=s.first+j.val
  have ctrl : A.nodePorts.cursor=base u 18:=by rw [ports];rfl
  have cache : A.nodePorts.cache=base u 13:=by rw [ports];rfl
  have nodeBase : A.nodePorts.nodes=base u 44:=by rw [ports];rfl
  have cur : numeric m A.nodePorts.cursor-1=id:=by rw [ctrl,current];simp [id]
  have phys:=directory_address_space (u:=u) age big nodeBound
  have strideEnough : 10*V₁ ≤ Diagonal.TickWorkspace.stride u := large_stride (V:=V₁) (by omega)
  have full:=word_space (u:=u) (i:=18) (by omega) (by omega)
  have curFits : A.nodePorts.cursor<2^W₁:=by rw [ctrl];omega
  have room : A.nodePorts.starts+(s.childCount+1)<2^W₁:=by rw [banks.childStarts];omega
  have nroom : A.nodePorts.nodes+8*((m A.nodePorts.cursor).val-1)+4<2^W₁:=by
    change A.nodePorts.nodes+8*(numeric m A.nodePorts.cursor-1)+4<_;rw [nodeBase,cur];dsimp [id];omega
  have pointerRoom : s.children+j.val*s.childCount<2^W₁ := by simpa using (cells.child j ⟨0,positive⟩).2
  have raw (k : Fin s.childCount) :
      (m ((m (A.nodePorts.nodes+8*((m A.nodePorts.cursor).val-1)+3)).val+k.val)).val=data.child j k := by
    change numeric m (numeric m (A.nodePorts.nodes+8*(numeric m A.nodePorts.cursor-1)+3)+k.val)=_
    rw [nodeBase,cur,←bNodes]
    have pp:=congrArg Fin.val dir.childPtr
    rw [Fin.val_cast_of_lt pointerRoom] at pp
    rw [show numeric m (b.nodes+8*id+3)=s.children+j.val*s.childCount from pp]
    exact read.child j k
  have ptrRoom (k : Fin s.childCount) :
      (m (A.nodePorts.nodes+8*((m A.nodePorts.cursor).val-1)+3)).val+k.val<2^W₁ := by
    change numeric m (A.nodePorts.nodes+8*(numeric m A.nodePorts.cursor-1)+3)+k.val<_
    rw [nodeBase,cur,←bNodes]
    rw [show numeric m (b.nodes+8*id+3)=s.children+j.val*s.childCount from
      (congrArg Fin.val dir.childPtr).trans (Fin.val_cast_of_lt pointerRoom)]
    exact (cells.child j k).2
  have size : 16*V₁^2 ≤ Diagonal.TickWorkspace.stride u := by
    change 16*V₁^2≤V₁^4
    calc _≤V₁^2*V₁^2:=Nat.mul_le_mul_right _ (by nlinarith)
         _=V₁^4:=by ring
  have cacheLimit:=word_space (u:=u) (i:=13) (by omega) (by omega)
  have cr (k : Fin s.childCount) :
      A.nodePorts.cache+8*(m ((m (A.nodePorts.nodes+8*((m A.nodePorts.cursor).val-1)+3)).val+k.val)).val+5<2^W₁ := by
    rw [cache,raw];have h:=ids k;omega
  have count : numeric m (A.nodePorts.nodes+8*(numeric m A.nodePorts.cursor-1)+4)=s.childCount:=by
    rw [nodeBase,cur,←bNodes]
    exact (congrArg Fin.val dir.childCount).trans (Fin.val_cast_of_lt (by omega))
  have numId : (HistoryNodePorts.id A.nodePorts).value (fun _=>0) m (fun _=>0)=(id:Word W₁) := by
    have ff : (HistoryNodePorts.id A.nodePorts).Fits W₁ (fun _=>0) (numeric m) (fun _=>0):=
      ⟨⟨trivial,curFits⟩,trivial,(m A.nodePorts.cursor).isLt,by change 1<2^W₁;omega⟩
    have cv:=(HistoryNodePorts.id A.nodePorts).value_eq_natural (fun _=>0) (numeric m) (fun _=>0) ff
    simpa only [word_numeric,Fin.cast_val_eq_self,Nat.cast_zero] using cv.trans (congrArg (fun x:ℕ=>(x:Word W₁)) cur)
  have addr:=nodeAddress_at nodeBase numId
  have point : wordAt m (HistoryMotifJoin.nodeAddress A.nodePorts m) 3=((s.children+j.val*s.childCount:ℕ):Word W₁) := by
    rw [addr];unfold wordAt
    change m (((base u 44+8*id:ℕ):Word W₁)+((3:ℕ):Word W₁)).val=_
    rw [←Nat.cast_add,Fin.val_cast_of_lt (by dsimp [id];omega),←bNodes]
    exact dir.childPtr
  have observed:=ChildReadCells.of_archive data j age big id nodeBound ctrl cache addr point read cells ids
  intro labels registers slots machine pc reg pub exit installed params cfg input entry initial
  exact child_starts A.nodePorts s.childCount m count.le room
    (childPrefix_physical banks big s.childCount few observed)
    (HistoryNodePorts.clipped_fits A.nodePorts s.childCount m curFits room nroom ptrRoom cr)
    machine pc reg pub exit installed params cfg input entry initial

end
end ThreeFlat.RAM.HistoryShrinkEmitter

end OAI
