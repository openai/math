import OAI.ThreeFlat.RAM.HistoryJoinTreeCost
import OAI.ThreeFlat.RAM.HistoryStageTariff
import OAI.ThreeFlat.RAM.HistoryShrinkEmitter
import OAI.ThreeFlat.RAM.HistoryMotifRates

namespace OAI
/-! # Native join, gather and site costs -/

set_option quotPrecheck false

namespace ThreeFlat.RAM.HistoryMotifJoin

open Computability.VPVNP.BurstRAM PrivateRAM HistoryStageBody.Physical HistoryBoundedBody HistoryJoinScan
open Diagonal.HistoryContraction PhysicalProcedure
open scoped BigOperators Classical
noncomputable section

/-- Exact elapsed time in `join_exec`, including command materialization and
relocation of each of the child's rows. -/
theorem join_ticks_le {W n h p : ℕ} {F : Type*} {arity : Fin n→ℕ}
    (A B : HistoryGatherBody.Layout) (same : Same A B) (g : Bool) (T : HistoryBoundedJoin.Hub)
    (N : ∀ i,Tree F (arity i)) (wire : ∀ i,Fin (arity i)→BitSource h p)
    (id : ((Fin 3→Bool)→F)→ℕ) (head : Fin n→Header ℕ) (m : Memory W)
    (argc : T.argc=n) (bound : n≤joinCap B g) :
    let group:=groupBuild A g T m
    let jobs:=Tape.tape (fun i=>(N i).compile) wire id head
    4+(rows A W g).length*(2*(joinHeader A W g).binds+4)+group.ticks jobs ≤
      joinRate B g*(1+(Tree.join h n arity wire N).resources) := by
  let cap:=joinCap B g
  let cells:=(Tree.join h n arity wire N).resources
  let fee:=100*(1+joinResources cap)
  let G:=groupBuild A g T m
  let jobs:=Tape.tape (W:=W) (fun i=>(N i).compile) wire id head
  have hc : G.cap=cap := by
    change (if g then A.party.parties else A.party.motifs)=_
    simp only [cap,joinCap,same.parties,same.motifs]
  have headers : (rows A W g).length=7+7*cap := by
    rw [rows_len]; simp only [cap,joinCap,same.parties,same.motifs]
  have base:=G.typed_ticks_le (fun i=>(N i).compile) wire id head
  have argc' : G.hub.argc=n := argc
  rw [argc',hc] at base
  have units := join_tree_units N wire (show n≤cap from bound)
  have paid : G.ticks jobs≤fee*((5+2*cap)*(1+cells)) := base.trans (Nat.mul_le_mul_left _ units)
  let boot:=4+(7+7*cap)*(2*(joinHeader B 1 g).binds+4)
  have init : boot≤boot*(1+cells) := Nat.le_mul_of_pos_right _ (by omega)
  change 4+(rows A W g).length*(2*(joinHeader A W g).binds+4)+G.ticks jobs≤joinRate B g*(1+cells)
  rw [headers,joinHeader_work (U:=1) A B g same.parties same.motifs]
  change boot+G.ticks jobs≤(boot+fee*(5+2*cap))*(1+cells)
  rw [Nat.add_mul boot (fee*(5+2*cap)) (1+cells),Nat.mul_assoc fee (5+2*cap) (1+cells)]
  exact Nat.add_le_add init paid

private theorem sum_range_le (n : ℕ) (f : ℕ→ℕ) (c : ℕ) (hf : ∀ i<n,f i≤c) :
    ((List.range n).map f).sum≤n*c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.map_append,List.sum_append,Nat.succ_mul]
    simpa using Nat.add_le_add (ih (fun i hi=>hf i (by omega))) (hf n (by omega))

/-- The real party bundle is scanned in its fixed public order. Every absent
role pays its own bounded pair and gather initializations. -/
theorem motif_ticks_joint (A B : HistoryGatherBody.Layout) (same : Same A B) {W work pair gather last : ℕ}
    (pairTax gatherTax : ℕ→ℕ) (positive : 0<work)
    (joint : ∀ j<A.party.parties,pairTax j+gatherTax j≤(pair+gather)*work)
    (lastPay : last≤joinRate B true*work) :
    4+9*(2*(privateHeader A W).binds+4)+
        ((List.range A.party.parties).map (fun j=>pairTax j+gatherTax j)).sum+last ≤
      motifRate B pair gather*work := by
  rw [privateHeader_work (U:=1) A B same.mode]
  have boot:=Nat.le_mul_of_pos_right (motifBoot B) positive
  have parties:=sum_range_le A.party.parties (fun j=>pairTax j+gatherTax j) ((pair+gather)*work)
    joint
  rw [same.parties,←Nat.mul_assoc] at parties
  rw [same.parties]
  dsimp only [motifRate]
  rw [Nat.add_mul,Nat.add_mul]
  exact Nat.add_le_add (Nat.add_le_add boot parties) lastPay

theorem motif_ticks_le (A B : HistoryGatherBody.Layout) (same : Same A B) {W work pair gather last : ℕ}
    (pairTax gatherTax : ℕ→ℕ) (positive : 0<work)
    (pairPay : ∀ j<A.party.parties,pairTax j≤pair*work)
    (gatherPay : ∀ j<A.party.parties,gatherTax j≤gather*work)
    (lastPay : last≤joinRate B true*work) :
    4+9*(2*(privateHeader A W).binds+4)+
        ((List.range A.party.parties).map (fun j=>pairTax j+gatherTax j)).sum+last ≤
      motifRate B pair gather*work := by
  apply motif_ticks_joint A B same pairTax gatherTax positive _ lastPay
  intro j hj
  rw [Nat.add_mul]
  exact Nat.add_le_add (pairPay j hj) (gatherPay j hj)

/-- The degree-refresh kernel visits motif zero once following the true node-port scan. -/
theorem kernel_refresh_ticks (B : HistoryGatherBody.Layout) {oldCap pair gather work fresh : ℕ}
    (positive : 0<work) (pay : fresh≤ motifRate B pair gather*work) :
    HistoryNodePorts.phaseCost oldCap+fresh≤kernelRate B oldCap pair gather*work := by
  have a:=Nat.le_mul_of_pos_right (HistoryNodePorts.phaseCost oldCap) positive
  have b : motifRate B pair gather ≤ (B.party.motifs+1)*motifRate B pair gather :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos B.party.motifs)
  have m := pay.trans (Nat.mul_le_mul_right work b)
  unfold kernelRate
  rw [Nat.add_mul (HistoryNodePorts.phaseCost oldCap+_) (joinRate B false) work,
    Nat.add_mul (HistoryNodePorts.phaseCost oldCap) ((B.party.motifs+1)*motifRate B pair gather) work]
  exact (Nat.add_le_add a m).trans (Nat.le_add_right _ _)

/-- The shrink kernel visits every public motif slot, then runs its site-level join. -/
theorem kernel_shrink_ticks (A B : HistoryGatherBody.Layout) (same : Same A B)
    {oldCap pair gather work last : ℕ} (tax : ℕ→ℕ) (positive : 0<work)
    (body : ∀ j<A.party.motifs,tax j≤ motifRate B pair gather*work)
    (root : last≤joinRate B false*work) :
    HistoryNodePorts.phaseCost oldCap+((List.range A.party.motifs).map tax).sum+last≤
      kernelRate B oldCap pair gather*work := by
  have a:=Nat.le_mul_of_pos_right (HistoryNodePorts.phaseCost oldCap) positive
  have head:=sum_range_le A.party.motifs tax (motifRate B pair gather*work) body
  rw [same.motifs,←Nat.mul_assoc] at head
  rw [same.motifs]
  have grow:=Nat.mul_le_mul_right work (Nat.mul_le_mul_right (motifRate B pair gather) (Nat.le_succ B.party.motifs))
  unfold kernelRate
  rw [Nat.add_mul,Nat.add_mul]
  exact Nat.add_le_add (Nat.add_le_add a (head.trans grow)) root

end
end ThreeFlat.RAM.HistoryMotifJoin

namespace ThreeFlat.RAM.HistoryRefreshEmitter

open Computability.VPVNP.BurstRAM PrivateRAM HistoryStageBody.Physical HistoryBoundedBody HistoryJoinScan
open Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree HistoryMotifJoin
open HistoryGatherExecution HistoryGatherBody PhysicalProcedure
open scoped BigOperators Classical
noncomputable section

variable {W a b p : ℕ} {F : Type*}

theorem vacant_map_ticks (A B : HistoryGatherBody.Layout) (same : Same A B) :
    vacantMapCost A W ≤ schemaCost B := by
  have header : headerCharge W A=headerCharge 0 B := by
    simp only [headerCharge,header_size,header_work (W:=W) (U:=0) A B same.mode same.demand same.supply,
      same.demand,same.supply]
  unfold vacantMapCost schemaCost
  rw [header,same.demand,same.supply]
  omega

/-- Includes each executed empty pair and all of its empty source slices.
Only the elected arm uses a tile-dependent number of copies. -/
theorem roster_ticks (A B : HistoryGatherBody.Layout) (same : Same A B)
    (node : ℕ) (winner : Fin A.party.parties) (id : ((Fin 3→Bool)→F)→ℕ)
    (stage occupiedPair occupiedGather : Memory W) (s e k bits d r pairTicks gatherTicks readRate : ℕ)
    (activePair : pairTicks≤partyTariff s e k bits d*(W+1)^3*(1+r))
    (activeGather : gatherTicks≤readRate*(1+r)) :
    let units:=(W+1)^3*(1+r)
    ∀ j,choosePairCost A node winner id stage occupiedPair occupiedGather pairTicks j≤
      partyTariff s e k bits d*units ∧
      chooseMapCost (W:=W) A winner gatherTicks j≤(schemaCost B+readRate)*units := by
  intro units j
  have pos : 0<units := by dsimp only [units];positivity
  have paidCopies : 1+r≤units := Nat.le_mul_of_pos_left _ (by positivity)
  by_cases selected : j=winner.val
  · rw [choosePairCost,chooseMapCost,ite_eq_left selected,ite_eq_left selected]
    exact ⟨by simpa only [Nat.mul_assoc] using activePair,
      activeGather.trans (Nat.mul_le_mul (Nat.le_add_left _ _) paidCopies)⟩
  · rw [choosePairCost,chooseMapCost,ite_eq_right selected,ite_eq_right selected]
    let mid:=entryOf A node winner id stage occupiedPair occupiedGather j
    let slot:=rawArm A j
    have empty:=vacant_pair_tariff slot.party mid s e k bits d
    have room : 1+0≤1+r := by omega
    have more:=Nat.mul_le_mul_left (partyTariff s e k bits d*(W+1)^3) room
    have map:=vacant_map_ticks (W:=W) slot B
      (⟨same.mode,same.demand,same.supply,same.parties,same.motifs⟩ : Same slot B)
    have rate : schemaCost B ≤ schemaCost B+readRate := Nat.le_add_right _ _
    refine ⟨?_, map.trans (rate.trans (Nat.le_mul_of_pos_right _ pos))⟩
    change vacantPairCost slot mid ≤ partyTariff s e k bits d * ((W+1)^3 * (1+r))
    unfold vacantPairCost
    exact (empty.trans more).trans_eq (Nat.mul_assoc _ _ _)

/-- The exact charge returned by `emit_from_image` for the one occupied party.
Its intrinsic tree cost and all real histogram copies are paid once. -/
theorem emit_ticks (A B : HistoryGatherBody.Layout) (same : Same A B)
    (node : ℕ) (winner : Fin A.party.parties) (L : Tree F a) (R : Tree F b)
    (wire : Fin (a+b)→BitSource 0 p) (id : ((Fin 3→Bool)→F)→ℕ)
    (stage occupiedPair occupiedGather beforeJoin : Memory W) (oldCap s e k bits d r pairTicks gatherTicks readRate : ℕ)
    (activePair : pairTicks≤partyTariff s e k bits d*(W+1)^3*(1+r))
    (activeGather : gatherTicks≤readRate*(1+r)) :
    let C:=withMotif A 0
    let G:=groupBuild C true (groupHub C beforeJoin true node p 0 1) beforeJoin
    let jobs:=Tape.tape (W:=W) (fun _ : Fin 1=>(pair L R).compile) (fun _ : Fin 1=>wire) id
      (fun _ : Fin 1=>rootHeader A node winner (a+b) p)
    let pairs:=choosePairCost A node winner id stage occupiedPair occupiedGather pairTicks
    let maps:=chooseMapCost (W:=W) A winner gatherTicks
    HistoryNodePorts.phaseCost oldCap+(4+9*(2*(privateHeader C W).binds+4)+
      ((List.range A.party.parties).map (fun j=>pairs j+maps j)).sum+
      (4+(HistoryMotifJoin.rows C W true).length*(2*(joinHeader C W true).binds+4)+G.ticks jobs)) ≤
      kernelRate B oldCap (partyTariff s e k bits d) (schemaCost B+readRate)*
        ((W+1)^3*(1+r)+(resultTree L R wire).resources) := by
  intro C G jobs pairs maps
  let rUnits:=(W+1)^3*(1+r)
  let work:=rUnits+(resultTree L R wire).resources
  have cSame : Same C B:=⟨same.mode,same.demand,same.supply,same.parties,same.motifs⟩
  have arms:=roster_ticks A B same node winner id stage occupiedPair occupiedGather s e k bits d r
    pairTicks gatherTicks readRate activePair activeGather
  have pos : 0<rUnits := by dsimp only [rUnits];positivity
  have after : rUnits≤work := Nat.le_add_right _ _
  have tree : 1+(resultTree L R wire).resources≤work := by dsimp only [work];omega
  have n : 1≤joinCap B true := by
    change 1≤B.party.parties
    exact (Nat.zero_lt_of_lt winner.isLt).trans_eq same.parties
  have last:=join_ticks_le C B cSame true (groupHub C beforeJoin true node p 0 1)
    (fun _ : Fin 1=>pair L R) (fun _ : Fin 1=>wire) id
    (fun _ : Fin 1=>rootHeader A node winner (a+b) p) beforeJoin rfl n
  apply kernel_refresh_ticks B (oldCap:=oldCap) (by omega : 0<work)
  apply motif_ticks_le C B cSame pairs maps (by omega : 0<work)
  · exact fun j _=>(arms j).1.trans (Nat.mul_le_mul_left _ after)
  · exact fun j _=>(arms j).2.trans (Nat.mul_le_mul_left _ after)
  · exact last.trans (Nat.mul_le_mul_left _ tree)

end
end ThreeFlat.RAM.HistoryRefreshEmitter

namespace ThreeFlat.RAM.HistoryShrinkEmitter

open Computability.VPVNP.BurstRAM PrivateRAM HistoryStageBody.Physical HistoryBoundedBody HistoryJoinScan
open Diagonal.HistoryContraction HistoryMotifJoin PhysicalProcedure
open scoped Classical

/-- The shrink emitter uses this same typed relocation at the occupied-motif
root and again when combining the actual active motifs at the stage site. -/
theorem group_ticks {W n h p : ℕ} {F : Type} {arity : Fin n→ℕ}
    (A B : HistoryGatherBody.Layout) (same : Same A B) (group : Bool) (node : ℕ) (m : Memory W)
    (N : ∀ i,Tree F (arity i)) (wire : ∀ i,Fin (arity i)→BitSource h p)
    (id : ((Fin 3→Bool)→F)→ℕ) (count : n≤joinCap B group) :
    let family:=fun i=>(N i).compile
    let q:=copy A group node m family (p:=p) (h:=h)
    let jobs:=Tape.tape (W:=W) family wire id q
    let P:=build A group node m (p:=p) (h:=h) (n:=n)
    4+(HistoryMotifJoin.rows A W group).length*(2*(joinHeader A W group).binds+4)+P.ticks jobs≤
      joinRate B group*(1+(Tree.join h n arity wire N).resources) := by
  exact join_ticks_le A B same group (groupHub A m group node p h n) N wire id _ m rfl count

/-- Native private-word initialization, all party pairs and gathers, and the
typed occupied-group output at one raw shrink motif slot. -/
theorem emit_motif_ticks {W n h p : ℕ} {F : Type} {arity : Fin n→ℕ}
    (A B : HistoryGatherBody.Layout) (same : Same A B) (node : ℕ) (m : Memory W)
    (N : ∀i,Tree F (arity i)) (wire : ∀i,Fin (arity i)→BitSource h p)
    (id : ((Fin 3→Bool)→F)→ℕ) (size : n≤A.party.parties)
    (r pairRate mapRate : ℕ) (pairTax mapTax : ℕ→ℕ)
    (joint : ∀i<A.party.parties,pairTax i+mapTax i≤(pairRate+mapRate)*((W+1)^3*(1+r))) :
    4+9*(2*(privateHeader A W).binds+4)+((List.range A.party.parties).map (fun i=>pairTax i+mapTax i)).sum+
        joinTicks A true node m (fun i=>(N i).compile) wire id ≤
      motifRate B pairRate mapRate*((W+1)^3*(1+r)+(Tree.join h n arity wire N).resources) := by
  let root:=(Tree.join h n arity wire N).resources
  let units:=(W+1)^3*(1+r)
  let work:=units+root
  have positive : 0<units := by dsimp only [units];positivity
  have left : units≤work := Nat.le_add_right _ _
  have right : 1+root≤work := by dsimp only [work];omega
  have fitCap : n≤joinCap B true := by
    simpa only [joinCap,ite_true,same.parties] using size
  apply motif_ticks_joint A B same pairTax mapTax (positive.trans_le left)
  · exact fun i hi=>(joint i hi).trans (Nat.mul_le_mul_left _ left)
  · exact (group_ticks A B same true node m N wire id fitCap).trans (Nat.mul_le_mul_left _ right)

section PhysicalSite
open HistoryMotifJoin BitNetwork.Ordered
variable {W n h p : ℕ} {F : Type} (A B : HistoryGatherBody.Layout) (node : ℕ) (m : Memory W)
  (id : ((Fin 3→Bool)→F)→ℕ)
open Diagonal Diagonal.MotifOuterTerms Diagonal.MotifKernel Diagonal.MotifBinaryPacking Diagonal.HistogramTileNetwork
open LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector
variable {J E S H Z : Type} [Field F] [Fintype J] [Nonempty J] [Fintype E] [Fintype S]
  [Fintype H] [DecidableEq H] [Nonempty H] [Fintype Z] [DecidableEq Z] {k d r s c b : ℕ}
  (D : PortGraph J E) (G : Supply J S) (place : J→Z) (v : Z) (width base : E→ℕ) (sw : H→S→ℕ)
  (code : H ↪ Fin (2^k)) (letter : H≃Fin s) (z : Histogram H r) (edges : Fin b≃Absorbed (ports G) place v)
  (parts : Fin c≃{j // place j=v}) {e t : Fin c→ℕ} (sup : ∀ i,Fin (e i)≃(ports G).Port (parts i).val)
  (dem : ∀ i,Fin (t i)≃D.Port (parts i).val) (fit : ∀ i q j,sw q (sup i j).1.1≤d)
  (table : ∀ q j,D.State (fun a=>Fin (2^base a)) j→(ports G).State (fun a=>Fin (2^sw q a)) j→F)
  (comp : BitNetwork F ((r*d)+(r*d+r*d))) (cnt : BitNetwork F (r+(r+r)))
  (old : ∀ i,(a : D.Port (parts i).val)→Fin (width a.1.1)→BitSource (HistogramTileNetwork.order G place v sw z edges (k:=k)).bits p)
  (cross : (x : ExternalAt (ports G) place v)→Fin (histWidth sw z x.val.val+r*k)→Fin p)
local notation "childTree" => fun i=>Tree.party D G (parts i).val base (hd D base code parts dem i) (sup i) sw
  (fit i) table letter z comp cnt
local notation "nets" => fun i=>(childTree i).compile
local notation "wires" => localWire D G place v width base sw code z edges parts sup dem old cross
local notation "tree" => Tree.occupiedTree D G place v width base sw code letter z edges parts sup dem fit table comp cnt old cross

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] [Fintype Z] in
theorem emit_occupied_ticks (same : Same A B) (geometry : Chart A true node m nets wires id) :
    joinTicks A true node m nets wires id≤joinRate B true*(1+(tree).resources) := by
  have fitCap : c≤joinCap B true := by
    simpa only [joinCap,ite_true,same.parties] using geometry.size
  exact group_ticks A B same true node m childTree wires id fitCap

variable {U I Vtx : Type} [Fintype U] [Fintype I] [Fintype Vtx] [DecidableEq Vtx]
  (put : U→I→Vtx) (site : Vtx) (motifs : Fin n≃Active put site)
  (piece : ∀ _u : Active put site,Tree F p)
local notation "pieces" => fun i=>(piece (motifs i)).compile
local notation "pins" => fun (_:Fin n) (j:Fin p)=>(BitSource.pin j : BitSource 0 p)
local notation "assembled" => Tree.activeTree put site motifs piece

omit [Field F] [Fintype U] [Fintype I] [Fintype Vtx] [DecidableEq Vtx] in
theorem emit_active_ticks (same : Same A B) (size : n≤A.party.motifs) :
    joinTicks A false node m pieces pins id≤joinRate B false*(1+(assembled).resources) := by
  have fitCap : n≤joinCap B false := by
    exact size.trans_eq same.motifs
  exact group_ticks A B same false node m (fun i=>piece (motifs i)) pins id fitCap

omit [Field F] [Fintype U] [Fintype I] [Fintype Vtx] [DecidableEq Vtx] in
/-- Every occupied subtree issued by the chronological motif loop belongs to
the site's native active-root join. -/
private theorem piece_le (j : Fin n) : (piece (motifs j)).resources≤(assembled).resources := by
  have single (f : Fin n→ℕ) : f j≤∑ i,f i :=
    Finset.single_le_sum (f:=f) (fun i _=>Nat.zero_le _) (Finset.mem_univ j)
  have bits:=single (fun i=>(piece (motifs i)).bits)
  have rows:=single (fun i=>(piece (motifs i)).rows)
  have nodes:=single (fun i=>(piece (motifs i)).nodes)
  have pinCount:=single (fun i=>(piece (motifs i)).footprint.pins)
  simp only [Tree.resources,Stage.treeWork,Tree.activeTree,Tree.bits,Tree.rows,Tree.nodes,Tree.footprint]
  omega

omit [Field F] [Fintype U] [Fintype I] [Fintype Vtx] [DecidableEq Vtx] in
/-- The exact site-level cost of `kernel_shrink`. Active motifs occur in the
archived dense prefix. Each remaining public motif runs the empty group. -/
theorem emit_site_ticks (same : Same A B) (size : n≤A.party.motifs)
    (oldCap pairRate mapRate : ℕ) (copies : Active put site→ℕ) (tax : ℕ→ℕ)
    (perMotif : ∀ j<A.party.motifs,
      tax j≤ motifRate B pairRate mapRate*((W+1)^3*
        (1+(if hj:j<n then copies (motifs ⟨j,hj⟩) else 0))+
        (if hj:j<n then (piece (motifs ⟨j,hj⟩)).resources else 1))) :
    HistoryNodePorts.phaseCost oldCap+((List.range A.party.motifs).map tax).sum+
        joinTicks A false node m pieces pins id≤
      kernelRate B oldCap pairRate mapRate*((W+1)^3*(1+∑ i : Fin n,copies (motifs i))+1+(assembled).resources) := by
  let total:=∑ i : Fin n,copies (motifs i)
  let work:=(W+1)^3*(1+total)+1+(assembled).resources
  have positive : 0<work := by dsimp only [work];omega
  apply kernel_shrink_ticks A B same tax positive
  · intro j hj
    apply (perMotif j hj).trans
    apply Nat.mul_le_mul_left
    by_cases found : j<n
    · simp only [dite_eq_left found]
      let i : Fin n:=⟨j,found⟩
      have cnt : copies (motifs i)≤total := Finset.single_le_sum (f:=fun k=>copies (motifs k))
        (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
      have pay:=Nat.mul_le_mul_left ((W+1)^3) (Nat.add_le_add_left cnt 1)
      have pieceCost:=piece_le put site motifs piece i
      change (W+1)^3*(1+copies (motifs i))+(piece (motifs i)).resources≤work
      dsimp only [work]
      omega
    · simp only [dite_eq_right found,Nat.add_zero,Nat.mul_one]
      have t:=Nat.le_mul_of_pos_right ((W+1)^3) (by omega : 0<1+total)
      dsimp only [work]
      omega
  · exact (emit_active_ticks A B node m id put site motifs piece same size).trans
      (Nat.mul_le_mul_left _ (by dsimp only [work];omega))

end PhysicalSite

end ThreeFlat.RAM.HistoryShrinkEmitter

namespace ThreeFlat.RAM.HistoryStageBody.StageRun

open Diagonal.HistoryContraction
open scoped BigOperators Classical

/-- Pass the actual local kernel charge to the same selected ancestor recurrence
that pays for the resulting site tree. The node's own reserve covers the empty
shrink slot. -/
theorem kernel_ticks_from_site {F Pins : Type*} [CommSemiring F] {S : Shape} {R : Rewrite S F} {b : Fin R.count}
    {old : Form S Pins} {newForm : Form (R.target b) Pins} (D : Stage R b old newForm)
    (forest : Forest F old) (v : (R.target b).Site) (prev : S.Site→ℕ)
    {W copies fresh unit schema rate ticks : ℕ} (paidCopies : 1+copies≤fresh)
    (width : (W+1)^3≤unit) (priced : schema≤rate)
    (run : ticks ≤ schema*((W+1)^3*(1+copies)+1+(D.root v).resources)) :
    ticks≤rate*(unit*(fresh+∑ i,prev (D.child v i).val)+(D.assemble forest v).resources) := by
  have paid := Nat.mul_le_mul width (paidCopies.trans (Nat.le_add_right _ (∑ i,prev (D.child v i).val)))
  have tree : 1+(D.root v).resources≤(D.assemble forest v).resources := by
    rw [Stage.resources_assemble]
    unfold Stage.freshResources
    omega
  exact run.trans (Nat.mul_le_mul priced (by omega))

end ThreeFlat.RAM.HistoryStageBody.StageRun

namespace ThreeFlat.RAM.HistoryStageBody.Physical

open HistoryMotifJoin HistoryGatherExecution HistoryRefreshEmitter Diagonal.PhysicalStage
open private term_le_sum from OAI.ThreeFlat.RAM.HistoryMotifRates
open scoped Classical

/-- The exact selected catalogue page supplies the demand widths used by the gather tariff. -/
theorem partyMapRate_bound {F : Type} (B : HistoryGatherBody.Layout) (p : Party F) (r ticks : ℕ)
    (actual : ticks ≤ schemaCost B*(1+r*(p.port.digits+p.supplies*(p.maxDigit+p.codeBits)+
      p.supplies*p.codeBits+p.header+p.supplies*p.maxDigit))) :
    ticks≤partyMapRate B p*(1+r) := by
  let k:=p.port.digits+p.supplies*(p.maxDigit+p.codeBits)+p.supplies*p.codeBits+p.header+p.supplies*p.maxDigit
  change ticks ≤ schemaCost B*(1+r*k) at actual
  have h : partyMapRate B p=schemaCost B*(1+k) := by dsimp [partyMapRate,k];ring
  rw [h,Nat.mul_assoc]
  apply actual.trans (Nat.mul_le_mul_left _ _)
  calc
    1+r*k ≤ (1+k)*(1+r) := by simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]; rw [Nat.mul_comm k r]; omega

theorem grid_kernel_same {F : Type} (G : Grid F) (u start : ℕ) (a : Archive) :
    Same (layout u a (G.family start)) (kernelTemplate G) := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem grid_rate_le_block {F : Type} [Field F] [Fintype F] (B : Block F) (G : Grid F)
    (gmem : G∈grids B) : gridKernelRate G≤blockKernelRate B :=
  (term_le_sum (grids B) gridKernelRate G gmem).trans (Nat.le_add_left _ _)

theorem party_rates_in_grid {F : Type} (G : Grid F) (p : Party F) (pmem : p∈G.rows) :
    partyRate p≤gridPairRate G ∧ partyMapRate (kernelTemplate G) p≤gridMapRate G :=
  ⟨(term_le_sum G.rows partyRate p pmem).trans (Nat.le_add_left _ _),
   (term_le_sum G.rows (partyMapRate (kernelTemplate G)) p pmem).trans (Nat.le_add_left _ _)⟩

/-- All executed raw slots and all grid cells use a single block rate, uniformly in
the age, word width, chronological addresses, and selected histogram. -/
theorem block_kernel_rate {F : Type} [Field F] [Fintype F] (B : Block F) (G : Grid F) (p : Party F)
    (gmem : G∈grids B) (pmem : p∈G.rows) :
    let ref:=layout 0 ⟨0,0,0,0,0,0⟩ (G.family 0)
    kernelRate ref G.childBound (partyRate p) (schemaCost ref+partyMapRate ref p)≤blockKernelRate B := by
  let ref:=kernelTemplate G
  have fee : partyRate p≤gridPairRate G := (term_le_sum G.rows partyRate p pmem).trans (Nat.le_add_left _ _)
  have gather:=term_le_sum G.rows (partyMapRate ref) p pmem
  have motif : motifRate ref (partyRate p) (schemaCost ref+partyMapRate ref p)≤
      motifRate ref (gridPairRate G) (gridMapRate G) := by
    unfold motifRate gridMapRate
    gcongr
  have body : kernelRate ref G.childBound (partyRate p) (schemaCost ref+partyMapRate ref p)≤gridKernelRate G := by
    unfold gridKernelRate kernelRate
    gcongr
  exact body.trans ((term_le_sum (grids B) gridKernelRate G gmem).trans (Nat.le_add_left _ _))

open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree
open HistoryBoundedBody HistoryJoinScan

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1200000 in
/-- A real occupied refresh site, with the two elected child calls and all
other actual arms, is paid at one constant for the immutable block. -/
theorem refresh_block_ticks {F : Type} [Field F] [Fintype F] {W a b p : ℕ}
    (B : Block F) (grid : Grid F) («rec» : Party F) (gmem : grid∈grids B) (pmem : «rec»∈grid.rows)
    (A : HistoryGatherBody.Layout) (same : Same A (kernelTemplate grid)) (node : ℕ) (winner : Fin A.party.parties)
    (L : Tree F a) (R : Tree F b) (wire : Fin (a+b)→BitSource 0 p) (id : ((Fin 3→Bool)→F)→ℕ)
    (stage occupiedPair occupiedGather beforeJoin : Memory W) (r pairTicks gatherTicks : ℕ)
    (pair : pairTicks≤partyRate «rec»*(W+1)^3*(1+r))
    (gather : gatherTicks≤partyMapRate (kernelTemplate grid) «rec»*(1+r)) :
    let C:=withMotif A 0
    let P:=groupBuild C true (groupHub C beforeJoin true node p 0 1) beforeJoin
    let jobs:=Tape.tape (W:=W) (fun _ : Fin 1=>(Diagonal.HistoryContraction.Tree.pair L R).compile)
      (fun _ : Fin 1=>wire) id (fun _ : Fin 1=>rootHeader A node winner (a+b) p)
    let pairs:=choosePairCost A node winner id stage occupiedPair occupiedGather pairTicks
    let maps:=chooseMapCost (W:=W) A winner gatherTicks
    HistoryNodePorts.phaseCost grid.childBound+(4+9*(2*(privateHeader C W).binds+4)+
      ((List.range A.party.parties).map (fun j=>pairs j+maps j)).sum+
      (4+(HistoryMotifJoin.rows C W true).length*(2*(HistoryMotifJoin.joinHeader C W true).binds+4)+P.ticks jobs)) ≤
      blockKernelRate B*((W+1)^3*(1+r)+(resultTree L R wire).resources) := by
  exact (HistoryRefreshEmitter.emit_ticks A (kernelTemplate grid) same node winner L R wire id stage
    occupiedPair occupiedGather beforeJoin grid.childBound «rec».letters «rec».supplies «rec».codeBits «rec».header
    «rec».maxDigit r pairTicks gatherTicks (partyMapRate (kernelTemplate grid) «rec») pair gather).trans
      (Nat.mul_le_mul_right _ (block_kernel_rate B grid «rec» gmem pmem))

open Diagonal.MotifKernel
open scoped BigOperators

/-- The native shrink site, priced at the same fixed block constant as refresh. -/
theorem shrink_block_ticks {F : Type} [Field F] [Fintype F] {W n p : ℕ}
    (B : Block F) (grid : Grid F) (gmem : grid∈grids B) (A : HistoryGatherBody.Layout)
    (same : Same A (kernelTemplate grid)) (node : ℕ) (m : Memory W) (id : ((Fin 3→Bool)→F)→ℕ)
    {U I Z : Type} [Fintype U] [Fintype I] [Fintype Z] [DecidableEq Z]
    (put : U→I→Z) (v : Z) (motifs : Fin n≃Active put v) (piece : Active put v→Tree F p)
    (copies : Active put v→ℕ) (tax : ℕ→ℕ)
    (size : n≤A.party.motifs)
    (perMotif : ∀ j<A.party.motifs,
      tax j≤ motifRate (kernelTemplate grid) (gridPairRate grid) (gridMapRate grid)*((W+1)^3*
        (1+(if hj:j<n then copies (motifs ⟨j,hj⟩) else 0))+
        (if hj:j<n then (piece (motifs ⟨j,hj⟩)).resources else 1))) :
    HistoryNodePorts.phaseCost grid.childBound+((List.range A.party.motifs).map tax).sum+
        HistoryShrinkEmitter.joinTicks A false node m (fun i=>(piece (motifs i)).compile)
          (fun (_ : Fin n) (j : Fin p)=>(BitSource.pin j : BitSource 0 p)) id ≤
      blockKernelRate B*((W+1)^3*(1+∑ i : Fin n,copies (motifs i))+1+(Tree.activeTree put v motifs piece).resources) := by
  exact (HistoryShrinkEmitter.emit_site_ticks A (kernelTemplate grid) node m id put v motifs piece same size
    grid.childBound (gridPairRate grid) (gridMapRate grid) copies tax perMotif).trans
    (Nat.mul_le_mul_right _ (grid_rate_le_block B grid gmem))

end ThreeFlat.RAM.HistoryStageBody.Physical

namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Diagonal Diagonal.PhysicalStage Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree
open private term_le_sum from OAI.ThreeFlat.RAM.HistoryMotifRates
open Diagonal.HistogramTileNetwork Diagonal.MotifOrderedCells Diagonal.MotifOuterTerms
open Diagonal.MotifSelectorChecks LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F] [Fintype F]

omit [Field F] in
theorem port_word_le_grid (ar : ℕ) (g : Grid F) {p : Party F} (hp : p∈g.rows) (k : Fin g.stride) :
    p.port.at g.demand g.supply k.val≤gridPageRate ar g := by
  let count (z : Party F) := ∑ t : Fin g.stride,z.port.at g.demand g.supply t.val
  have one : p.port.at g.demand g.supply k.val≤count p :=
    Finset.single_le_sum (fun t _=>Nat.zero_le (p.port.at g.demand g.supply t.val)) (Finset.mem_univ k)
  have all : count p≤gridPortWords g:=term_le_sum g.rows count p hp
  unfold gridPageRate
  omega

omit [Field F] in
theorem party_page_le_grid (ar : ℕ) (g : Grid F) {p : Party F} (cell : p∈g.rows) :
    partyPageRate ar p≤gridPageRate ar g :=
  (term_le_sum g.rows (partyPageRate ar) p cell).trans (Nat.le_add_left _ _)


/-- The scalar tag stored in a compiled row fits in one actual native word. -/
theorem block_tags_at_age (B : Block F) {u : ℕ} (intrinsic : blockPageRate B≤u) :
    Fintype.card ((Fin 3→Bool)→F)≤2^(16*u^10) := by
  have tags:Fintype.card ((Fin 3→Bool)→F)≤blockPageRate B:=Nat.le_add_right _ _
  have growing:u≤u^10:=Nat.le_self_pow (by decide) u
  exact (tags.trans intrinsic).trans ((Nat.le_of_lt u.lt_two_pow_self).trans
    (Nat.pow_le_pow_right (by decide:0<2) (by omega)))

/-- Sizes of the real LUT, compaction, scalar and pair allocations. -/
structure PartyPageCaps (V ar : ℕ) (p : Party F) (r t rows bits : ℕ) : Prop where
  width : 2^t≤V
  work : StableCompactNativeBudget.budget t≤V
  kindSmall : ∀ i : Fin 7,(p.kind ar).words i≤V
  pairRows : 8*rows≤V
  pairPins : (r*(p.supplies*p.codeBits+p.letters)+p.letters*(r+(r+r)))+
      (r*(p.header+(p.supplies*p.maxDigit+p.supplies*p.maxDigit))+
        p.supplies*(r*p.maxDigit+(r*p.maxDigit+r*p.maxDigit)))≤V
  commands : 23*(r+max p.letters p.supplies)≤V
  pairBits : bits≤V

omit [Field F] in
/-- Every selected tile height fits the actual native library at height
`16*u^10` once its copy count is covered by a priced chronological node. -/
theorem page_height_at_age (ar u price r : ℕ) (g : Grid F) (p : Party F)
    (cell : p∈g.rows) (copies:r≤price)
    (margin : gridPageRate ar g*((price+1)*(16*u^10+1)^3)≤volume u) :
    siteHeight r p.maxDigit≤16*u^10 := by
  let U:=(price+1)*(16*u^10+1)^3
  have units:0<U:=by dsimp [U];positivity
  have entry:partyPageRate ar p≤gridPageRate ar g:=party_page_le_grid ar g cell
  have digit:800000*(p.maxDigit+1)≤gridPageRate ar g:=by
    apply _root_.le_trans _ entry
    change 800000*(p.maxDigit+1)≤_
    unfold partyPageRate
    omega
  have dfit:p.maxDigit≤volume u:=(by omega : p.maxDigit≤gridPageRate ar g).trans
    ((Nat.le_mul_of_pos_right _ units).trans margin)
  have uf:U≤volume u:=(Nat.le_mul_of_pos_left U (by omega : 0<gridPageRate ar g)).trans margin
  have rc:r≤volume u:=copies.trans ((Nat.le_succ _).trans ((Nat.le_mul_of_pos_right _ (by positivity : 0<(16*u^10+1)^3)).trans uf))
  apply Nat.clog_le_of_le_pow
  apply le_trans _ (Nat.pow_le_pow_right (by decide : 0<2) (show u^10+u^10≤16*u^10 by omega))
  rw [pow_add]
  exact max_le (rc.trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))) (Nat.mul_le_mul rc dfit)

section TypedPage
variable {J E S : Type} [Fintype J] [Nonempty J] [Fintype E] [Fintype S]
  {r n e : ℕ} (D : PortGraph J E) (G : Supply J S) (j : J) (base : E→ℕ)
  (T : FixedMotifTile D (ports G) base F) (dp : Fin n≃D.Port j) (sp : Fin e≃(ports G).Port j)
  (di : Fin n→ℕ) (si : Fin e→ℕ) (v : Histogram T.Alphabet r)
local instance : Nonempty T.Alphabet := T.hasLetter
local notation "H" => (⟨dp,T.encode⟩ : Header (D.Port j) T.Alphabet (fun a=>base a.1.1) T.bits n)
local notation "P" => Party.ofTile D G j base T dp sp di si
local notation "m" => siteHeight r T.bitCap
local notation "sl" => (r+1)*(m+1)^3
local notation "C" => MotifNativeCompactors.partialInput F r m
local notation "E₀" => MotifNativeCompactors.partialInput F (r*T.bitCap) m
local notation "s" => Fintype.card T.Alphabet
local notation "idT" => Fintype.equivFin T.Alphabet
local notation "tile" => HistogramTileNetwork.tile D G j base H sp T.output (fun a q=>T.output_le_cap a _) T.entry
local notation "L" => admission (headerGood G j sp T.encode) (headerLetter G j sp idT T.encode) C (numberHistogram idT v)
local notation "R" => tiled tile E₀

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1300000 in
/-- Word bounds follow from the actual archived row and its one scalar page
margin, for shrink and refresh with their own selected demand/supply order. -/
theorem party_page_caps (ar V : ℕ) (g : Grid F) (cell : P∈g.rows)
    (margin : gridPageRate ar g*sl≤V) :
    PartyPageCaps V ar P r m ((L).rows+(R).rows) ((L).bits+(R).bits) := by
  classical
  let scale:ℕ:=sl
  let d:=T.bitCap
  have frame:partyPageRate ar P*scale≤V:=
    (Nat.mul_le_mul_right scale (party_page_le_grid ar g cell)).trans margin
  have unit : 1 ≤ scale := by
    change 0 < (r + 1) * (m + 1)^3
    positivity
  have fit (c:ℕ) (le:c≤partyPageRate ar P):c*scale≤V:=(Nat.mul_le_mul_right scale le).trans frame
  have metadata:((∑ i : Fin 7,((P).kind ar).words i))*scale≤V:=fit _ (by unfold partyPageRate;omega)
  have gates:(8*partyCoefficient (H).arity T.bits s e d)*scale≤V:=fit _ (by
    change 8*partyCoefficient (P).header (P).codeBits (P).letters (P).supplies (P).maxDigit≤_
    unfold partyPageRate;omega)
  have pins:partyPinCoefficient (H).arity T.bits s e d*scale≤V:=fit _ (by
    change partyPinCoefficient (P).header (P).codeBits (P).letters (P).supplies (P).maxDigit≤_
    unfold partyPageRate;omega)
  have cmds:(23*(5+s+e))*scale≤V:=fit _ (by
    change 23*(5+(P).letters+(P).supplies)≤_;unfold partyPageRate;omega)
  have compact:(800000*(d+1))*scale≤V:=fit _ (by
    change 800000*((P).maxDigit+1)≤_;unfold partyPageRate;omega)
  have priced:=party_resources D G j base H sp T.output (fun a q=>T.output_le_cap a _) T.entry idT v
  have sizes:(L).rows+(R).rows+((L).bits+(R).bits)≤partyCoefficient (H).arity T.bits s e d*scale:=by
    simpa only [party,pair_rows,pair_bits] using priced.1
  have pinWords:(L).footprint.pins+(R).footprint.pins≤partyPinCoefficient (H).arity T.bits s e d*scale:=by
    have step:=priced.2.1
    rw [party,pair_pins] at step
    exact (Nat.le_add_right _ _).trans step
  have cnt:3+2*r+s+e≤(5+s+e)*scale:=by
    simpa only [party_nodes] using priced.2.2
  have bounds:8*((L).rows+(R).rows+((L).bits+(R).bits))≤V:=by
    rw [Nat.mul_assoc] at gates
    exact (Nat.mul_le_mul_left 8 sizes).trans gates
  have work:StableCompactNativeBudget.budget m≤V:=by
    calc
      _ ≤ ((r+1)*(2*(d+1)))*(400000*(m+1)^3) := Nat.mul_le_mul_right _ (siteHeight_capacity r d)
      _ = (800000*(d+1))*scale := by dsimp [scale];ring
      _ ≤ _ := compact
  refine ⟨((StableCompactNativeBudget.capacities F m).2.1).trans work,work,?_,by omega,?_,?_,by omega⟩
  · intro i
    have h : ((P).kind ar).words i ≤ ∑ j : Fin 7,((P).kind ar).words j :=
      Finset.single_le_sum (f := fun j : Fin 7 => ((P).kind ar).words j)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact h.trans ((Nat.le_mul_of_pos_right _ unit).trans metadata)
  · rw [admission_pins,tiled_pins] at pinWords
    exact pinWords.trans pins
  · rw [Nat.mul_assoc] at cmds
    apply (Nat.mul_le_mul_left 23 _).trans cmds
    exact (show r+max s e≤3+2*r+s+e by omega).trans cnt


set_option maxRecDepth 12000 in
/-- A fixed family rate times the selected chronological charge and the cubic
word-width tariff suffices for every byte range. In particular the compactor
height is derived from the copy count and the actual static digit width. -/
theorem party_page_caps_at_age (ar u price : ℕ) (g : Grid F) (cell : P∈g.rows) (copies : r≤price)
    (margin : gridPageRate ar g*((price+1)*(16*u^10+1)^3)≤volume u) :
    PartyPageCaps (volume u) ar P r m ((L).rows+(R).rows) ((L).bits+(R).bits) := by
  have height:m≤16*u^10:=page_height_at_age ar u price r g P cell copies margin
  apply party_page_caps D G j base T dp sp di si v ar (volume u) g cell
  exact (Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.succ_le_succ copies)
    (Nat.pow_le_pow_left (Nat.succ_le_succ height) 3))).trans margin

end TypedPage
end
end ThreeFlat.RAM.HistoryStageBody.Physical


namespace ThreeFlat.RAM.HistoryStageBody.Physical

open Computability.VPVNP.BurstRAM PrivateRAM HistoryGatherBody HistoryGatherExecution
open Diagonal Diagonal.MotifOuterTerms Diagonal.HistogramTileNetwork Diagonal.MotifBinaryPacking
open LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector BitLayout
open scoped Classical BigOperators Fin.NatCast
noncomputable section

variable {F J E S : Type} [Field F] [Fintype F] [Fintype J] [Nonempty J] [Fintype E] [Fintype S]
  {e n r h p W : ℕ}
  (A : HistoryGatherBody.Layout) (input : Memory W) (gathered : ℕ→Word W)
  (D : PortGraph J E) (G : Supply J S) (j : J) (base live : E→ℕ)
  (tile : FixedMotifTile D (ports G) base F)
  (dp : Fin n ≃ D.Port j) (sp : Fin e ≃ (ports G).Port j) (di : Fin n→ℕ) (si : Fin e→ℕ)
  (v : Histogram tile.Alphabet r) (old : (a : D.Port j)→Fin (live a.1.1)→BitSource h p)
  (fresh : (a : (ports G).Port j)→Fin (histWidth tile.output v a.1.1+r*tile.bits)→BitSource h p)

local instance : Nonempty tile.Alphabet := tile.hasLetter
local notation "H" => (⟨dp,tile.encode⟩ : HistogramTileNetwork.Header (D.Port j) tile.Alphabet
  (fun a=>base a.1.1) tile.bits n)
local notation "row" => Party.ofTile D G j base tile dp sp di si
local notation "plan" => nativePlan A input
  (typedSources (W:=W) A D G j base live H sp tile.output v old fresh) gathered

/-- The cost of an actual active map uses the rate of the selected finite ROM row. -/
theorem tile_partyMapRate (ref : HistoryGatherBody.Layout) (mode : A.mode=ref.mode)
    (dem : A.demandCap=ref.demandCap) (sup : A.supplyCap=ref.supplyCap)
    (a page : ℕ) (initial : ReadPage A input row a page) (nst : n≤A.demandCap) (est : e≤A.supplyCap)
    (demWidth : ∀u:Fin n,(physicalWidth A input false u.val).val=live (dp u).1.1)
    (supWidth : ∀u:Fin e,(physicalWidth A input true u.val).val=histWidth tile.output v (sp u).1.1+r*tile.bits)
    (copyFit : ∀u:Fin n,live (dp u).1.1≤base (dp u).1.1*r)
    (mapLength : (partyMapCount A input).val=r*(e*tile.bits)+(r*(H).arity+e*(r*tile.bitCap))) :
    tariff W A plan≤partyMapRate ref row*(1+r) := by
  apply partyMapRate_bound
  exact tile_tariff_le A input gathered D G j base live tile dp sp di si v old fresh
    ref mode dem sup a page initial nst est demWidth supWidth copyFit mapLength

end
end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI
