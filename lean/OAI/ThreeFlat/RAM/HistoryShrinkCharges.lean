import OAI.ThreeFlat.RAM.HistoryShrinkPrefixes

namespace OAI
set_option quotPrecheck false
set_option maxErrors 600

namespace ThreeFlat.RAM.HistoryShrinkEmitter
open Computability.VPVNP.BurstRAM PrivateRAM HistoryMotifJoin HistoryPartyBatchExec HistoryGatherBody
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {W n : ℕ} {A : HistoryGatherBody.Layout} {m after : Memory W}
variable {geo : Diagonal.CompressorPacking.Native.Graph.Stage}

/-- At the end of the party loop the ninth prefix word is the number of hidden
pins of the ordered absorbed edges of this particular shrink piece. -/
theorem occupied_private_total {owns : Fin 8→Prop} {issued : Fin 8→ℕ}
    (native : PrivateSite (geo:=geo) A m owns issued)
    (edges : Fin n ≃ {e // owns e}) (room : A.privateStarts+9<2^W)
    (held : after (A.privateStarts+8)=
      headerImage (privateHeader A W) A.privateStarts 9 m (A.privateStarts+8)) :
    after (((A.privateStarts+8:ℕ):Word W).val)=(∑ i,issued (edges i).val:ℕ) := by
  have lastWord : headerImage (privateHeader A W) A.privateStarts 9 m (A.privateStarts+8)=
      ((∑ e∈Finset.univ.filter (fun e:Fin 8=>owns e ∧ e.val<8),issued e:ℕ):Word W) :=
    HistoryMotifJoin.PrivateSite.prefix A native (8:Fin 9) room
  rw [Fin.val_cast_of_lt (show A.privateStarts+8<2^W by omega),held,lastWord]
  apply congrArg (fun x : ℕ => (x : Word W))
  calc
    _ = ∑ e : {e : Fin 8 // owns e},issued e.val := by
      symm
      apply Finset.sum_bij (fun (e : {j : Fin 8 // owns j}) _ => e.val)
      · intro e _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.property,e.val.isLt⟩
      · intro e _ f _ eq;exact Subtype.ext eq
      · intro e he
        exact ⟨⟨e,(Finset.mem_filter.mp he).2.1⟩,Finset.mem_univ _,rfl⟩
      · intro e _;rfl
    _ = ∑ i,issued (edges i).val := (edges.sum_comp (fun e=>issued e.val)).symm

/-- A padding slot uses no shared bit, even if the stale incident pointer still
points at an occupied descriptor. The motif-count test disables every width. -/
theorem padding_private_total
    (inactive : ¬(A.party.motif:Word W)<wordAt m (selected A m).kernel 3)
    (room : A.privateStarts+9<2^W)
    (held : after (A.privateStarts+8)=
      headerImage (privateHeader A W) A.privateStarts 9 m (A.privateStarts+8)) :
    after (((A.privateStarts+8:ℕ):Word W).val)=0 := by
  have lastWord : headerImage (privateHeader A W) A.privateStarts 9 m (A.privateStarts+8) =
      ∑ i ∈ Finset.range 8, privateWidth A m i := by
    simpa only [show (8 : Fin 9).val = 8 by rfl] using
      HistoryMotifJoin.private_prefix A m (8 : Fin 9) room
  rw [Fin.val_cast_of_lt (by omega), held, lastWord]
  apply Finset.sum_eq_zero
  intro j _
  cases h : A.mode <;> simp [privateWidth,inactive,h]

theorem padding_party_count
    (inactive : ¬(A.party.motif:Word W)<wordAt m (selected A m).kernel 3) :
    Fintype.card {j : Fin A.party.parties // selectedBit A m j.val}=0 := by
  let : IsEmpty {j : Fin A.party.parties // selectedBit A m j.val} :=
    ⟨fun j=>inactive j.property.1⟩
  exact Fintype.card_eq_zero

end
end ThreeFlat.RAM.HistoryShrinkEmitter

namespace ThreeFlat.RAM.HistoryShrinkEmitter
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr HistoryMotifJoin HistoryPartyBatchExec HistoryGatherBody
open HistoryStageRoot Diagonal.PhysicalStage
open scoped Classical BigOperators Fin.CommRing
open private rd l from OAI.ThreeFlat.RAM.HistoryNodePorts
noncomputable section
variable {W : ℕ} {A : HistoryGatherBody.Layout} {m : Memory W}

/-- The typed old half-width prefix and the successor's archived final half row
are the two operands of the actual motif port header. -/
theorem selected_port_total {d lanes : ℕ} {X : State d lanes} (sites : X.ArchiveSites) (z : X.Site)
    (Q : HistoryStageRoot.Input) (halves : State.HalfRows sites (fun a=>a<2^W) (numeric m))
    (node : HistoryMotifJoin.nodeAddress A.nodePorts m=(HistoryStageRoot.node Q:Word W))
    (nodeFit : HistoryStageRoot.node Q+6<2^W)
    (pointer : numeric m (HistoryStageRoot.node Q+6)=sites.layer.incident+(sites.ord z).val*2)
    (old : ℕ) (prefixRoom : A.nodePorts.starts+childCount Q (numeric m)<2^W)
    (prefixRead : m (A.nodePorts.starts+childCount Q (numeric m))=(old:Word W))
    (degree : 0<d) :
    (selected A m).oldBits+(selected A m).newBits=((old+X.incidentWidth z:ℕ):Word W) := by
  let head:=sites.layer.incident+(sites.ord z).val*2
  let last : Fin (2*d):=⟨2*d-1,by omega⟩
  let tail:=numeric m (head+1)+4*last.val
  have hr : head<2^W := halves.headerSafe z 0
  have cnt : (m head).val=2*d:=halves.count z
  have fr : 1<2^W:=by have := (m head).isLt;omega
  have one : (1:Word W).val=1:=Fin.val_cast_of_lt fr
  have ge : (1:Word W)≤ m head:=by change (1:Word W).val≤(m head).val;rw [one,cnt];omega
  have cutOK : cutWord (m head) 1=(last.val:Word W):=by
    apply Fin.ext
    rw [cutWord,ite_eq_right (not_lt.mpr ge),Fin.sub_val_of_le ge,cnt,one,Fin.val_cast_of_lt
      (last.isLt.trans_le (by rw [←cnt];exact (m head).isLt.le))]
  have field (j : Fin 7) : wordAt m (HistoryMotifJoin.nodeAddress A.nodePorts m) j.val=
      m (HistoryStageRoot.node Q+j.val) := by
    rw [node,wordAt,←Nat.cast_add,Fin.val_cast_of_lt (by have:=j.isLt;omega)]
  have hp : wordAt m (HistoryMotifJoin.nodeAddress A.nodePorts m) 6=(head:Word W) :=
    (field 6).trans (Fin.ext (pointer.trans (Fin.val_cast_of_lt hr).symm))
  have hn : m head≠0:=by intro bad;rw [bad] at cnt;simp at cnt;omega
  have tailWord : lastHalfAddress A.nodePorts m=(tail:Word W) := by
    rw [lastHalfAddress,hp,Fin.val_cast_of_lt hr,cutOK,wordAt,←Nat.cast_add,
      Fin.val_cast_of_lt (show head+1<2^W from halves.headerSafe z 1)]
    simp [tail,numeric,Nat.cast_add,Nat.cast_mul]
  have readTail (k : Fin 4) : wordAt m (lastHalfAddress A.nodePorts m) k.val=m (tail+k.val) := by
    rw [tailWord,wordAt,←Nat.cast_add,Fin.val_cast_of_lt (show tail+k.val<2^W from halves.entriesSafe z last k)]
  have fresh : (selected A m).newBits =
      if m (wordAt m (HistoryMotifJoin.nodeAddress A.nodePorts m) 6).val=0 then 0
      else wordAt m (lastHalfAddress A.nodePorts m) 3+wordAt m (lastHalfAddress A.nodePorts m) 2 := by
    change (HistoryNodePorts.fresh A.nodePorts).value _ _ _=_
    have eqTest (x y : Word W) : DescriptorExpr.Comparison.test .eq x y = true ↔ x = y :=
      beq_iff_eq
    have ltTest (x y : Word W) : DescriptorExpr.Comparison.test .lt x y = true ↔ x < y :=
      decide_eq_true_iff
    simp only [HistoryNodePorts.fresh,HistoryNodePorts.halves,rd,l,eqz,add,mul,Formula.value,
      eqTest,ltTest,BinaryOp.eval,HistoryMotifJoin.nodeAddress,lastHalfAddress,wordAt,cutWord,
      Fin.ofNat_eq_cast,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
    first
    | rfl
  have fw:=HistoryStageSetup.stage_half sites halves Q z pointer
  change (if numeric m (numeric m (HistoryStageRoot.node Q+6))=0 then 0 else
    numeric m (numeric m (numeric m (HistoryStageRoot.node Q+6)+1)+
    4*(numeric m (numeric m (HistoryStageRoot.node Q+6))-1)+3) +
    numeric m (numeric m (numeric m (HistoryStageRoot.node Q+6)+1)+
    4*(numeric m (numeric m (HistoryStageRoot.node Q+6))-1)+2))=_ at fw
  rw [pointer,show numeric m head=2*d from cnt,ite_eq_right (by omega)] at fw
  have oldRead : (selected A m).oldBits=(old:Word W):=by
    change m ((A.nodePorts.starts:Word W)+wordAt m (HistoryMotifJoin.nodeAddress A.nodePorts m) 4).val=_
    have countWord : wordAt m (HistoryMotifJoin.nodeAddress A.nodePorts m) 4 =
        ((childCount Q (numeric m):ℕ):Word W) :=
      (field 4).trans (Fin.cast_val_eq_self (m (HistoryStageRoot.node Q+4))).symm
    rw [countWord]
    rw [←Nat.cast_add,Fin.val_cast_of_lt prefixRoom,prefixRead]
  have startRead : wordAt m (lastHalfAddress A.nodePorts m) 3=m (tail+3) := readTail 3
  have widthRead : wordAt m (lastHalfAddress A.nodePorts m) 2=m (tail+2) := readTail 2
  have sumTail : (m (tail+3)).val+(m (tail+2)).val=X.incidentWidth z := fw
  rw [oldRead,fresh,hp,Fin.val_cast_of_lt hr,ite_eq_right hn,startRead,widthRead,←sumTail]
  simp only [Nat.cast_add,Fin.cast_val_eq_self]

end
end ThreeFlat.RAM.HistoryShrinkEmitter

namespace ThreeFlat.RAM.HistoryShrinkEmitter
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TickWorkspace Diagonal.HistoryContraction
open HistoryGatherBody HistoryMotifJoin HistoryPartyBatchExec
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {u node p : ℕ} {F : Type} [Field F] [Fintype F] {A : HistoryGatherBody.Layout}
local notation "W" => 16*u^10
local notation "V" => HistoryStageBody.Physical.volume u

omit [Field F] [Fintype F] in
theorem Children.charge_eq {tree : Tree F p} (C : Children tree) :
    tree.resources=C.shared+1+∑i,((C.factor i).resources+C.arity i) := by
  calc
    tree.resources=(Tree.join C.shared C.count C.arity C.wire C.factor).resources:=
      congrArg (fun T : Tree F p=>T.resources) C.eqn
    _ = _ := by
      simp only [Tree.resources,Stage.treeWork,Tree.rows,Tree.bits,Tree.nodes,Tree.footprint,Finset.sum_add_distrib]
      omega

omit [Field F] [Fintype F] in
theorem Children.factor_resources_le {tree : Tree F p} (C : Children tree) (i : Fin C.count) :
    (C.factor i).resources≤tree.resources := by
  have atIndex := Finset.single_le_sum
    (f:=fun j : Fin C.count=>(C.factor j).resources+C.arity j) (fun j _=>Nat.zero_le _) (Finset.mem_univ i)
  rw [C.charge_eq]
  omega

omit [Field F] [Fintype F] in
private theorem Children.chart_cost {tree : Tree F p} (C : Children tree)
    (age : 16≤u) (cost : 4*tree.resources≤V) (id : ((Fin 3→Bool)→F)→ℕ) (tags : ∀ t,id t<2^W) :
    (∀ i,C.arity i≤V) ∧ 4*(∑ i,(C.factor i).compile.cells)≤V ∧
    C.shared<2^W ∧ (∀ i,(C.factor i).compile.internal<2^W) ∧
    (∀ i r j,HistoryCompiledRows.metadata id (C.factor i).compile r j<2^W) := by
  let charge := fun i : Fin C.count=>(C.factor i).resources+C.arity i
  have chargeEq : tree.resources=C.shared+1+∑ i,charge i := C.charge_eq
  have single (i : Fin C.count) : charge i≤∑ i,charge i :=
    Finset.single_le_sum (fun j _=>Nat.zero_le (charge j)) (Finset.mem_univ i)
  have rows : (∑ i,(C.factor i).rows)≤∑ i,charge i := by
    apply Finset.sum_le_sum
    intro i _
    change (C.factor i).rows≤(C.factor i).resources+C.arity i
    unfold Tree.resources Stage.treeWork
    omega
  have ar (i : Fin C.count) : C.arity i≤V:=by
    have arityLe : C.arity i ≤ charge i := Nat.le_add_left ..
    have bounded := arityLe.trans (single i)
    omega
  have hidden (i : Fin C.count) : (C.factor i).compile.internal≤V:=by
    rw [Tree.compiled_bits]
    have bits : (C.factor i).bits≤charge i := by
      change (C.factor i).bits≤(C.factor i).resources+C.arity i
      unfold Tree.resources Stage.treeWork
      omega
    have bounded := bits.trans (single i)
    omega
  have expo : 1≤u^10:=Nat.one_le_pow _ _ (by omega)
  have wide : 2+2*V≤2^W:=calc
    _ ≤ 4*V:=by have h : 0<V:=Nat.two_pow_pos _;omega
    _ = 2^(2+u^10):=by rw [pow_add];rfl
    _ ≤ 2^W:=Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨ar,?_,by omega,fun i=>by have:=hidden i;omega,
    fun i=>HistoryCompiledRows.metadata_fits id _ (by have:=ar i;have:=hidden i;omega) tags⟩
  simp only [Tree.compiled_rows]
  omega

omit [Field F] [Fintype F] in
/-- The one cost bound for the selected geometric piece controls its child
arities, emitted records, private indices and every source code in those records. -/
theorem Children.finish_chart {tree : Tree F p} (C : Children tree)
    (arms : ArmRows A W C.count) (m : Memory W) (id : ((Fin 3→Bool)→F)→ℕ)
    (banks : PhysicalBanks u A) (age : 16≤u) (smallNode : node<V^2)
    (static : (A.party.motifs+2)*(A.party.parties+2)*8*32≤V)
    (motif : A.party.motif<A.party.motifs) (six : A.party.parties=6)
    (cost : 4*tree.resources≤V) (pins : p<2^W) (tags : ∀ t,id t<2^W)
    (safe : Protected (joinHeader A W true) m (A.party.seed+64) (HistoryMotifJoin.rows A W true).length)
    (cursor : (HistoryNodePorts.id A.nodePorts).value (fun _=>0) m (fun _=>0)=(node:Word W))
    (ports : (selected A m).oldBits+(selected A m).newBits=(p:Word W))
    (shared : m (((A.privateStarts+8:ℕ):Word W).val)=(C.shared:Word W))
    (active : Fintype.card {j : Fin A.party.parties //selectedBit A m j.val}=C.count)
    (roles : ∀ i : Fin C.count,role A m i.val=(arms.index i).val) :
    (∀ i : Fin C.count,role A m i.val=((C.slot arms).arms.index i).val) ∧
      Chart A true node m (C.slot arms).children (C.slot arms).wire id := by
  obtain ⟨ar,gates,share,hidden,metadata⟩:=C.chart_cost age cost id tags
  have expo : 1≤u^10:=Nat.one_le_pow _ _ (by omega)
  have cap : C.count≤A.party.parties:=by
    rw [←active]
    simpa using Fintype.card_subtype_le (fun i:Fin A.party.parties=>selectedBit A m i.val)
  have mask : 2^A.party.parties<2^W:=by
    rw [six]
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  exact ⟨roles,Chart.of_layout banks age true m (fun i=>(C.factor i).compile) C.wire id
    smallNode static (fun _=>motif) cap ar gates ⟨pins,share,hidden⟩ metadata
    safe cursor ports (fun _=>shared) (fun _=>active.symm) (by intro h;cases h) mask⟩

omit [Field F] [Fintype F] in
/-- The outer shrinkSite uses the archived incidence count, identity pin rows,
and the actual activeTree charge on the complete selected roster. -/
theorem activeTree_chart {M J Z : Type} [Fintype M] [Fintype J] [Fintype Z] [DecidableEq Z]
    {s : ℕ} (site : M→J→Z) (v : Z) (order : Fin s≃Diagonal.MotifKernel.Active site v)
    (child : Diagonal.MotifKernel.Active site v→Tree F p) (m : Memory W) (id : ((Fin 3→Bool)→F)→ℕ)
    (banks : PhysicalBanks u A) (age : 16≤u) (smallNode : node<V^2)
    (static : (A.party.motifs+2)*(A.party.parties+2)*8*32≤V)
    (six : A.party.parties=6) (cap : s≤A.party.motifs)
    (cost : 4*(Tree.activeTree site v order child).resources≤V)
    (pins : p<2^W) (tags : ∀ t,id t<2^W)
    (safe : Protected (joinHeader A W false) m (A.party.seed+64) (HistoryMotifJoin.rows A W false).length)
    (cursor : (HistoryNodePorts.id A.nodePorts).value (fun _=>0) m (fun _=>0)=(node:Word W))
    (ports : (selected A m).oldBits+(selected A m).newBits=(p:Word W))
    (size : wordAt m (selected A m).kernel 3=(s:Word W)) :
    Chart A false node m (fun i=>(child (order i)).compile)
      (fun (_ : Fin s) (j : Fin p)=>(BitSource.pin j : BitSource 0 p)) id := by
  let C : Children (Tree.activeTree site v order child):=
    Children.join 0 s (fun _=>p) (fun _ j=>.pin j) (fun i=>child (order i))
  obtain ⟨ar,gates,share,hidden,metadata⟩:=C.chart_cost age cost id tags
  have expo : 1≤u^10:=Nat.one_le_pow _ _ (by omega)
  exact Chart.of_layout banks age false m (fun i=>(child (order i)).compile)
    (fun _ j=>(BitSource.pin j : BitSource 0 p)) id smallNode static (by intro h;cases h) cap
    ar gates ⟨pins,share,hidden⟩ metadata safe cursor ports (by intro h;cases h) (by intro h;cases h)
    (fun _=>size) (by rw [six];exact Nat.pow_lt_pow_right (by decide) (by omega))

omit [Field F] [Fintype F] in
/-- A padded incidence still emits its physical empty join. Both raw tests for
occupancy are evaluated in the memories on the corresponding sides of the arm scan. -/
theorem emptySlot_chart (input m : Memory W) (id : ((Fin 3→Bool)→F)→ℕ)
    (banks : PhysicalBanks u A) (age : 16≤u) (smallNode : node<V^2)
    (static : (A.party.motifs+2)*(A.party.parties+2)*8*32≤V)
    (motif : A.party.motif<A.party.motifs) (six : A.party.parties=6)
    (pins : p<2^W)
    (safe : Protected (joinHeader A W true) m (A.party.seed+64) (HistoryMotifJoin.rows A W true).length)
    (cursor : (HistoryNodePorts.id A.nodePorts).value (fun _=>0) m (fun _=>0)=(node:Word W))
    (ports : (selected A m).oldBits+(selected A m).newBits=(p:Word W))
    (inactive : ¬(A.party.motif:Word W)<wordAt input (selected A input).kernel 3)
    (still : ¬(A.party.motif:Word W)<wordAt m (selected A m).kernel 3)
    (room : A.privateStarts+9<2^W)
    (held : m (A.privateStarts+8)=headerImage (privateHeader A W) A.privateStarts 9 input (A.privateStarts+8)) :
    let Z : SiteSlot F W p A := emptySlot A
    (∀ i,role A m i.val=(Z.arms.index i).val) ∧ Chart A true node m Z.children Z.wire id := by
  dsimp only
  have wide : 1≤u^10:=Nat.one_le_pow _ _ (by omega)
  refine ⟨fun i=>Fin.elim0 i,Chart.of_layout banks age true m _ _ id smallNode static (fun _=>motif)
    (Nat.zero_le _) (fun i=>Fin.elim0 i) ?_ ⟨pins,Nat.two_pow_pos _,fun i=>Fin.elim0 i⟩
    (fun i=>Fin.elim0 i) safe cursor ports (fun _=>padding_private_total inactive room held)
    (fun _=>(padding_party_count still).symm) (by intro h;cases h) ?_⟩
  · change 4 * (∑ i : Fin 0, ((emptySlot A : SiteSlot F W p A).children i).cells) ≤ V
    simp only [Fin.sum_univ_zero, Nat.mul_zero, Nat.zero_le]
  · rw [six];exact Nat.pow_lt_pow_right (by decide) (by omega)

end
end ThreeFlat.RAM.HistoryShrinkEmitter

namespace ThreeFlat.RAM.HistoryShrinkEmitter
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr BitLayout HistoryMotifJoin
open HistoryStageBody.Physical Diagonal.HistoryContraction HistoryRefreshEmitter
open scoped Classical
noncomputable section

variable {F : Type} [Field F] [Fintype F] {u node W h p : ℕ}
variable (id : ((Fin 3→Bool)→F)→ℕ) (A : HistoryGatherBody.Layout) (active : Fin A.party.parties→Prop)
variable (arity : Fin (Fintype.card {j : Fin A.party.parties // active j})→ℕ) (N : ∀ i,BitNetwork F (arity i)) (wire : ∀ i,Fin (arity i)→BitSource h p)
variable (allowance : Fin (Fintype.card {j : Fin A.party.parties // active j})→ℕ)

private def paid (i : Fin (Fintype.card {j : Fin A.party.parties // active j})) (m : Memory W) (w : ArmWrite W) : Prop :=
  ArmWrite.Real u node id (withParty A (Diagonal.HistoryMaskOrder.order active i).val.val) (N i) (wire i) m w ∧
    w.ticks+HistoryGatherExecution.tariff W (withParty A (Diagonal.HistoryMaskOrder.order active i).val.val) w.plan≤allowance i


/-- Choose the actual achieved pair and gather bounds for a reachable arm.
Only a proof outside the program uses choice. The native procedure has the
fixed party roster and reads its mask directly. -/
def pickedWrite (i : Fin (Fintype.card {j : Fin A.party.parties // active j})) (m : Memory W) : ArmWrite W :=
  if cert : ∃ out,paid (u := u) (node := node) id A active arity N wire allowance i m out then Classical.choose cert
  else ⟨m,⟨fun _=>0,fun _ _=>0,fun _ _ _=>0,0,0,fun _=>0⟩,0⟩

local notation "pick" => pickedWrite (u := u) (node := node) id A active arity N wire allowance

omit [Field F] [Fintype F] in
private theorem pickedWrite_spec (i : Fin (Fintype.card {j : Fin A.party.parties // active j})) (m : Memory W)
    (ex : ∃ z,paid (u := u) (node := node) id A active arity N wire allowance i m z) : paid (u := u) (node := node) id A active arity N wire allowance i m (pick i m) := by
  unfold pickedWrite
  rw [dite_eq_left ex]
  exact Classical.choose_spec ex

local notation "init" m:arg => headerImage (privateHeader A W) A.privateStarts 9 m

def issuedSlot (m : Memory W) : SiteSlot F W p A :=
  ⟨h,Fintype.card {j : Fin A.party.parties // active j},arity,N,wire,evaluatedArms node id A active pick (init m)⟩

local notation "Z" m:arg => issuedSlot (u:=u) (node:=node) id A active arity N wire allowance m
local notation "atArm" m:arg j:arg =>
  ArmRows.entry node id (SiteSlot.arms (Z m)) (SiteSlot.init (Z m) m) j

omit [Field F] [Fintype F] in
/-- A captured row has exactly the output produced at the earlier chronological
prefix. The concrete field and budget proof feeds both the chosen instruction
stream and its price, even with multiple occupied parties at this site. -/
theorem issuedSlot_live (m : Memory W) (banks : PhysicalBanks u A) (nodeRoom : node<A.party.V^2)
    (capacity : (A.party.motifs+2)*(A.party.parties+2)*8*32≤A.party.V)
    (motif : A.party.motif<A.party.motifs) (hdr : 3+5*A.demandCap+4*A.supplyCap≤A.party.V)
    (room : A.privateStarts+9<2^W) (safe : HistoryPartyBatchExec.Protected (privateHeader A W) m A.privateStarts 9)
    (activeAt : ∀ i,(Z m).prefixWords (u:=u) node id m (Diagonal.HistoryMaskOrder.order active i).val.val →
      ∃ w,ArmWrite.Real u node id (withParty A (Diagonal.HistoryMaskOrder.order active i).val.val) (N i) (wire i)
          (atArm m (Diagonal.HistoryMaskOrder.order active i).val.val) w ∧
        w.ticks+HistoryGatherExecution.tariff W (withParty A (Diagonal.HistoryMaskOrder.order active i).val.val) w.plan≤allowance i)
    (absent : ∀j:Fin A.party.parties,¬active j →
      (Z m).prefixWords (u:=u) node id m j.val → VacantRoom (withParty A j.val) node id (atArm m j.val))
    (final : (Z m).prefixWords (u:=u) node id m A.party.parties →
      (∀ i,role A (atArm m A.party.parties) i.val=(Diagonal.HistoryMaskOrder.order active i).val.val) ∧
      Chart A true node (atArm m A.party.parties) N wire id) :
    (Z m).Live node id m ∧ (Z m).ArmSpace node id m u ∧
      ∀ i,(Z m).arms.pairCost i+HistoryGatherExecution.tariff W (withParty A (Diagonal.HistoryMaskOrder.order active i).val.val)
        ((Z m).arms.plan i)≤allowance i := by
  have picked (i : Fin (Fintype.card {j : Fin A.party.parties // active j})) (word : (Z m).prefixWords (u:=u) node id m (Diagonal.HistoryMaskOrder.order active i).val.val) :
      paid (u := u) (node := node) id A active arity N wire allowance i (atArm m (Diagonal.HistoryMaskOrder.order active i).val.val)
        (pick i (maskedBefore node id A active pick (init m) (Diagonal.HistoryMaskOrder.order active i).val.val)) := by
    have ex:=activeAt i word
    have e:=evaluatedArms_entry node id A active pick (init m) (Diagonal.HistoryMaskOrder.order active i).val.val
    change atArm m (Diagonal.HistoryMaskOrder.order active i).val.val=maskedBefore node id A active pick (init m) (Diagonal.HistoryMaskOrder.order active i).val.val at e
    rw [←e]
    exact pickedWrite_spec id A active arity N wire allowance i _ ex
  have row (j : Fin A.party.parties) (known : (Z m).prefixWords (u:=u) node id m j.val) :
      (Z m).IssuedArm (u:=u) node id m j := by
    have live (i : Fin (Fintype.card {j : Fin A.party.parties // active j})) (ok : (Z m).arms.select j.val=some i) :
        ArmWrite.Real u node id (withParty A j.val) (N i) (wire i) (atArm m j.val)
          (pick i (maskedBefore node id A active pick (init m) (Diagonal.HistoryMaskOrder.order active i).val.val)) := by
      have key:=maskSelect_some A active ok
      rw [←key] at known ⊢
      exact (picked i known).1
    refine ⟨⟨hdr,fun i ok=>(live i ok).width,fun i ok=>(live i ok).mapBase,
      fun i ok=>(live i ok).mapWords,fun i ok=>(live i ok).pairFrame⟩,?_,fun i ok=>(live i ok).elected⟩
    intro unselected
    apply absent j _ known
    intro on
    change maskSelect A active j.val = Option.none at unselected
    simp [maskSelect,j.isLt,on] at unselected
  have facts:=(Z m).issued_live node id m banks nodeRoom capacity motif hdr room safe row final
  refine ⟨facts.1,facts.2,?_⟩
  intro i
  have hold := (Z m).issued_prefix_words node id m banks nodeRoom capacity motif row
  exact (picked i (hold _ (Diagonal.HistoryMaskOrder.order active i).val.isLt.le)).2

end
end ThreeFlat.RAM.HistoryShrinkEmitter

end OAI
