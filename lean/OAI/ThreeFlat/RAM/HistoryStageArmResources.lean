import OAI.ThreeFlat.RAM.HistoryStageJoinResources
import OAI.ThreeFlat.RAM.HistoryStageBody

namespace OAI
/-! # Static resources of the node, gather, motif, kernel and root procedures -/
namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Computability.VPVNP.BurstRAM PhysicalProcedure PhysicalPinsExpr DescriptorExpr
open scoped Classical BigOperators Fin.CommRing
noncomputable section

def nodeResources (cap : ℕ) :=
  let A : HistoryNodePorts.Layout := ⟨0,0,0,0⟩
  resources (HistoryNodePorts.phase 1 A cap)

theorem node_resources {W : ℕ} (A : HistoryNodePorts.Layout) (cap : ℕ) :
    resources (HistoryNodePorts.phase W A cap)=nodeResources cap := by
  simp only [nodeResources,HistoryNodePorts.phase,resources_write,HeaderScan.binds_closed]
  apply congrArg (fun n : ℕ => 11+4*n+0)
  apply HistoryNodePorts.prefix_work
  rfl



private theorem fold_resources {W : ℕ} (xs : List ℕ) (step : Procedure W→ℕ→Procedure W)
    (B : ℕ) (per : ∀ p j,resources (step p j)≤resources p+B) (p : Procedure W) :
    resources (xs.foldl step p)≤resources p+xs.length*B := by
  induction xs generalizing p with
  | nil => simp
  | cons j xs ih =>
    have h := ih (step p j)
    have hp := per p j
    simpa only [List.foldl_cons,List.length_cons,Nat.add_mul,Nat.one_mul] using
      h.trans (by omega : resources (step p j)+xs.length*B≤resources p+(xs.length*B+B))


structure Same (A B : HistoryGatherBody.Layout) : Prop where
  mode : A.mode=B.mode
  demand : A.demandCap=B.demandCap
  supply : A.supplyCap=B.supplyCap
  parties : A.party.parties=B.party.parties
  motifs : A.party.motifs=B.party.motifs

def gatherResources (B : HistoryGatherBody.Layout) :=
  11+4*(HistoryGatherBody.headerTerm 1 B).binds+
    B.demandCap*(18+4*HistoryGatherBody.sourceCost B.mode false)+
    B.supplyCap*(18+4*HistoryGatherBody.sourceCost B.mode true)+18+4*(HistoryGatherBody.gatherTerm 1 B).binds

private theorem gather_write_bound {W : ℕ} (term : Term W 0 1) (base length price : ℕ)
    (work : term.binds=price) :
    resources (PhysicalInputPhases.writing term Fin.elim0 base length) ≤ 11+4*price := by
  rw [resources_write,Nat.add_zero,work]

private theorem gather_scan_bound {W : ℕ} (term : Term W 0 1) (ptr : Word W) (off price : ℕ)
    (work : term.binds ≤ price) :
    resources (HeaderScan.procedure ptr off (off+1) term) ≤ 18+4*price :=
  (resources_scan term ptr off (off+1)).le.trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left 4 work) 18)

private theorem gather_fold_bound {W : ℕ} (entry last : Procedure W) (scan : Bool→ℕ→Procedure W)
    (nd ns d s headWork lastWork : ℕ) (rate : Bool→ℕ) (dCount : nd=d) (sCount : ns=s)
    (initial : resources entry ≤ 11+4*headWork)
    (each : ∀ q j, resources (scan q j) ≤ 18+4*rate q)
    (finish : resources last ≤ 18+4*lastWork) :
    resources (((List.range ns).foldl (fun (p : Procedure W) j=>p.seq (scan true j))
      ((List.range nd).foldl (fun (p : Procedure W) j=>p.seq (scan false j)) entry)).seq last) ≤
      11+4*headWork+d*(18+4*rate false)+s*(18+4*rate true)+18+4*lastWork := by
  subst d
  subst s
  let step (q : Bool) (p : Procedure W) (j : ℕ) := p.seq (scan q j)
  have one (q : Bool) (p : Procedure W) (j : ℕ) :
      resources (step q p j) ≤ resources p+(18+4*rate q) :=
    (resources_seq p (scan q j)).le.trans (Nat.add_le_add_left (each q j) _)
  have demand := fold_resources (List.range nd) (step false) _ (one false) entry
  have supply := fold_resources (List.range ns) (step true) _ (one true)
    ((List.range nd).foldl (step false) entry)
  simp only [List.length_range] at demand supply
  rw [resources_seq,Nat.add_assoc _ 18 (4*lastWork)]
  exact Nat.add_le_add
    (supply.trans (Nat.add_le_add_right (demand.trans (Nat.add_le_add_right initial _)) _))
    finish


section
attribute [local irreducible] resources HeaderScan.procedure PhysicalInputPhases.writing
  HistoryGatherBody.headerTerm HistoryGatherBody.gatherTerm HistoryGatherBody.sourceTerm
  HistoryGatherBody.sourceCost HistoryGatherBody.fields

private theorem gather_source_bound (W : ℕ) (A B : HistoryGatherBody.Layout) (eq : Same A B)
    (q : Bool) (j : ℕ) :
    (HistoryGatherBody.sourceTerm W A q j).binds ≤ HistoryGatherBody.sourceCost B.mode q := by
  rw [← eq.mode]
  exact HistoryGatherBody.source_bound W A q j

set_option maxHeartbeats 800000 in
theorem gather_resources {W : ℕ} (A B : HistoryGatherBody.Layout) (eq : Same A B) :
    resources (HistoryGatherBody.procedure W A) ≤ gatherResources B := by
  unfold HistoryGatherBody.procedure gatherResources
  exact gather_fold_bound
    (PhysicalInputPhases.writing (HistoryGatherBody.headerTerm W A) Fin.elim0 A.temp
      (HistoryGatherBody.fields (W:=W) A).length)
    (HeaderScan.procedure (A.temp : Word W) (2*(A.demandCap+A.supplyCap))
      (2*(A.demandCap+A.supplyCap)+1) (HistoryGatherBody.gatherTerm W A))
    (fun q j=> HeaderScan.procedure (A.temp : Word W) (2*HistoryGatherBody.slot A q j)
      (2*HistoryGatherBody.slot A q j+1) (HistoryGatherBody.sourceTerm W A q j))
    A.demandCap A.supplyCap B.demandCap B.supplyCap (HistoryGatherBody.headerTerm 1 B).binds
    (HistoryGatherBody.gatherTerm 1 B).binds (HistoryGatherBody.sourceCost B.mode)
    eq.demand eq.supply
    (gather_write_bound (HistoryGatherBody.headerTerm W A) A.temp
      (HistoryGatherBody.fields (W:=W) A).length (HistoryGatherBody.headerTerm 1 B).binds
      (HistoryGatherBody.header_work (W:=W) (U:=1) A B eq.mode eq.demand eq.supply))
    (fun q j=>gather_scan_bound (HistoryGatherBody.sourceTerm W A q j) (A.temp : Word W)
      (2*HistoryGatherBody.slot A q j) (HistoryGatherBody.sourceCost B.mode q)
      (gather_source_bound W A B eq q j))
    (gather_scan_bound (HistoryGatherBody.gatherTerm W A) (A.temp : Word W)
      (2*(A.demandCap+A.supplyCap)) (HistoryGatherBody.gatherTerm 1 B).binds
      (HistoryGatherBody.gather_work W 1 A B).le)
end


def motifJoinResources (B : HistoryGatherBody.Layout) (group : Bool) :=
  11+4*(HistoryMotifJoin.joinHeader B 1 group).binds+joinResources (if group then B.party.parties else B.party.motifs)

theorem motif_join_resources {W : ℕ} (A B : HistoryGatherBody.Layout) (eq : Same A B) (q : Bool) :
    resources (HistoryMotifJoin.join A W q)≤ motifJoinResources B q := by
  simp only [HistoryMotifJoin.join,resources_seq,resources_write,Nat.add_zero,
    HistoryMotifJoin.joinHeader_work (W:=W) (U:=1) A B q eq.parties eq.motifs,motifJoinResources]
  apply Nat.add_le_add_left
  rw [← eq.parties,← eq.motifs]
  exact bounded_resources _ _


def motifResources (B : HistoryGatherBody.Layout) :=
  11+4*(HistoryMotifJoin.privateHeader B 1).binds+B.party.parties*(pairResources+gatherResources B)+motifJoinResources B true

theorem motif_resources {W : ℕ} (A B : HistoryGatherBody.Layout) (eq : Same A B) :
    resources (HistoryMotifJoin.motif A W)≤ motifResources B := by
  let step (p : Procedure W) (j : ℕ) :=
    let a := HistoryMotifJoin.withParty A j
    (p.seq (HistoryPartyPair.procedure W a.party)).seq (HistoryGatherBody.procedure W a)
  have one (p : Procedure W) (j : ℕ) : resources (step p j)≤resources p+(pairResources+gatherResources B) := by
    have h := pair_resources (W:=W) (HistoryMotifJoin.withParty A j).party
    have e : Same (HistoryMotifJoin.withParty A j) B := ⟨eq.mode,eq.demand,eq.supply,eq.parties,eq.motifs⟩
    have k := gather_resources (W:=W) _ _ e
    simpa only [step,resources_seq,Nat.add_assoc] using
      Nat.add_le_add_left (Nat.add_le_add h k) (resources p)
  have loop := fold_resources (List.range A.party.parties) step _ one (HistoryMotifJoin.privateRows A W)
  change resources (((List.range A.party.parties).foldl step (HistoryMotifJoin.privateRows A W)).seq _)≤_
  rw [resources_seq,motifResources,← eq.parties]
  rw [List.length_range] at loop
  have init : resources (HistoryMotifJoin.privateRows A W)=
      11+4*(HistoryMotifJoin.privateHeader B 1).binds := by
    rw [HistoryMotifJoin.privateRows,resources_write,Nat.add_zero,
      HistoryMotifJoin.privateHeader_work (W:=W) (U:=1) A B eq.mode]
  rw [init] at loop
  exact Nat.add_le_add loop (motif_join_resources A B eq true)


def kernelResources (B : HistoryGatherBody.Layout) (cap : ℕ) :=
  nodeResources cap+(B.party.motifs+1)*motifResources B+motifJoinResources B false

theorem kernel_resources {W : ℕ} (A B : HistoryGatherBody.Layout) (eq : Same A B) (cap : ℕ) :
    resources (HistoryMotifJoin.kernelProcedure A W cap)≤kernelResources B cap := by
  let p := HistoryNodePorts.phase W A.nodePorts cap
  have hp : resources p=nodeResources cap := node_resources _ _
  have e (j : ℕ) : Same (HistoryMotifJoin.withMotif A j) B := ⟨eq.mode,eq.demand,eq.supply,eq.parties,eq.motifs⟩
  have item (j : ℕ) := motif_resources (W:=W) _ _ (e j)
  unfold HistoryMotifJoin.kernelProcedure
  cases h : A.mode with
  | shrink _ =>
    have loop := fold_resources (List.range A.party.motifs)
      (fun prev j=>prev.seq (HistoryMotifJoin.motif (HistoryMotifJoin.withMotif A j) W)) (motifResources B)
      (fun prev j=>by rw [resources_seq];exact Nat.add_le_add_left (item j) _) p
    have join := motif_join_resources (W:=W) _ _ eq false
    rw [List.length_range,hp] at loop
    rw [resources_seq,kernelResources,← eq.motifs,Nat.add_mul,Nat.one_mul]
    exact Nat.add_le_add
      (loop.trans (Nat.add_le_add_left (Nat.le_add_right _ _) _)) join
  | refresh _ _ _ =>
    have it := item 0
    rw [resources_seq,node_resources]
    rw [kernelResources,Nat.add_mul,Nat.one_mul]
    exact (Nat.add_le_add_left (it.trans (Nat.le_add_left _ _)) _).trans
      (Nat.le_add_right _ _)



def rootScanResources (cap : ℕ) (b : HistoryStageRoot.Bank) := 18+4*((HistoryStageRoot.formula cap b).work+5000)

def rootResources (B : HistoryGatherBody.Layout) (cap : ℕ) :=
  11+4*(HistoryStageBody.joinHeader B cap 1).binds+
  rootScanResources cap .hub+rootScanResources cap .link+rootScanResources cap .mapArgs+
  rootScanResources cap .extArgs+rootScanResources cap .extCommand+
  (11+4*(HistoryStageBody.cache (W:=1) B).binds)+readyResources+joinResources (cap+1)+rootScanResources cap .result

private theorem root_scan_cost (W : ℕ) (A : HistoryGatherBody.Layout) (cap : ℕ)
    (b : HistoryStageRoot.Bank) (off : ℕ) :
    resources (HistoryStageBody.scan A cap W b off)≤rootScanResources cap b := by
  unfold HistoryStageBody.scan rootScanResources
  rw [resources_scan]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 4 (HistoryStageBody.field_bound A cap W b)) 18

private theorem root_write_cost {W : ℕ} (t : Term W 0 1) (addr len budget : ℕ)
    (h : t.binds=budget) :
    resources (PhysicalInputPhases.writing t Fin.elim0 addr len)≤11+4*budget := by
  rw [resources_write, h, Nat.add_zero]

open private binary_binds from OAI.ThreeFlat.RAM.HistoryGatherBody
open private id_field_cost from OAI.ThreeFlat.RAM.HistoryMotifJoin
open private literal_cost from OAI.ThreeFlat.RAM.HistoryStageBody

private theorem root_cache_cost (W : ℕ) (A B : HistoryGatherBody.Layout) :
    (HistoryStageBody.cache (W:=W) A).binds=(HistoryStageBody.cache (W:=1) B).binds := by
  simp only [HistoryStageBody.cache, HistoryStageBody.a, HistoryStageBody.times, HistoryStageBody.nodeId,
    binary_binds, literal_cost, HeaderScan.binds_closed, id_field_cost]

private theorem root_sequence_cost {W : ℕ}
    {start hub links maps args commands cache tape join result : Procedure W}
    {i h l m a c p t j r : ℕ} (initial : resources start ≤ i)
    (hubBound : resources hub ≤ h) (linkBound : resources links ≤ l) (mapBound : resources maps ≤ m)
    (argBound : resources args ≤ a) (cmdBound : resources commands ≤ c) (cacheBound : resources cache ≤ p)
    (tapeBound : resources tape ≤ t) (joinBound : resources join ≤ j) (resultBound : resources result ≤ r) :
    resources ((((((((start.seq hub).seq links).seq maps).seq args).seq commands).seq cache).seq tape).seq
      (join.seq result))  ≤  i+h+l+m+a+c+p+t+j+r := by
  simp only [resources_seq]
  omega

section
attribute [local irreducible] resources readyResources joinResources rootScanResources
  HistoryReadyTape.execute HistoryBoundedBody.procedure HistoryStageBody.scan
  HistoryStageBody.cache HistoryStageBody.joinHeader

set_option maxHeartbeats 800000 in
theorem root_resources {W : ℕ} (A B : HistoryGatherBody.Layout) (eq : Same A B) (cap : ℕ) :
    resources (HistoryStageBody.join A cap W)≤rootResources B cap := by
  unfold HistoryStageBody.join rootResources
  exact root_sequence_cost
    (root_write_cost (HistoryStageBody.joinHeader A cap W) (HistoryStageBody.args A)
      (HistoryStageBody.fields (W:=W) A cap).length _ (HistoryStageBody.joinHeader_work A cap B W 1 eq.mode))
    (root_scan_cost W A cap .hub 0)
    (root_scan_cost W A cap .link 2)
    (root_scan_cost W A cap .mapArgs 4)
    (root_scan_cost W A cap .extArgs 6)
    (root_scan_cost W A cap .extCommand 8)
    (root_write_cost (HistoryStageBody.cache (W:=W) A) (HistoryStageBody.hub A+6) 1 _ (root_cache_cost W A B))
    (ready_resources (fun _ : Fin 1 => ((HistoryStageBody.loc A 22:ℕ):Word W)))
    (bounded_resources (W:=W) ⟨HistoryStageBody.hub A,A.party.seed,A.party.commands⟩ (cap+1))
    (root_scan_cost W A cap .result 12)
end


end
end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI
