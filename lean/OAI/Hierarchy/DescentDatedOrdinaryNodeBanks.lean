import OAI.Hierarchy.DescentOrdinaryUnfundedArity
import OAI.Hierarchy.DescentDatedPhysicalOperandBanks
import OAI.Hierarchy.DescentDatedOrdinaryCountRoof

namespace OAI
/-! # The ordinary node checkpoint reads the true f6 page of each retained operand -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedPriorOperand DescentSIMDLookup DescentPackedColony DescentPackedZip DescentOperandStateBanks ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM DescentOrdinaryAtomFieldRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) {w : ℕ}

def nodeChart : DescentDatedNodeMetadata.Chart:=⟨v.resolver.blocks,v.resolver.nodes,v.resolver.hosts,
  v.resolver.groups,v.metadata.chart.bits,v.resolver.lanes⟩
def spanVectors (floor : ℕ) (x : Fin v.resolver.blocks) (j : Fin v.resolver.operands) : Bank :=
  previousBank v.resolver (v.vectorOutput floor) x (page 6 j)

theorem nodeEnd (floor : ℕ) (shape : v.metadata.chart=v.nodeChart) (span : v.metadata.spanBits=v.resolver.size+2) :
    v.nodeChart.ordinaryEnd (v.metaStart floor) v.metadata.paidBits (v.resolver.size+2)=v.metaEnd floor :=by
  change _=v.metadata.chart.ordinaryEnd (v.metaStart floor) v.metadata.paidBits v.metadata.spanBits
  rw [shape,span]

theorem span_vectors_post (floor : ℕ) (side : Fin v.resolver.jobs→Fin 6→Bank) (route : Fin v.resolver.jobs→Fin 3→Bank)
    (m : Memory w) (dims : v.VectorShape) (early : (v.operandBanks floor side route).Early (v.normalizedEnd floor) w)
    (space : v.endAddress floor<2^w) (wide : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2)
    (x : Fin v.resolver.blocks) (j : Fin v.resolver.operands)
    (Y : Fin v.resolver.hosts→Fin v.resolver.groups→Cell ((v.resolver.size+2)*v.resolver.nodes))
    (original : Reads (v.spanVectors floor x j) Y v.resolver.lanes m) :
    (v.spanVectors floor x j).Fits w (v.endAddress floor) ∧ v.resolver.rows≤(v.spanVectors floor x j).size ∧
    Reads (v.spanVectors floor x j) Y v.resolver.lanes (v.operandState (v.operandBanks floor side route) floor m) :=by
  have before:=v.resolver.floor_le (v.normalizedEnd floor)
  obtain ⟨fit,cap⟩:=from_previous_placed v.resolver v.vector (v.vectorStart floor) dims.operands dims.blocks dims.hosts
    dims.groups dims.lanes ((v.routed_le floor).trans_lt (before.trans_lt space)) x (page 6 j)
  refine ⟨⟨fit.1,fit.2.1,fit.2.2.trans ((v.routed_le floor).trans before)⟩,cap,?_⟩
  have scan:=v.operand_any (v.operandBanks floor side route) floor m early space wide
  intro r
  exact (scan.2.1 _ (.inl ((Nat.add_lt_add_left ((row _ _ _ r).isLt.trans_le cap) _).trans_le (fit.2.2.trans (v.routed_le floor))))).trans (original r)

/-- Both masks use the actual previous vector carried through the ordinary scalar resolver.
A genuine funded count distinguishes a real nullary node from a missing gate. -/
theorem node_checkpoint_all (floor fundingEnd : ℕ) (side : Fin v.resolver.jobs→Fin 6→Bank) (route : Fin v.resolver.jobs→Fin 3→Bank)
    (m : Memory w) (dims : v.VectorShape) (early : (v.operandBanks floor side route).Early (v.normalizedEnd floor) w)
    (funded : Memory w) (afterResolve : v.endAddress floor≤fundingEnd)
    (frame : ∀a<v.normalizedEnd floor,funded a=(v.operandState (v.operandBanks floor side route) floor m) a)
    (room : v.nodeChart.ordinaryEnd fundingEnd v.metadata.paidBits (v.resolver.size+2)<2^w) (wide : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2)
    (paid : Fin v.resolver.blocks→Expr) (payFits : ∀x,(paid x).Fits w fundingEnd)
    (amount : Fin v.resolver.blocks→Fin v.resolver.hosts→Fin v.resolver.groups→Cell v.metadata.paidBits)
    (payRead : ∀x,Source (paid x) (amount x) v.resolver.lanes funded)
    (Y : Fin v.resolver.blocks→Fin v.resolver.operands→Fin v.resolver.hosts→Fin v.resolver.groups→Cell ((v.resolver.size+2)*v.resolver.nodes))
    (original : ∀x j,Reads (v.spanVectors floor x j) (Y x j) v.resolver.lanes m)
    (arity : Fin v.resolver.blocks→Fin v.resolver.nodes→Fin v.resolver.hosts→Fin v.resolver.groups→ℕ)
    (bound : ∀x n h g,arity x n h g≤v.resolver.operands)
    (live : ∀x n j h g,ScalarOperand.take (a:=v.resolver.size+2) n (Y x j h g)≠0 ↔ j.val<arity x n h g)
    (f : Fin 2) (x : Fin v.resolver.blocks) :
    let c:=v.nodeChart;let start:=fundingEnd;let a:=v.metadata.paidBits;let b:=v.resolver.size+2
    let done:=c.ordinaryImage start a b paid (v.spanVectors floor) funded
    Reads (c.bank (c.inputsEnd (c.digitEnd start b) a b) f x) (fun h g=>encode c.bits c.nodes (fun n=>
      if f=0 then (if n.val<(amount x h g).val then (1:Cell c.bits) else 0) else (arity x n h g:Cell c.bits))) c.lanes done :=by
  have lo : fundingEnd≤v.nodeChart.digitEnd fundingEnd (v.resolver.size+2):=Nat.le_add_right ..
  have checked:=v.nodeChart.digitRoom fundingEnd v.metadata.paidBits (v.resolver.size+2) room
  have good:=(afterResolve.trans lo).trans_lt checked
  have banks (x j):=v.span_vectors_post floor side route m dims early good wide x j _ (original x j)
  have kept (x j) : Reads (v.spanVectors floor x j) (Y x j) v.resolver.lanes funded:=by
    obtain ⟨fit,sz⟩:=from_previous_placed v.resolver v.vector (v.vectorStart floor) dims.operands dims.blocks
      dims.hosts dims.groups dims.lanes ((v.routed_le floor).trans_lt ((v.resolver.floor_le (v.normalizedEnd floor)).trans_lt good)) x (page 6 j)
    intro p
    exact (frame _ ((Nat.add_lt_add_left ((row _ _ _ p).isLt.trans_le sz) _).trans_le (fit.2.2.trans (v.routed_le floor)))).trans ((banks x j).2.2 p)
  exact v.nodeChart.ordinaryPair fundingEnd v.metadata.paidBits (v.resolver.size+2) paid (v.spanVectors floor) funded
    amount Y arity bound live payFits (fun x j=>⟨(banks x j).1.1,(banks x j).1.2.1,(banks x j).1.2.2.trans afterResolve⟩)
    payRead (fun x j=>(banks x j).2.1) kept room f x

theorem node_checkpoint (floor fundingEnd : ℕ) (side : Fin v.resolver.jobs→Fin 6→Bank) (route : Fin v.resolver.jobs→Fin 3→Bank)
    (m : Memory w) (dims : v.VectorShape) (early : (v.operandBanks floor side route).Early (v.normalizedEnd floor) w)
    (funded : Memory w) (afterResolve : v.endAddress floor≤fundingEnd)
    (frame : ∀a<v.normalizedEnd floor,funded a=(v.operandState (v.operandBanks floor side route) floor m) a)
    (room : v.nodeChart.ordinaryEnd fundingEnd v.metadata.paidBits (v.resolver.size+2)<2^w) (wide : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2)
    (paid : Fin v.resolver.blocks→Expr) (payFits : ∀x,(paid x).Fits w fundingEnd)
    (amount : Fin v.resolver.blocks→Fin v.resolver.hosts→Fin v.resolver.groups→Cell v.metadata.paidBits)
    (payRead : ∀x,Source (paid x) (amount x) v.resolver.lanes funded)
    (Y : Fin v.resolver.blocks→Fin v.resolver.operands→Fin v.resolver.hosts→Fin v.resolver.groups→Cell ((v.resolver.size+2)*v.resolver.nodes))
    (original : ∀x j,Reads (v.spanVectors floor x j) (Y x j) v.resolver.lanes m)
    (arity : Fin v.resolver.blocks→Fin v.resolver.nodes→Fin v.resolver.hosts→Fin v.resolver.groups→ℕ)
    (bound : ∀x n h g,arity x n h g≤v.resolver.operands)
    (live : ∀x n j h g,ScalarOperand.take (a:=v.resolver.size+2) n (Y x j h g)≠0 ↔ n.val<(amount x h g).val ∧ j.val<arity x n h g)
    (f : Fin 2) (x : Fin v.resolver.blocks) :
    let c:=v.nodeChart;let start:=fundingEnd;let a:=v.metadata.paidBits;let b:=v.resolver.size+2
    let done:=c.ordinaryImage start a b paid (v.spanVectors floor) funded
    Reads (c.bank (c.inputsEnd (c.digitEnd start b) a b) f x) (fun h g=>encode c.bits c.nodes (fun n=>
      if n.val<(amount x h g).val then if f=0 then (1:Cell c.bits) else (arity x n h g:Cell c.bits) else 0)) c.lanes done :=by
  classical
  let active (x : Fin v.resolver.blocks) (n : Fin v.resolver.nodes) (h : Fin v.resolver.hosts) (g : Fin v.resolver.groups) :=
    if n.val<(amount x h g).val then arity x n h g else 0
  have bound' x n h g : active x n h g≤v.resolver.operands:=by
    unfold active
    split <;> first | exact bound .. | exact Nat.zero_le _
  have live' x n j h g : ScalarOperand.take (a:=v.resolver.size+2) n (Y x j h g)≠0 ↔ j.val<active x n h g:=by
    rw [live]
    by_cases hn:n.val<(amount x h g).val <;> simp [active,hn]
  have observed:=v.node_checkpoint_all floor fundingEnd side route m dims early funded afterResolve frame room wide
    paid payFits amount payRead Y original active bound' live' f x
  let c:=v.nodeChart
  have eqn : (fun (h : Fin c.hosts) (g : Fin c.groups)=>encode c.bits c.nodes (fun n=>
      if f=0 then (if n.val<(amount x h g).val then (1:Cell c.bits) else 0) else (active x n h g:Cell c.bits))) =
      (fun h g=>encode c.bits c.nodes (fun n=>
        if n.val<(amount x h g).val then if f=0 then (1:Cell c.bits) else (arity x n h g:Cell c.bits) else 0)):=by
    funext h g
    apply congrArg (encode c.bits c.nodes)
    funext n
    by_cases hn:n.val<(amount x h g).val <;> by_cases hf:f=0 <;> simp [active,hn,hf]
  exact (congrArg (fun values => Reads _ values _ _) eqn).mp observed

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
