import OAI.Hierarchy.DescentCalendarPublicSocketField
import OAI.Hierarchy.DescentPostedSignedNames
import OAI.Hierarchy.DescentReachedSignedPublicPointer

namespace OAI
/-! The peer and first serial of every emitted reset grain are the reached argument pointer on its original edge. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt
open DescentParallelBase DescentResetSignedScan DescentNextSignedWindow DescentCableDonorNames
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "groups" => S.groupCount (i+1)
local notation "next" => B.reblock.result
local notation "A" => B.next.placement
local notation "ord" => B.next.order.trans Fin.valEmbedding
local notation "board" => Stage.source A ord


open scoped BigOperators
open DescentNextSignedWindow
local notation "C₀" => blocks B
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "live" => fun e : (coarse).graph.Edge=>e∈(coarse).core

open DescentNextSignedWindow.Native
open DescentSIMDLookup DescentOperandStateBanks

set_option quotPrecheck false
local notation "unitAt" host:arg => GrainPorts.Unit A ord C₀ host

open DescentPackedOperand.Public DescentPacking.PackedMatch.Local.Stage
open DescentKernelHistory DescentBundleHistory Computability.BorderVNP.Crossing ThreeFlat.Routing
local notation "originalNames" => cableNames k (groupRank (Fin.valEmbedding (n:=groups)) (B.next.vertex.trans Fin.valEmbedding))
local notation "canonical" side:arg g:arg => endpoint A ord S B.next.valid originalNames side g
local notation "physical" h:arg q:arg => Stage.live A ord S B.next.valid (fieldNames B) h q

/-- The physical table assigns the reached compact peer and first-wire labels to
each port, including ports after a gap in the sparse host directory. -/
theorem published_live_port (host : Host) (port : (A).CellPorts host.1.1 host.1.2 host.2) :
    physical host port=Stage.live A ord S B.next.valid originalNames host port:=by
  apply Option.some.inj
  rw [←Stage.signed_read A ord S B.next.valid (fieldNames B) host port,
      ←Stage.signed_read A ord S B.next.valid originalNames host port]
  exact posted_signed_panel B (Nat.le_refl (Fintype.card B.next.V)) host _

private theorem equal_live_peer {a b : Host} (same : a=b)
    (p : ↥((board).incident a)) (q : ↥((board).incident b)) (wireAt : p.val=q.val) :
    (Stage.neighbors A ord originalNames).slot a p=(Stage.neighbors A ord originalNames).slot b q:=by
  subst b
  exact congrArg ((Stage.neighbors A ord originalNames).slot a) (Subtype.ext wireAt)

private theorem endpoint_loop_fields (q : Stage.Grain A)
    (same : (next).graph.src q.1=(next).graph.dst q.1) (side : Bool) :
    (canonical side q).neighbor=(canonical false q).neighbor ∧
    (canonical side q).wire=(canonical false q).wire:=by
  cases side with
  | false=>exact ⟨rfl,rfl⟩
  | true=>
    have home := congrArg (Stage.home A) same.symm
    constructor
    · exact equal_live_peer B home
        (Stage.ofPort A ord _ (DescentSharedCableNames.Exchange.targetPort A q))
        (Stage.ofPort A ord _ (DescentSharedCableNames.Exchange.sourcePort A q)) rfl
    · let e := Stage.stream A ord q
      apply Fin.ext
      change (board).serial (Stage.home A ((next).graph.dst q.1))
        ((board).peer (Stage.home A ((next).graph.dst q.1)) e) e =
        (board).serial (Stage.home A ((next).graph.src q.1))
          ((board).peer (Stage.home A ((next).graph.src q.1)) e) e
      rw [home]

/-- The port at the actual piece and within-edge offset determines the complete
reached pointer. A loop uses its source-first serial from either signed face. -/
theorem emitted_first_cable {p : ℕ} (hp : 0<p) (host : Host) (u : unitAt host)
    (site : (next).graph.Site) (edge : Incident (next).graph site) (chunk : ℕ)
    (fits : (chunk+1)*p≤(next).graph.width edge.val) (emitted : ((emission B).units u.val.1).1=edge.val)
    (atSite : (if u.val.2 then (next).graph.dst edge.val else (next).graph.src edge.val)=site) :
    let child:=physical host (GrainPorts.port A ord C₀ host u)
    Pointer.cable child.neighbor.val (child.wire.val-child.within.val) chunk=
      B.next.firstCable hp site edge chunk fits:=by
  let q:=(emission B).units u.val.1
  let first : Stage.Grain A:=⟨q.1,⟨0,Nat.zero_lt_of_lt q.2.isLt⟩⟩
  have gr : GrainPorts.grain A ord C₀ host u=q:=by
    change (Stage.stream A ord).symm ((C₀).order u.val.1)=_
    rw [(emission B).order_eq,Equiv.symm_apply_apply]
  have port : physical host (GrainPorts.port A ord C₀ host u)=canonical u.val.2 q:=calc
    _ = Stage.live A ord S B.next.valid originalNames host (GrainPorts.port A ord C₀ host u) :=
      published_live_port B host _
    _ = _ := by rw [GrainPorts.at_end,gr]
  have common:=DescentResetWindowFields.first_signed_fields A ord S B.next.valid originalNames C₀ live
    (emission B) u.val.1.1 u.val.1.2 u.val.2
  change (canonical u.val.2 q).neighbor=(canonical u.val.2 first).neighbor ∧
    (canonical u.val.2 q).wire.val-(canonical u.val.2 q).within.val=(canonical u.val.2 first).wire.val at common
  have positive : 0<(A).grainCount edge.val:=by rw [←emitted];exact Nat.zero_lt_of_lt q.2.isLt
  let begin_ : Stage.Grain A:=⟨edge.val,⟨0,positive⟩⟩
  have initial : first=begin_:=Sigma.ext emitted
    ((Fin.heq_ext_iff (congrArg (fun e=> (A).grainCount e) emitted)).mpr rfl)
  rw [initial] at common
  let chosen:=decide ((next).graph.src edge.val≠site)
  have choose : (canonical u.val.2 begin_).neighbor=(canonical chosen begin_).neighbor ∧
      (canonical u.val.2 begin_).wire=(canonical chosen begin_).wire:=by
    by_cases loop : (next).graph.src edge.val=(next).graph.dst edge.val
    · obtain ⟨a,b⟩:=endpoint_loop_fields B begin_ loop u.val.2
      obtain ⟨c,e⟩:=endpoint_loop_fields B begin_ loop chosen
      exact ⟨a.trans c.symm,b.trans e.symm⟩
    · have id : chosen=u.val.2:=by
        cases right:u.val.2
        · simp only [right,Bool.false_eq_true,ite_false] at atSite
          simp [chosen,atSite]
        · simp only [right,ite_true] at atSite
          simp [chosen,←atSite,loop]
      rw [id]
      exact ⟨rfl,rfl⟩
  change Pointer.cable _ _ chunk=_
  rw [port,common.1,common.2,choose.1,choose.2]
  exact (Reached.firstCable_endpoint B.next hp site edge chunk fits positive).symm

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
