import OAI.Hierarchy.DescentResetAllNodeMetadata
import OAI.Hierarchy.DescentDatePortArchiveRead

namespace OAI
/-! # All reached node metadata on the reset output -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentDatedPriorOperand DescentPackedColony DescentPackedZip
open DescentOperandStateBanks DescentDatedNodeMetadata DescentOperandCandidateLookup DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "A" => (v).receiver
local notation "s" => u.operand
local notation "start" => (v).sheetsStart b
local notation "plan" => (v).linkedRankInputs u.sectors start
local notation "rendered" => (v).renderFromRanks plan b
local notation "ports" => reset a floor u
local notation "head" => a.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
local notation "ht" => a.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits
local notation "acted" m actorMem => ((head).seq ((v).actor.actorBody u.actor ((v).middle.stop b) w)).Exec m actorMem
  (ht+(v).actor.actorTicks u.actor ((v).middle.stop b) w)



private theorem reindex_metadata {c₀ c₁:Chart} (eqn:c₀=c₁) {w lower:ℕ} {mem:Memory w} (f:Fin 2)
    (original:Fin c₁.blocks→Fin c₁.nodes→Fin c₁.hosts→Fin c₁.groups→ℕ)
    (expected:Fin c₀.blocks→Fin c₀.nodes→Fin c₀.hosts→Fin c₀.groups→ℕ)
    (same:∀x n h g,original (x.cast (congrArg Chart.blocks eqn)) (n.cast (congrArg Chart.nodes eqn))
      (h.cast (congrArg Chart.hosts eqn)) (g.cast (congrArg Chart.groups eqn))=expected x n h g)
    (read:∀x,Reads (c₁.bank lower f x) (fun h g=>encode c₁.bits c₁.nodes
      (fun n=>(original x n h g:Cell c₁.bits))) c₁.lanes mem) (x:Fin c₀.blocks):
    Reads (c₀.bank lower f x) (fun h g=>encode c₀.bits c₀.nodes (fun n=>(expected x n h g:Cell c₀.bits))) c₀.lanes mem:=by
  subst c₁
  have equal:original=expected:=funext fun x=>funext fun n=>funext fun h=>funext fun g=>same x n h g
  rw [←equal]
  exact read x

local notation "c₀" => (ports).metadataChart
local notation "c₁" => (v).metadata.chart

/-- Read the reset metadata directly from the actual census and gathered range
tokens, with the unfunded nodes included in the structural arity. -/
theorem reset_archive_metadata (z:u.FinalInputs) (space:z.Room) {m mid out:Memory w}
    (ran:(PhysicalReset.date z).Runs m out) (first:u.throughOperandDate.Runs m mid) (chart:c₀=c₁)
    (amount:Fin (c₁).blocks→Fin (c₁).hosts→Fin (c₁).groups→Cell (v).metadata.paidBits)
    (sp:Fin (c₁).blocks→Fin (c₁).nodes→Fin (s).slots→Fin (c₁).hosts→Fin (c₁).groups→Cell (v).metadata.spanBits)
    (arity:Fin (c₁).blocks→Fin (c₁).nodes→Fin (c₁).hosts→Fin (c₁).groups→ℕ)
    (bounded:∀x n h g,arity x n h g≤(s).slots)
    (live:∀x n j h g,sp x n j h g≠0 ↔ j.val<arity x n h g)
    (counts:∀x,Source ((PhysicalReset.FinalInputs.paid u) x) (amount x) (c₁).lanes (z.tokenImage (z.roleInput mid)))
    (ranges:∀x n j,Source (z.spans x n j) (sp x n j) (c₁).lanes (z.tokenImage (z.roleInput mid)))
    (f:Fin 2) (expected:Fin (c₀).blocks→Fin (c₀).nodes→Fin (c₀).hosts→Fin (c₀).groups→ℕ)
    (agrees:∀x n h g,let X:=x.cast (congrArg Chart.blocks chart);let N:=n.cast (congrArg Chart.nodes chart)
      let H:=h.cast (congrArg Chart.hosts chart);let J:=g.cast (congrArg Chart.groups chart)
      (if f=0 then (if N.val<(amount X H J).val then 1 else 0) else arity X N H J)=expected x n h g)
    (x:Fin (c₀).blocks):
    Reads (metadataPage ports f x) (fun h g=>encode (c₀).bits (c₀).nodes
      (fun n=>(expected x n h g:Cell (c₀).bits))) (c₀).lanes out:=by
  let lower:=(v).metadata.headerEnd ((v).primitiveEnd b)
  let original:=fun (x:Fin (c₁).blocks)(n:Fin (c₁).nodes)(h:Fin (c₁).hosts)(g:Fin (c₁).groups)=>
    if f=0 then (if n.val<(amount x h g).val then 1 else 0) else arity x n h g
  have captured(x:Fin (c₁).blocks):Reads ((c₁).bank lower f x) (fun h g=>encode (c₁).bits (c₁).nodes
      (fun n=>(original x n h g:Cell (c₁).bits))) (c₁).lanes out:=by
    have result:=z.dated_node_fields space ran first amount sp arity bounded live counts ranges f x
    have lower_eq : lower=(c₁).inputsEnd ((v).primitiveEnd b) (v).metadata.paidBits (v).metadata.spanBits := rfl
    rw [lower_eq]
    by_cases left:f=0 <;> simpa [original,left,apply_ite] using result
  exact reindex_metadata chart f original expected agrees captured x

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
