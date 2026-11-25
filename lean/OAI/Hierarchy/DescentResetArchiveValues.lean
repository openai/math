import OAI.Hierarchy.DescentResetRegisteredOperandRows
import OAI.Hierarchy.DescentRegisterArchiveValues
import OAI.Hierarchy.DescentRegisterArchiveClaim

namespace OAI
/-! # The physical retained selector and all seven returned reset pages -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentDatedPriorOperand DescentPackedColony DescentPackedZip
open DescentOperandStateBanks DescentOperandCandidateLookup DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
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
local notation:max "acted" m:arg actorMem:arg => ((head).seq ((v).actor.actorBody u.actor ((v).middle.stop b) w)).Exec m actorMem
  (ht+(v).actor.actorTicks u.actor ((v).middle.stop b) w)


section
variable {u}
/-- The finite sum actually written by the retained operand selector. -/
def OrdinalRead.amount {ok : u.Ready} {small actorMem i} (observed : OrdinalRead u ok small actorMem i)
    (h : Fin a.successor.receiver.hosts) (g : Fin a.successor.receiver.groups) : Cell u.operand.coeff :=
  ⟨_,observed.room h g⟩
end

private theorem reindex_rows {l L : Layout} (e:l=L) {width w base : ℕ} {dst : Memory w}
    (x:Fin l.blocks) (j:Fin l.operands) (f:Fin 7)
    (digits:Fin L.nodes→Fin L.hosts→Fin L.groups→Cell width)
    (got:Reads (previousBank L base (x.cast (congrArg Layout.blocks e))
      (page f (j.cast (congrArg Layout.operands e)))) (fun h g=>encode width L.nodes (fun n=>digits n h g)) L.lanes dst) :
    ∃cells:Fin l.hosts→Fin l.groups→Cell (width*l.nodes),
      Reads (previousBank l base x (page f j)) cells l.lanes dst ∧ ∀h g n,
      ((encode width l.nodes).symm (cells h g) n).val=
        (digits (n.cast (congrArg Layout.nodes e)) (h.cast (congrArg Layout.hosts e)) (g.cast (congrArg Layout.groups e))).val:=by
  subst L
  exact ⟨_,got,fun h g n=>by simp⟩

local notation "L" => (ports).rangeLayout
local notation "R" => (v).rangeLayout

/-- The same native actor execution accounts for every pointer and range page.
Each digit equals the counted kept term plus the requested original candidate. -/
theorem reset_archive_values (z:u.FinalInputs) (ok:u.Ready) (space:z.Room) {m mid dst:Memory w}
    (first:u.throughOperandDate.Runs m mid) (run:(PhysicalReset.date z).Runs m dst)
    (bits:(s).coeff=(v).nodeBits) (small:2*(A).candidates<2^(A).queryBits) (e:L=R):
    ∃actorMem,acted m actorMem ∧ ∀choice:∀i,OrdinalRead u ok small actorMem i,
      ∀(x:Fin (L).blocks)(j:Fin (L).operands)(f:Fin 7),
      ∃cells:Fin (L).hosts→Fin (L).groups→Cell ((ports).operandBits*(L).nodes),
        Reads (previousBank L (ports).archive.arguments x (page f j)) cells (L).lanes dst ∧ ∀h g n,
        ((encode (ports).operandBits (L).nodes).symm (cells h g) n).val=
          ((choice ((v).operandOrdinal (s) f ((j.cast (congrArg Layout.operands e)).cast ok.slots.symm)
            (x.cast (congrArg Layout.blocks e)) ((n.cast (congrArg Layout.nodes e)).cast ok.nodes.symm))).amount
             (h.cast (congrArg Layout.hosts e)) (g.cast (congrArg Layout.groups e))).val:=by
  obtain ⟨actorMem,acted_,output⟩:=PhysicalReset.dated_fields z ok space first run bits small
  refine ⟨actorMem,acted_,?_⟩
  intro input x j f
  let x':=x.cast (congrArg Layout.blocks e)
  let j':=j.cast (congrArg Layout.operands e)
  let values:=fun i h g=>(input i).amount h g
  have post:=output (fun i=>(input i).query) (fun i=>(input i).raw) (fun i=>(input i).kept) values
    (fun i=>(input i).query_read) (fun i=>(input i).kept_read) (fun i=>(input i).source_read) (fun _ _ _=>rfl) f j' x'
  rw [←(v).operand_bank b x' j' f] at post
  exact reindex_rows e x j f (fun n h g=>
    (values ((v).operandOrdinal (s) f (j'.cast ok.slots.symm) x' (n.cast ok.nodes.symm)) h g).cast
      (congrArg (2^·) bits)) post

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
