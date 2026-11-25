import OAI.Hierarchy.DescentResetRegisteredOperandRows
import OAI.Hierarchy.DescentEncodedBookTags

namespace OAI
/-! # The physical reset return publishes a common tagged operand archive -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentDatedPriorOperand DescentPackedColony DescentPackedZip
open DescentOperandStateBanks DescentOperandCandidateLookup DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
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
local notation "acted" m:arg actorMem:arg => ((head).seq ((v).actor.actorBody u.actor ((v).middle.stop b) w)).Exec m actorMem
  (ht+(v).actor.actorTicks u.actor ((v).middle.stop b) w)


open DescentOrdinaryAtomFieldRAM DescentPriorOperandColumns
local notation "L" => (v).rangeLayout

private theorem same_coefficients {srcBits dstBits cellBits K H G M w : ℕ} (width : srcBits=dstBits) (e : cellBits=srcBits)
    (digits : Fin H→Fin G→Fin K→Cell cellBits) (bank : Bank) (mem : Memory w)
    (issued : Reads bank (fun h g=>encode srcBits K (fun n=>(digits h g n).cast (congrArg (2^·) e))) M mem) :
    Reads bank (fun h g=>encode dstBits K (fun n=>(digits h g n).cast (congrArg (2^·) (e.trans width)))) M mem :=by
  subst dstBits
  exact issued

/-- The witness contains the words actually written in all seven banks, together with
a legal kind at every node and argument, including inactive hosts and unused sockets. -/
theorem reset_tagged_books (z : u.FinalInputs) (ok : u.Ready) (space : z.Room) {m mid dst : Memory w}
    (first : u.throughOperandDate.Runs m mid) (run : (PhysicalReset.date z).Runs m dst)
    (bits : (s).coeff=(v).nodeBits) (two : 2 ≤ (v).nodeBits)
    (small : 2*(A).candidates<2^(A).queryBits)
    (reads : ∀actorMem,acted m actorMem → ∀ f j x n,
      Nonempty (OrdinalRead u ok small actorMem ((v).operandOrdinal (s) f j x n)))
    (tag : ∀actorMem,acted m actorMem → ∀ j x n,
      ∃r : OrdinalRead u ok small actorMem ((v).operandOrdinal (s) 0 j x n),∀h g,
      (r.kept h g).val+(selected r.query (fun i h g=>((r.raw i h g).val:Cell (s).coeff)) h g).val ≤ 2) :
    ∃bks : Books L, BookTags bks ∧ ∀x pg,
      Reads (previousBank L (PriorResetArchive.reset (v) b).arguments x pg) (bks x pg) (A).lanes dst :=by
  obtain ⟨mem,actedHere,output⟩:=PhysicalReset.dated_fields z ok space first run bits small
  have one (i : Fin (A).fields) :
      ∃r : OrdinalRead u ok small mem i, ((v).operandIndex (s) i).2.1=0 → ∀h g,
      (r.kept h g).val+(selected r.query (fun j h g=>((r.raw j h g).val:Cell (s).coeff)) h g).val ≤ 2 :=by
    obtain ⟨⟨⟨⟨f,j⟩,x⟩,n⟩,rfl⟩:=((v).operandOrder (s)).surjective i
    change ∃r : OrdinalRead u ok small mem ((v).operandOrdinal (s) f j x n), _
    by_cases firstField : f=0
    · subst f
      obtain ⟨r,c⟩:=tag mem actedHere j x n
      exact ⟨r,fun _=>c⟩
    · obtain ⟨r⟩:=reads mem actedHere f j x n
      exact ⟨r,fun err=>False.elim (firstField (by
        exact ((congrArg (fun z => z.2.1) ((v).operandIndex_ordinal (s) f j x n)).symm.trans err)))⟩
  let rows:=fun i=>Classical.choose (one i)
  let cells:=fun i h g=>(⟨_,(rows i).room h g⟩:Cell (s).coeff)
  have post:=output (fun i=>(rows i).query) (fun i=>(rows i).raw) (fun i=>(rows i).kept) cells
    (fun i=>(rows i).query_read) (fun i=>(rows i).kept_read) (fun i=>(rows i).source_read) (fun _ _ _=>rfl)
  have width : (v).nodeBits=(L).size+2 := by change (v).nodeBits=(v).nodeBits-2+2;omega
  let atNode:=fun (x : Fin (A).blocks) (pg : Pages (v).argumentSlots) (h : Fin (A).hosts)
      (g : Fin (A).groups) (n : Fin (v).nodes)=>
    let fa := (finProdFinEquiv : Fin 7×Fin (v).argumentSlots ≃ _).symm pg
    cells ((v).operandOrdinal (s) fa.1 (fa.2.cast ok.slots.symm) x (n.cast ok.nodes.symm)) h g
  let bks : Books L :=fun x pg h g=>encode ((L).size+2) (v).nodes
    (fun n=>(atNode x pg h g n).cast (congrArg (2^·) (bits.trans width)))
  refine ⟨bks,?_,?_⟩
  · apply bookTags_of_encoded (l:=L)
      (fun x pg h g n=>(atNode x pg h g n).cast (congrArg (2^·) (bits.trans width)))
    intro x j h g n
    let id:=(v).operandOrdinal (s) 0 (j.cast ok.slots.symm) x (n.cast ok.nodes.symm)
    have good:=(Classical.choose_spec (one id)) (congrArg (fun z => z.2.1) ((v).operandIndex_ordinal (s) 0 (j.cast ok.slots.symm) x (n.cast ok.nodes.symm))) h g
    have pg : pageOf j 0 = (finProdFinEquiv : Fin 7 × Fin (v).argumentSlots ≃ _ ) (0, j) := rfl
    rw [pg]
    simp only [atNode,Equiv.symm_apply_apply,Fin.val_cast]
    exact good
  · intro x pg
    obtain ⟨⟨f,j⟩,rfl⟩:=((finProdFinEquiv : (Fin 7×Fin (v).argumentSlots)≃Pages (v).argumentSlots).surjective pg)
    change Reads (previousBank L (PriorResetArchive.reset (v) b).arguments x (DescentOperandStateBanks.page f j)) _ _ dst
    rw [(v).operand_bank b x j f]
    apply same_coefficients width bits
    simp only [atNode,Equiv.symm_apply_apply]
    exact post f j x

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
