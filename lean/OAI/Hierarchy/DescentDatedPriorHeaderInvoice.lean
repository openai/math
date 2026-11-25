import OAI.Hierarchy.DescentMaterialTariffNumbers
import OAI.Hierarchy.DescentDatedPriorHeaderProgram
import OAI.Hierarchy.DescentSignedPrefixInvoice

namespace OAI
/-! The complete native four/eight-hop prior header has one public
clock and text bill across all ordinary geometry consumers. -/
namespace Hierarchy.DescentDatedAddressBook.PriorHeader
open DescentHaloWalkRAM DescentStaticWordColumn DescentDyadicSpan DescentSIMDLookup
open Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
noncomputable section
variable (H G M D:ℕ) (base:ℕ) (adj:Bank)
local notation "P"=>breadth D
local notation "J"=>H*(P*P)
local notation "N"=>H*P
local notation "pitch"=>stride H G M D
def time (H G M D:ℕ):=4+10*((breadth D+13)*stride H G M D)+7*(8+(H*(breadth D*breadth D))*(2*opLimit D+4))+4
def code (H G M D:ℕ):=15*((breadth D+13)*stride H G M D+1)+7*(15+(11+4*opLimit D))+15

private theorem operations (job:SignedPrefix.Job) (inList:job∈jobs H G M D base adj):
    job.within (opLimit D):=by
  simp only [jobs,List.mem_cons,List.not_mem_nil,or_false] at inList
  rcases inList with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
  · trivial
  all_goals intro i hi;dsimp only;unfold opLimit
  · have h:=DescentHaloWalkRAM.body_work (walks H G M D base adj) H D 4;omega
  · have h:=Ranks.body_work (ranks4 H G M D base) P;omega
  · have h:=Gather.work (duplicates H G M D base) H P;omega
  · have h:=Rebase.body_work (reversals H G M D base) .rank H D;omega
  · have h:=Rebase.body_work (reversals H G M D base) .path H D;omega
  · simp only [PairRanks.op,Expr.work]
    omega
  · have h:=Ranks.body_work (ranks8 H G M D base) (P*P);omega

theorem priced (w:ℕ):
    (phase H G M D base adj w).ticks≤time H G M D ∧
    names (phase H G M D base adj w).program≤code H G M D:=by
  have p:0<P:=by dsimp [breadth];positivity
  have n:N≤J:=by rw [←Nat.mul_assoc];exact Nat.le_mul_of_pos_right _ p
  have term:=Nat.mul_le_mul_right (2*opLimit D+4) n
  have inv:=SignedPrefix.invoice (fun _=>lastPhase w) (jobs H G M D base adj) base (opLimit D)
    (operations H G M D base adj)
  have tailClock : (lastPhase w).ticks=4 := rfl
  have tailNames : names (lastPhase w).program=15 := by
    change names (ProtocolRAM.scan w 0 0 (.lit 0))=15
    simp only [names_scan,Expr.work]
  constructor
  · apply inv.1.trans
    simp only [jobs,SignedPrefix.Job.clocks,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      Nat.add_zero,Nat.one_mul,tailClock,time]
    omega
  · apply inv.2.trans
    simp only [jobs,SignedPrefix.Job.textSize,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      Nat.add_zero,Nat.one_mul,tailNames,code]
    omega

theorem costs {ι:ℕ→Type*} (h g m d:∀t,ι t→ℕ) (hosts:Bounded h) (diam:Bounded d)
    (paths:Bounded fun t i=>breadth (d t i)) (rows:Bounded fun t i=>h t i*chunks (g t i) (m t i)):
    Bounded (fun t i=>time (h t i) (g t i) (m t i) (d t i)) ∧
    Bounded (fun t i=>code (h t i) (g t i) (m t i) (d t i)):=by
  let c:=@Bounded.const ι
  have sq:=paths.mul paths
  have op:Bounded fun t i=>opLimit (d t i):=
    ((c 128).add ((c 20).mul ((diam.add (c 10)).pow 4))).add ((c 64).mul (paths.add sq))
  have pad:=((((c 1).add hosts).add (hosts.mul sq)).add rows).padded
  have paid:Bounded fun t i=>(breadth (d t i)+13)*stride (h t i) (g t i) (m t i) (d t i):=
    (paths.add (c 13)).mul pad
  exact ⟨(((c 4).add ((c 10).mul paid)).add ((c 7).mul ((c 8).add ((hosts.mul sq).mul (((c 2).mul op).add (c 4)))))).add (c 4),
    (((c 15).mul (paid.add (c 1))).add ((c 7).mul ((c 15).add ((c 11).add ((c 4).mul op))))).add (c 15)⟩
end
end Hierarchy.DescentDatedAddressBook.PriorHeader

end OAI
