import OAI.Hierarchy.DescentPaidResetSources
import OAI.Hierarchy.DescentRecipeClosedReset
import OAI.Hierarchy.DescentNamedGeometry

namespace OAI
/-! # Funding reads on the three families of actual reset sites -/
namespace Hierarchy.DescentPaidResidentCount.Reset
open DescentSixParty DescentCompiler DescentKernelHistory DescentHostDirectory
open DescentResetTrunks DescentStageEdgeReceipt DescentSixParty.StarKeys
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D w hist n h C f g cut tail p : ℕ}
variable {cap : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
variable (b : ClosedReset cap ctl) (issued : b.Recorded p)
local notation "key" => (DescentOrderedReset.grains W b.count b.order)
local notation "vertex" => (b.frame.host.symm.toEmbedding.trans cap.vertex)
local notation "rank" => ((b.reset.rawHostRank b.terminals vertex).trans Fin.valEmbedding)
local notation "rows" => (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) rank)
local notation "ps" => (DescentPhysicalOrder.rename (b.raw.siteFrom rows b.valid.coordinates))
local notation "rawId" => ((b.reset.nativeResetEdges b.terminals vertex key).order.trans Fin.valEmbedding)
local notation "pe" => (DescentPhysicalOrder.rename (DescentResetLocalOrder.allCode b.raw rawId S
  b.valid (b.raw.siteFrom rows b.valid.coordinates)))

local notation "bank" => b.reset.laneRecipe key (b.reset.unit/p) p issued.positive (Nat.div_mul_cancel issued.divides).symm
local notation "names" => b.reset.resetNames b.terminals
local notation "norm" => b.reset.orderedReblock b.terminals key

/-- Three different payees share a reset slot chart. Incoming relay multiplicity is
the number of genuine old grain arrivals, including every unit of a wider cable. -/
def payee : ((Bool×b.reset.Fallback) ⊕ b.reset.bank.Site)→ℕ
  | .inl (false,t)=>∑u : {u : W.graph.Site // b.terminals.home u=t}, (cap.placement.records u.val).length
  | .inl (true,t)=>∑e : {e : W.graph.Edge // b.terminals.home (W.graph.dst e)=t},cap.placement.grainCount e.val
  | .inr a=>Fintype.card (bank a).Node

theorem raw_paid (v) : (b.raw.records v).length=payee b issued (names v) := by
  rw [issued.sizes, b.reset.recipeRecords_length b.terminals cap.placement.records bank v]
  generalize names v=x
  rcases x with ⟨_|_,t⟩|a
  · change Fintype.card (Σu : {u : W.graph.Site // b.terminals.home u=t},Fin (cap.placement.records u.val).length)=_
    simp [payee,Fintype.card_sigma]
  · change Fintype.card {e : Σe : W.graph.Edge,Fin (b.count e) // b.terminals.home (W.graph.dst e.1)=t}=_
    exact (grain_total b.count (fun e : W.graph.Edge => b.terminals.home (W.graph.dst e)) t).trans
      (Finset.sum_congr rfl (fun e _ => congrFun b.count_eq e.val))
  · rfl

/-- The ordinary rename uses the exact source-local edge and site orders
installed on this branch. -/
theorem next_paid :
    (fun v=>(b.next.placement.records v).length)=
      transferRow ((norm).appendNames_result ps pe) ((fun v=>payee b issued (names v))∘(ps).symm) := by
  rw [show (fun v=>payee b issued (names v))=(fun v=>(b.raw.records v).length) from funext (fun v=>(raw_paid b issued v).symm)]
  exact (GroupStage.renamed_particle_fields b.raw ps pe ((norm).appendNames_result ps pe)).1

end
end Hierarchy.DescentPaidResidentCount.Reset

end OAI
