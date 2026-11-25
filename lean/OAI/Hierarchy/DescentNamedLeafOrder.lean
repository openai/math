import OAI.Hierarchy.DescentNamedNativeCaps
import OAI.Hierarchy.DescentNamedExteriorRows
import OAI.Hierarchy.DescentTerminalPortChart
import OAI.Hierarchy.DescentPackedMatchRoster
import OAI.Hierarchy.DescentTerminalReachedVolume

namespace OAI
/-! # Both native charts used to price and read the same terminal network -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalExteriorPackets DescentKernelHistory CorrectionBatch
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)


local notation "s" => S.firstWidth G.b p
local notation "net" => ((Epochs.finish G hu he r).state c).graph
local notation "E" => Fintype.card (Port P X.width)
variable {tail j rest : ℕ} (base : S.baseGroups=2^tail)
variable (width : S.groupWidth k tail 0+k=j+(j+rest))

/-- Original copy/port names follow the signed basis, then the native stable home sort. -/
def leafExternal : (Σ _:Fin S.copies,Fin E) ↪ ℕ :=
  let pins:=NativeBranch.rawPin S (X:=X) (radix:=radix) base width
  let rows:=chart (j:=j) (r:=rest) (publicLayout X G S b hp base width)
  code (pins.symm.trans rows) (publicHost X G S b hp base width)

/-- Positive cable halves follow the actual signed panel. Attached inputs use
the frozen-cohort ranks read by the address generator on the same panel. -/
def leafOperands (v : (net).Site) : Boundary net v ↪ ℕ :=
  let names:=DescentPacking.PackedMatch.Local.Stage.cableNames k
    (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=S.groupCount S.length)) (b.target.vertex.trans Fin.valEmbedding))
  DescentTerminalPortChart.rank b.target.placement (b.target.order.trans Fin.valEmbedding) S b.target.valid names v
    ((densePinEquiv X G S b hp base v).toEmbedding.trans Fin.valEmbedding)

def leafOrder := b.target.terminalOrder p (leafExternal X G S b hp base width) (leafOperands X G S b hp base)

local notation "O" => leafOrder X G S b hp base width
local notation "A" => NativeBranch.localLimit G S
local notation "V" => S.groupCount S.length*2^k

theorem leaf_book_bounds (i : Fin (S.hostSize S.length)) :
    ((O).site i).groups ≤ 4 ∧ ((O).site i).nodes ≤ V ∧
    (∀v,((O).site i).arity v ≤ A) ∧ (∀g,((O).site i).size g ≤ V*A) := by
  have verts : ((O).site i).nodes ≤ V := b.target.occurrence_bound i
  have args (v : Fin ((O).site i).nodes) : ((O).site i).arity v ≤ A :=
    final_slots X G S b hp ((O).node i v)
  have freq:=b.target.groups_le p (leafExternal X G S b hp base width) (leafOperands X G S b hp base) i
  refine ⟨freq,verts,args,?_⟩
  intro g
  calc
    _ ≤ ∑z,((O).site i).size z := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ g)
    _ ≤ ∑v,((O).site i).arity v := DescentTerminalGraphVolume.source_budget O i
    _ ≤ ∑_v : Fin ((O).site i).nodes,A := Finset.sum_le_sum fun v _=>args v
    _ = ((O).site i).nodes*A := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ verts


end
end Hierarchy.DescentSixParty.SeedNamed.Branch
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
