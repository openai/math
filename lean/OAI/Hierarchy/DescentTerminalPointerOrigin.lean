import OAI.Hierarchy.DescentTerminalPointerInputs
import OAI.Hierarchy.DescentTerminalOperandSlots
import OAI.Hierarchy.DescentTerminalPortChart
import OAI.Hierarchy.DescentBundleTerminal

namespace OAI
/-! # Private, cable, and pin origins of the reached terminal argument -/
namespace Hierarchy.DescentTerminalPointerIssue
open Computability.BorderVNP.Crossing DescentSixParty DescentSharedCableNames DescentKernelHistory DescentTerminalPortChart
open DescentBundleHistory DescentCompiler DescentColonies DescentLocalPrivateNames
open DescentOperandStateBanks DescentTerminalPointerDigits DescentTerminalChronologicalBooks
open ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section

section Slots
variable {Tag B : Type} {N A D cap : ℕ} (r:Recipe Tag B) (birth:r.Node↪ℕ)
    (nodes:Fintype.card r.Node≤N) (arity:∀u,r.arity u≤A)
local notation "nr" => row r birth nodes
local notation "whereAt" => slot r birth nodes arity
variable (t : CellInputs D cap N A)
theorem live_slot (head:t.n=Fintype.card r.Node) (cols:∀u,t.arity (nr u)=r.arity u) (s:Slot r) :
    t.active (whereAt s) := by
  unfold CellInputs.active
  let pair:= (nr s.1,s.2.castLE (arity s.1))
  change (finProdFinEquiv.symm (finProdFinEquiv pair)).1.val<t.n ∧
    (finProdFinEquiv.symm (finProdFinEquiv pair)).2.val<t.arity (finProdFinEquiv.symm (finProdFinEquiv pair)).1
  dsimp only [pair]
  rw [Equiv.symm_apply_apply,head,cols]
  exact ⟨(ordinal birth s.1).isLt,s.2.isLt⟩

end Slots

section Sources
variable {P Tag : Type} [Fintype P] {d p D cap N A K : ℕ} {bits:P→ℕ}
    (G:Network d P bits) (v:G.Site) (r:Recipe Tag (BlockRef p (boundaryWidth G v)))
    (birth:r.Node↪ℕ) (nodes:Fintype.card r.Node≤N) (arity:∀u,r.arity u≤A) (aliases:Slot r↪Fin K)
    (rk:Boundary G v↪ℕ) (port:Attached G v↪ℕ) (t:CellInputs D cap N A)
local notation "loc" => slot r birth nodes arity
local notation "alias" => firstAlias r aliases
/-- Original decoded pointers with their actual incident or exterior identity. The
source need only account for existing operands. The native active predicate decides
which words contribute to the distinct private-name census. -/
structure Origin : Prop where
  population : t.n=Fintype.card r.Node
  arities : ∀u,t.arity (row r birth nodes u)=r.arity u
  privateWord : ∀s (h:r.UsedWord),r.operand s.1 s.2=.inr h.val→t.pointer (loc s)=.privateWord (alias h).val
  cable : ∀s (e:Incident G v) j (clip:(j+1)*p≤G.width e.val),
    r.operand s.1 s.2=.inl ⟨.inl e,j,clip⟩→∃peer serial,
      t.pointer (loc s)=.cable peer serial j ∧ rk (.inl e)=peer*cap+serial
  exterior : ∀s (z:Attached G v) j (clip:(j+1)*p≤bits z.val),
    r.operand s.1 s.2=.inl ⟨.inr z,j,clip⟩→∃k,
      t.pointer (loc s)=.pin k j ∧ (Finset.univ.filter (fun a:Attached G v=>port a<port z)).card=k

end Sources

/-- Replace only the original public-copy label by its attained final cohort rank. -/
def reindexed {D cap N M:ℕ} (t:CellInputs D cap N M) (index:ℕ→ℕ) : CellInputs D cap N M :=
  {t with pointer:=fun i=>reindex index (t.pointer i)}

section Reached
variable {F P J V Tag : Type} [Field F] [Fintype P] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i p q N M K tags : ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F} {price ε:ℝ}
    (A:GroupStage W G price ε J V k) (native:W.graph.Edge↪ℕ) (S:AtomSchedule) (ready:A.StateBounds S i)
    (names:Stage.Host J V k↪ℕ) (v:W.graph.Site)
    (port:Attached W.graph v↪ℕ) (hp:0<p)
    (r:Recipe Tag (BlockRef p (boundaryWidth W.graph v)))
    (birth:r.Node↪ℕ) (nodes:Fintype.card r.Node≤N) (arity:∀u,r.arity u≤M) (aliases:Slot r↪Fin K)
    (t:CellInputs A.degree A.cap N M)
local notation "rk" => rank A native S ready names v port
local notation "loc" => slot r birth nodes arity
local notation "G'" => W.graph

include hp in
/-- The old cable fields name the nearest signed first grain. This constructor
computes its boundary rank from the reached geometry and relabels a public pin only
when it passes through the original-copy permutation. -/
theorem origin_fields (freeze:ℕ→ℕ) (original:Attached G' v→ℕ)
    (population:t.n=Fintype.card r.Node) (arities:∀u,t.arity (row r birth nodes u)=r.arity u)
    (hidden:∀s (h:r.UsedWord),r.operand s.1 s.2=.inr h.val→
      t.pointer (loc s)=.privateWord (firstAlias r aliases h).val)
    (cable:∀s (e:Incident G' v) j (clip:(j+1)*p≤W.graph.width e.val) (alive:0<A.grainCount e.val),
      let wing:=Stage.live A native S ready names (Stage.home A v) (DescentTerminalPortChart.first A v e alive)
      r.operand s.1 s.2=.inl ⟨.inl e,j,clip⟩→t.pointer (loc s)=.cable wing.neighbor.val wing.wire.val j)
    (pin:∀s (z:Attached G' v) j (clip:(j+1)*p≤bits z.val),
      r.operand s.1 s.2=.inl ⟨.inr z,j,clip⟩→t.pointer (loc s)=.pin (original z) j)
    (frozen:∀z,(Finset.univ.filter (fun a:Attached G' v=>port a<port z)).card=freeze (original z)) :
    Origin G' v r birth nodes arity aliases rk port (reindexed t freeze) := by
  refine ⟨population,arities,?_,?_,?_⟩
  · intro s h hit
    simp only [reindexed,hidden s h hit,reindex]
  · intro s e j clip hit
    have nonempty:=Nat.mul_pos (Nat.zero_lt_succ j) hp
    have alive : 0 < A.grainCount e.val :=
      DescentTerminalPortChart.positive_of_bit A S ready v e ⟨0, nonempty.trans_le clip⟩
    let wing:=Stage.live A native S ready names (Stage.home A v) (DescentTerminalPortChart.first A v e alive)
    refine ⟨wing.neighbor.val,wing.wire.val,?_,?_⟩
    · exact congrArg (reindex freeze) (cable s e j clip alive hit)
    · rw [positive_rank A native S ready names v port e alive]
      change wing.wire.val+A.cap*wing.neighbor.val=wing.neighbor.val*A.cap+wing.wire.val
      ring
  · intro s z j clip hit
    exact ⟨freeze (original z),by simp only [reindexed,pin s z j clip hit,reindex],frozen z⟩

end Reached

end
end Hierarchy.DescentTerminalPointerIssue

end OAI
