import OAI.Hierarchy.DescentOrdinaryDonorRows
import OAI.Hierarchy.DescentHaloParentRoster

namespace OAI
/-! # The original donor shelf address with its group carried in the SIMD lane -/
namespace Hierarchy.DescentRawCablePanel
open DescentSharedCableNames DescentCableDonorNames DescentSixParty DescentPacking
open scoped Classical
noncomputable section
variable {I F P J V : Type} [Fintype I] [DecidableEq I] [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable {d k H R i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {price ε : ℝ} (A : GroupStage W G price ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (old : W.graph.Edge↪ℕ) (vertex : V↪Fin H) (group : J≃Fin R) (pick : I×Fin 2↪W.graph.Edge)
local notation "O" => 2^k*A.cap*11

def birthGroup (e : Live A pick) :=(A.pos (W.graph.src (anchor pick e.val))).1

def shortSlot (e : Live A pick) : Fin H×Fin O :=
  let z:Stage.Positive A:=⟨anchor pick e.val,e.property⟩
  let u:=W.graph.src z.val
  (vertex (A.pos u).2,finProdFinEquiv (finProdFinEquiv (A.block u,Stage.outgoing A old S ready z),role e.val))

omit [Fintype I] [DecidableEq I] in
theorem wide_eq (e : Live A pick) :
    ((slot A S ready old vertex group pick e).2).val=(group (birthGroup A pick e)).val*O+(shortSlot A S ready old vertex pick e).2.val :=by
  let z : Stage.Positive A := ⟨anchor pick e.val,e.property⟩
  let u := W.graph.src z.val
  change (finProdFinEquiv (finProdFinEquiv (finProdFinEquiv (group (A.pos u).1,A.block u),
    Stage.outgoing A old S ready z),role e.val)).val = _
  simp only [finProdFinEquiv_apply_val,shortSlot,birthGroup,u,z]
  ring

/-- All old occurrence addresses are uniform across every group. The
resident scan ranges over block/outgoing/role and never loops over groups. -/
def byGroup (j : J) : {e : Live A pick // birthGroup A pick e=j}↪Fin H×Fin O where
  toFun f:=shortSlot A S ready old vertex pick f.val
  inj':=by
    intro a b eqn
    have coarse : slot A S ready old vertex group pick a.val=slot A S ready old vertex group pick b.val:=by
      apply Prod.ext
      · exact congrArg (fun z : Fin H×Fin O => z.1) eqn
      · apply Fin.ext
        rw [wide_eq A S ready old vertex group pick a.val,wide_eq A S ready old vertex group pick b.val,a.property,b.property]
        exact congrArg (fun z:Fin H×Fin O=>(group j).val*O+z.2.val) eqn
    exact Subtype.ext ((slot A S ready old vertex group pick).injective coarse)

/-- Install this at `ParentFilter.Measured.raw h` with `X=Fin H×Fin O` and
`loc=Embedding.refl _`. Each next observer supplies its *one* old group. -/
def ParentGroupSlot.anchored {E U : Type} [Fintype E] [DecidableEq U] {n : ℕ} {B : Ends U n}
    (C : DescentParallelBase.Blocks B E) (h : U) (g : J) (survives : DescentParallelBase.Local C h↪Live A pick)
    (same : ∀e,birthGroup A pick (survives e)=g) : DescentParallelBase.Local C h↪Fin H×Fin O :=
  (show DescentParallelBase.Local C h↪{e : Live A pick // birthGroup A pick e=g} from
    ⟨fun e=>⟨survives e,same e⟩,fun _ _ he=>survives.injective (congrArg Subtype.val he)⟩).trans (byGroup A S ready old vertex group pick g)

end
end Hierarchy.DescentRawCablePanel

end OAI
