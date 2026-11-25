import OAI.Computability.BorderVNP.DiagonalPositiveCoreReceived
import OAI.Computability.BorderVNP.CubePhysicalSignedVisitOrder
import OAI.Computability.BorderVNP.CubePhysicalReportLedger

/-! # The signed operand order on the actual compact native report table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments.ReceivedRows

open DiagonalTallyCellReports

variable {T C : ℕ} {layout : Fin T → ReportLayout} (R : ReceivedRows layout C)
    (owner : Fin C → Fin T) (stored : ∀ j, owner (R.order j) = j.1)

/-- Restrict the joint physical cell enumeration to the records visited by
one processor, in their actual memory order. -/
noncomputable def compactOrder (t : Fin T) :
    Fin (R.cells t).length ≃ {c : Fin C // owner c=t} := Equiv.ofBijective
  (fun i => ⟨R.order ⟨t,i⟩,stored ⟨t,i⟩⟩) (by
    constructor
    · intro i j eqn
      exact heq_iff_eq.mp ((Sigma.mk.inj_iff.mp (R.order.injective (congrArg Subtype.val eqn))).2)
    · rintro ⟨c,owned⟩
      obtain ⟨⟨v,i⟩,sameCell⟩ := R.order.surjective c
      have same : v=t := (stored ⟨v,i⟩).symm.trans ((congrArg owner sameCell).trans owned)
      subst v
      exact ⟨i,Subtype.ext sameCell⟩)

open Crossing Diagonal.CellEntries NativeLedger FiniteEvaluator BorderVNP.Cube.Tally
open scoped Classical

variable {D n d blocks b h K s B H U : ℕ} {P : Type} {bits : P → ℕ} {N : Network D P bits}
    {cell : N.Site → Fin C}
    (tags : N.Tables (Entry (Fin H) (Fin U))) (words : PowerWords (Fin T) (Fin H) (Fin U) B N tags)
    (label : Fin C → Label (n+1) d) (team : Fin d → Fin T) (path : Path N cell n d blocks b h K s)
    (owners : ∀ j, pathCellOwner label team path (R.order j)=j.1)

/-- An order on the sources of a signed team. Cell ordinals come from
its real compact report table and cube ordinals from the signed vertex
scanner on this path. Unary slots have their complete finite enumeration. -/
noncomputable def ledgerOrder (t : Fin T) : Orders tags words label team path t where
  nUse := Fintype.card {i // routedPowerOwner tags words label team path i=t}
  uses := (Fintype.equivFin _).symm
  nCell := (R.cells t).length
  cells := R.compactOrder (pathCellOwner label team path) owners t
  nVertex := (CubeVisits.teamList (chosen b s path.2.2.2.1) blocks (Fin.val ∘ team) t.val).length
  vertices := nativeVertexOrder label team path t

variable {l : ReportLayout} (rc : ReceivedRows (fun _ : Fin T => l) C)

/-- Obtain the descriptor of a global cell at its actual publishing processor and
compact ordinal, including cells that have no private rows. -/
def nativeReport (c : Fin C) : ReportCell l :=
  let j := rc.order.symm c
  (rc.cells j.1).get j.2

variable (numTags : N.Tables (Entry (Fin l.parameters) (Fin l.gadgets)))
    (numWords : PowerWords (Fin T) (Fin l.parameters) (Fin l.gadgets) B N numTags)
    (hosts : ∀ j, pathCellOwner label team path (rc.order j) = j.1)

/-- The report cells passed to the signed subtotal routine are exactly the
list returned by this processor. The physical vertex ordering operation preserves
this equality. -/
theorem teamReports_native (t : Fin T) :
    let o := rc.ledgerOrder numTags numWords label team path hosts t
    teamReports numTags numWords label team path t (Orders.withNativeVertices numTags numWords label team path t o)
      rc.nativeReport = rc.cells t := by
  intro o
  change (List.ofFn fun j => rc.nativeReport (rc.order ⟨t,j⟩))=_
  let get (j : (t : Fin T) × Fin (rc.cells t).length) := (rc.cells j.1).get j.2
  exact (congrArg List.ofFn (funext fun i => congrArg get (rc.order.symm_apply_apply ⟨t,i⟩))).trans
    (List.ofFn_get (rc.cells t))

/-- The row for a global cell after the native count and use choices were
written onto its owner's actual compact report bank. -/
def reportedWithTape (stream : Fin T → ℕ → Bool) (start : Fin T → ℕ) (c : Fin C) : ReportCell l :=
  let j := rc.order.symm c
  let updated := tapeCells (stream j.1) (start j.1) (rc.cells j.1)
  updated.get (Fin.cast (tapeCells_length ..).symm j.2)

/-- A single source array works on every reported word of every team, at the
same report cursor and in the same native cell order as the signed suffix. -/
theorem teamReports_withTape (stream : Fin T → ℕ → Bool) (start : Fin T → ℕ) (t : Fin T) :
    let o := rc.ledgerOrder numTags numWords label team path hosts t
    teamReports numTags numWords label team path t (Orders.withNativeVertices numTags numWords label team path t o)
      (rc.reportedWithTape stream start) = tapeCells (stream t) (start t) (rc.cells t) := by
  intro o
  change (List.ofFn fun j => rc.reportedWithTape stream start (rc.order ⟨t,j⟩))=_
  let rows := fun t => tapeCells (stream t) (start t) (rc.cells t)
  let get (j : (t : Fin T) × Fin (rc.cells t).length) := (rows j.1).get (Fin.cast (tapeCells_length ..).symm j.2)
  refine (congrArg List.ofFn (funext fun i => congrArg get (rc.order.symm_apply_apply ⟨t,i⟩))).trans ?_
  apply List.ext_getElem
  · exact List.length_ofFn.trans (tapeCells_length ..).symm
  · intro i h h'
    simp only [List.getElem_ofFn]
    rfl

end Cube.Physical.NativeAssignments.ReceivedRows

end BorderVNP
end Computability
end OAI
