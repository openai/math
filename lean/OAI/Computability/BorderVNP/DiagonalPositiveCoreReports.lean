import OAI.Computability.BorderVNP.DiagonalPositiveReportClaimFiber

/-! # Report and subtotal choices before any original core is screened -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM TeamContraction TeamContraction.JointHeader CompactMachine CellMacro.Generator _root_.OAI.Computability.BorderVNP.Cube
open DiagonalTallyCellReports
open scoped BigOperators Classical

variable {axes box lanes selectors symbols T n w reserve groups cap dim width : ℕ}
    {id : TableEntry axes box lanes selectors symbols → ℕ} {gen : Fragment IO}
    {p : PositiveFields reserve axes groups cap T dim width}

/-- Real preparation states and private input vectors of an arbitrary original
candidate, prior to checking the source's native guards. -/
structure UncheckedCandidate (id : TableEntry axes box lanes selectors symbols → ℕ)
    (gen : Fragment IO) (n w : ℕ) (T dim width : ℕ) where
  /-- Report layout at each current owner. -/
  layout : Fin T → ReportLayout
  /-- Physical cell directories and original raw input bits in report order. -/
  assigned : ∀ u, List (AssignedCell (layout u))
  /-- Native positive team at the proposed fields. -/
  team : NativeReports assigned → (Fin (T*dim*width) → Bool) → Fin T → PositiveTeam id gen n w
  /-- Native directories grouped under their real owners. -/
  joined : ∀ r raw (a : (u : Fin T) → (team r raw u).Prefix),
    JoinedCells (fun u => (team r raw u).pub) (fun u => (team r raw u).postMemory) (fun u => (team r raw u).generated) a
  /-- Actual pre-dispatch register state, full RAM and all original private bits. -/
  candidate : ∀ r raw, PositiveAssignment (team r raw) (joined r raw)
  /-- Addressed native reports read by every owned cell at every proposed field. -/
  image : ∀ r raw, (joined r raw (candidate r raw).1).ReportImage (candidate r raw).2 assigned r

namespace UncheckedCandidate

variable (X : UncheckedCandidate id gen n w T dim width)

/-- Data obtained from a successful original guard. The arithmetic allocator
starts only on its native report image. Its receipt comes from the genuine
selected-ID program on that post-builder state. -/
structure Completion (X : UncheckedCandidate id gen n w T dim width) (p : PositiveFields reserve axes groups cap T dim width) where
  core : ∀ u s, s ∈ X.assigned u → s.Passing w n
  /-- The original physical owners' parameter and scalar counts. -/
  rows : Fin T → Fin dim → ℕ
  /-- Selected native operands of the same guarded original source. -/
  input : ∀ raw u, let r := canonicalReports X.assigned core
    let S := X.team r raw u
    let a := (X.candidate r raw).1 u
    let mac := install gen n S.routines
    PositiveFields.FinishInput u rows width S.pub mac (cellBank S.pub mac a.2.val.2.1 a.2.val.2.2) a.2.val.2.2
      (p.withSubtotals raw).tallyWords
  widthFit : width ≤ w
  rowFit : ∀ u c, rows u c < 2^width
  sumFit : ∀ c, ∑ u,rows u c < 2^w

/-- Install the checked reports and physical row counts on the original
machine and the very same pre-dispatch bank. -/
def completed (h : X.Completion p) : NativeReportCandidate id gen n w p :=
  ⟨X.layout,X.assigned,h.core,h.rows,X.team,X.joined,X.candidate,X.image,h.input,h.widthFit,h.rowFit,h.sumFit⟩

/-- Eliminate the report and shared subtotal fields across *all* proposed
original source cores. Only the actual positive predicate occurs on the
physical side. The completed evaluator is used just on surviving cores. -/
noncomputable def guardedSourceEquiv {Source : Type*} (A : Source → UncheckedCandidate id gen n w T dim width)
    (fields : Source → PositiveFields reserve axes groups cap T dim width) (guard : Source → Prop)
    (read : ∀ a r raw, ((A a).joined r raw ((A a).candidate r raw).1).privateWeight ((A a).candidate r raw).2 ≠ 0 → guard a)
    (close : ∀ a,guard a → (A a).Completion (fields a)) :
    (Σ a : Source, Σ r : NativeReports (A a).assigned, {raw : Fin (T*dim*width) → Bool //
      positivePass ((A a).team r raw) ((A a).joined r raw) ((A a).candidate r raw)}) ≃ {a : Source // guard a} := by
  let checked (u : {a : Source // guard a}) := (A u.val).completed (close u.val u.property)
  let includeGuard : (Σ a : Source, Σ r : NativeReports (A a).assigned, {raw : Fin (T*dim*width) → Bool //
      positivePass ((A a).team r raw) ((A a).joined r raw) ((A a).candidate r raw)}) ≃
      (Σ u : {a : Source // guard a}, Σ r : NativeReports (checked u).assigned, {raw : Fin (T*dim*width) → Bool //
        positivePass ((checked u).team r raw) ((checked u).joined r raw) ((checked u).candidate r raw)}) :=
    { toFun := fun ⟨a,r,b,h⟩ => ⟨⟨a,read a r b h.1⟩,r,b,h⟩
      invFun := fun ⟨u,r,b,h⟩ => ⟨u.val,r,b,h⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  refine includeGuard.trans {
    toFun := Sigma.fst
    invFun := fun u => ⟨u,canonicalReports (checked u).assigned (checked u).core,
      PositiveFields.canonicalSubtotals width (checked u).rows,((checked u).pass_iff _ _).mpr ⟨rfl,rfl⟩⟩
    left_inv := ?_
    right_inv := fun _ => rfl }
  rintro ⟨u,r,raw,h⟩
  obtain ⟨rfl,rfl⟩ := ((checked u).pass_iff r raw).mp h
  rfl

end UncheckedCandidate
end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
