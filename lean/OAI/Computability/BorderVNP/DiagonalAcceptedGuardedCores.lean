import OAI.Computability.BorderVNP.DiagonalPreparedCandidate
import OAI.Computability.BorderVNP.DiagonalPositiveCoreReadback

/-! # Recovering the guarded original core from an entire positive execution -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM TeamContraction ProcessorSlots TeamContraction.JointHeader DiagonalTallyCellReports
open CellMacro.Generator BorderVNP.Cube
open scoped Classical

variable {R n w axes b h K s dim width : ℕ} {id : TableEntry axes b h K s → ℕ} {gen : Fragment IO}
    {X Raw Hist : Type} {Route : Hist → Type} {Bank : Hist → Type} {Report : (i : Raw) → (q : Hist) → Route q → Type}
    (S : X → Fin (R+1) → PositiveTeam id gen n w)
    (J : ∀ x (p : (u : Fin (R+1)) → (S x u).Prefix),
      JoinedCells (fun u => (S x u).pub) (fun u => (S x u).postMemory) (fun u => (S x u).generated) p)
    (prep : JointBeforeCells S ≃ PreparedFields Raw Hist (Fin ((R+1)*dim*width) → Bool) Route Report)
    (banks : ∀ f : PreparedFields Raw Hist (Fin ((R+1)*dim*width) → Bool) Route Report,
      (J (prep.symm f).1 (prep.symm f).2).Private ≃ Bank f.2.1)

local notation "Claim" => Fin ((R+1)*dim*width) → Bool

/-- The physical report-row numbering and observed cell bank for an arbitrary
proposed original core, before screening the reports or the subtotal word. -/
structure PreparedCellRows (i : Raw) (q : Hist) (v : Route q × Bank q) where
  /-- Layout at the team that actually receives the cell. -/
  layout : Fin (R+1) → ReportLayout
  /-- Ordered cell directory of each receiving team. -/
  cells : ∀ u, List (AssignedCell (layout u))
  /-- Physical report digits in the order of these cell rows. -/
  order : Report i q v.1 ≃ NativeReports cells
  /-- On every proposal the same pre-call RAM and private bits supply these rows. -/
  read : PreparedReportImage S J prep banks i q v cells order

section
variable {S J prep banks} {i : Raw} {q : Hist} {v : Route q × Bank q}

/-- The unchecked native execution built from this addressed report directory. -/
noncomputable abbrev PreparedCellRows.candidate (P : PreparedCellRows S J prep banks i q v) :=
  preparedUnchecked S J prep banks i q v P.cells P.order P.read

end

variable (rows : ∀ i q v, PreparedCellRows S J prep banks i q v)

variable {reserve groups cap : ℕ}
    (header : Raw → (q : Hist) → Route q × Bank q → PositiveFields reserve axes groups cap (R+1) dim width)
    (guard : Raw → (q : Hist) → Route q × Bank q → Prop)
    (sound : ∀ i q v r c, let A := (rows i q v).candidate
      (A.joined r c (A.candidate r c).1).privateWeight (A.candidate r c).2 ≠ 0 → guard i q v)
    (complete : ∀ i q v, guard i q v → ((rows i q v).candidate).Completion (header i q v))

/-- Decode the actual shared exterior and all native histories, transport the original
private banks, then check every proposed report and every subtotal. The resulting
fiber retains each guarded original core exactly once, including cores whose
later residue entry evaluates to zero. -/
noncomputable def acceptedGuardedEquiv :
    AcceptedExterior S J ≃ (Σ i : Raw, Σ q : Hist, {v : Route q × Bank q // guard i q v}) := by
  refine (acceptedPrefixBankEquiv S J prep banks).trans (Equiv.sigmaCongrRight fun i =>
    Equiv.sigmaCongrRight fun q => ?_)
  let proposals := Equiv.sigmaCongrRight fun v : Route q × Bank q =>
    preparedReportsEquiv S J prep banks i q v (rows i q v).cells (rows i q v).order (rows i q v).read
  exact proposals.trans (UncheckedCandidate.guardedSourceEquiv (fun v => (rows i q v).candidate)
    (header i q) (guard i q) (sound i q) (complete i q))

include sound complete in
/-- The raw pin, history, source route and original private bank are the ones obtained
before the guessed checks; eliminating reports changes none of these coordinates. -/
theorem acceptedGuardedEquiv_read (a : AcceptedExterior S J) :
    let old := acceptedPrefixBankEquiv S J prep banks a
    let decoded := acceptedGuardedEquiv S J prep banks rows header guard sound complete a
    (⟨decoded.1,decoded.2.1,decoded.2.2.val⟩ : Σ _ : Raw, Σ q : Hist, Route q × Bank q) =
      ⟨old.1,old.2.1,old.2.2.1⟩ := rfl


/-- Reconstruct the full physical positive assignment for a guarded source.
This emits the actual canonical report digits and the row subtotals checked
by each team at its own finishing addresses. -/
noncomputable def restoreGuarded (i : Raw) (q : Hist) (v : Route q × Bank q) (hv : guard i q v) :
    AcceptedExterior S J := by
  let A := (rows i q v).candidate
  let H := complete i q v hv
  let rr := canonicalReports A.assigned H.core
  let c := PositiveFields.canonicalSubtotals width H.rows
  let fields : PreparedFields Raw Hist Claim Route Report := ⟨i,q,v.1,c,(rows i q v).order.symm rr⟩
  exact ⟨(prep.symm fields).1,⟨A.candidate rr c,
    ((A.completed H).pass_iff rr c).mpr ⟨rfl,rfl⟩⟩⟩

/-- The inverse inserts the original private bank into the jointly prepared
prefix. In particular all later reads are from the very same execution that
appears in the integer sum. -/
theorem acceptedGuardedEquiv_symm (i : Raw) (q : Hist) (v : Route q × Bank q) (hv : guard i q v) :
    (acceptedGuardedEquiv S J prep banks rows header guard sound complete).symm ⟨i,q,v,hv⟩ =
      restoreGuarded S J prep banks rows header guard complete i q v hv := rfl

include sound complete in
/-- On a complete accepted execution the product of the signed private
validator returns is one, even when the lead residue computation vanishes. -/
theorem acceptedGuarded_privateWeight (a : AcceptedExterior S J) :
    (J a.1 a.2.val.1).privateWeight a.2.val.2 = 1 := by
  obtain ⟨⟨i,q,v,hv⟩,rfl⟩ := (acceptedGuardedEquiv S J prep banks rows header guard sound complete).symm.surjective a
  rw [acceptedGuardedEquiv_symm]
  let A := (rows i q v).candidate
  let H := complete i q v hv
  let rr := canonicalReports A.assigned H.core
  let c := PositiveFields.canonicalSubtotals width H.rows
  exact UncheckedCandidate.Completion.privateWeight_one A H rr c (((A.completed H).pass_iff rr c).mpr ⟨rfl,rfl⟩)

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
