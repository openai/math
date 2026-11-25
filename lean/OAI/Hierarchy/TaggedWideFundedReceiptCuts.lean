import OAI.Hierarchy.TaggedWideFundedReceiptCore

namespace OAI
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1600000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open scoped Classical BigOperators Fin.CommRing
open Tagged Tagged.WideStack
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (unitCost : ℕ)

attribute [local irreducible] ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec
  CatalystArchive.recordCount CatalystArchive.issued
  CatalystArchive.nativeSite CatalystArchive.debit

/- Recover the dates from the reconciliation's actual count of issued records. -/
open Lean Elab Term in
local elab "fundedCutReportDates " cert:ident : term => do
  let receipt ← Meta.getFVarFromUserName cert.getId
  let reconciliation ← Meta.whnf (← Meta.inferType receipt)
  unless reconciliation.getAppFn.isConstOf ``Whole.Reconciliation do
    throwError "expected a settlement reconciliation"
  let some rowCountExpr := reconciliation.getAppArgs[7]? | throwError "expected a reconciliation record count"
  let count ← Meta.whnf rowCountExpr
  unless count.getAppFn.isConstOf ``CatalystArchive.recordCount do
    throwError "expected the native record count"
  let issuedExpr ← Meta.whnf count.getAppArgs.back!
  unless issuedExpr.getAppFn.isConstOf ``CatalystArchive.issued do
    throwError "expected the dated issues"
  return ← instantiateMVars issuedExpr.getAppArgs.back!



set_option maxHeartbeats 8000000 in
private abbrev stagedCutStatement {κ B : ℝ} : Prop :=
    ∀ᶠ x : Tagged.WideParent κ B in Tagged.WideParent.large κ B,
      ∀ (size : ℕ) (extent : v.wideFundedSize x.h x.w v.maxBits≤ size)
        (π : Equiv.Perm (Fin (2^x.h))) (raw : Boot.Tape x.h (2^v.W))
        (late : v.wideFundedHeight≤ x.h) (stockRoom : v.keepLimit*x.w+1≤2^x.h)
        (bounded : x.w≤2^x.h) cost state names,
      let placementAt:=v.widePlacement x.h x.w
      let stockAt:=v.fixedTerminalStock placementAt x.h x.w
      let checkout:=v.wideSignedCheckoutAt x.h x.w size stockAt v.radius π
        (wideRouteOrder x.h (2^v.W) k) (v.wideFundedRaw x.h x.w v.maxBits raw)
      let report:=v.wide_native_report x.h x.w size π raw v.maxBits extent late stockRoom bounded cost state names
      checkout ((v.privateArena placementAt x.h x.w).endAddress v.mesh)=0 →
        Nonempty (v.FundedCutRows x.h x.w size π raw report.rows report.geometry unitCost)

attribute [local irreducible] wide_report_for_dates

set_option maxHeartbeats 8000000 in
theorem cofinal_report_cut_rows {κ B : ℝ} (rate : v.sharpPaidUnit≤ unitCost) :
    stagedCutStatement v unitCost (κ:=κ) (B:=B) := by
  have high : Filter.Tendsto (Tagged.WideParent.h (κ:=κ) («A»:=B)) (Tagged.WideParent.large κ B)
      Filter.atTop := Filter.tendsto_comap
  refine ((v.cofinal_funded_budget (κ:=κ) (B:=B)).and
    ((high.eventually v.wide_funded_row_ids).and ((high.eventually v.wideWindow_owner_of_table).and
      (v.wideWindow_raw_cap (κ:=κ) (B:=B) unitCost rate)))).mono ?_
  intro x available
  obtain ⟨price, idAt, ownerAt, boundAt⟩ := available
  intro size extent π raw late stockRoom bounded cost state names placementAt stockAt checkout report accepted
  obtain ⟨_,_,_,amount⟩ := price
  let run := v.wide_funded_run_at x.h x.w v.radius π raw v.maxBits size extent late stockRoom bounded state
  let settled := Classical.choose_spec run
  let certificate := settled.1
  let dated := fundedCutReportDates certificate
  have accounts : 0 < Fintype.card (Columns x.h (2^v.W)) * k :=
    Nat.mul_pos (Fintype.card_pos_iff.mpr ⟨.inl ⟨0,Nat.two_pow_pos _⟩⟩) v.positive
  refine ⟨v.wide_report_cut_rows x.h x.w size π raw extent late stockRoom bounded cost unitCost
    (dates := dated) (pos := accounts) certificate (names _ _) ?_ ?_ ?_ ?_⟩
  · exact amount π raw size extent state accepted
  · exact idAt x.w v.maxBits size extent bounded stockRoom π raw _ _ _
  · exact ownerAt x.w v.maxBits size extent bounded stockRoom π raw _ _ _
  · exact boundAt size extent π raw accepted _ _ _ certificate

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
