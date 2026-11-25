import OAI.Hierarchy.TaggedWideFundedCursorRows
import OAI.Hierarchy.WidthSignedPathCertificate
import OAI.Hierarchy.TaggedWideFundedReceiptCuts
import OAI.Hierarchy.ProbeFixedPathCash

namespace OAI
/-! # Cofinal funding of the row geometry on every actual encoded calendar path -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute WireTelescope CalendarTape
open Tagged Filter CoreBoard.PhysicalTerm
open scoped Classical Fin.CommRing
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option cleanup.letToHave false

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (unitCost : ℕ)

private abbrev pathCutCondition (x : WideParent κ A) : Prop :=
      ∃ (age : v.wideStockHeight ≤ x.h) (budget : v.keepLimit*x.w+1 ≤ 2^x.h)
        (small : x.w ≤ 2^x.h) (late : v.reportHeight ≤ x.h) (room : v.ReportWordRoom x.h x.w),
      ∀(size : ℕ) (expanse : v.wideFundedSize x.h x.w v.maxBits ≤ size)
        (π : Equiv.Perm (Tagged.Row x.h)) (seed : Boot.Tape x.h (2^v.W)),
      let reader:=v.wideSelector x.h x.w age budget small
      let es:=events v.mesh
      let base:=v.wideOrigin x.h x.w size seed π
      ∀j : Path reader.format.slot es base,
      let raw:=reader.format.windows.header es (encode reader.format.slot es base j) seed
      let report:=v.wide_reported_path x.h x.w size π seed age budget small expanse late room j
      Nonempty (v.FundedCutRows x.h x.w size π.symm raw report.rows report.geometry unitCost)

/-- The same choice of word bounds works for every permutation, initial tape
and complete path. The receipt prices exactly the original report's row geometry. -/
theorem cofinal_reported_path_cut_rows (rate : v.sharpPaidUnit ≤ unitCost) :
    ∀ᶠ x : WideParent κ A in WideParent.large κ A, pathCutCondition v unitCost x := by
  refine ((v.wide_path_cash (κ:=κ) (A:=A)).and ((v.cofinal_report_sources (κ:=κ) (B:=A)).and
    (v.cofinal_report_cut_rows (κ:=κ) (B:=A) unitCost rate))).mono ?_
  intro x available
  obtain ⟨dims,sources,fund⟩ := available
  obtain ⟨age,budget,small,_⟩ := dims
  obtain ⟨late,room⟩ := sources
  refine ⟨age,budget,small,late,room,?_⟩
  intro size expanse π seed reader es base j raw report
  obtain ⟨admitted,cost,names,accepted,eqn⟩ :=
    v.wide_reported_path_funded x.h x.w size π seed age budget small expanse late room j
  let native:=v.signedPathNativeReport x.h x.w size π.symm raw v.maxBits expanse admitted budget
    small cost 0 names
  have paid := fund size expanse π.symm raw admitted budget small cost 0 names accepted
  let n:=(v.widePlacement x.h x.w).catalogue.rows
  let T:=(lines : Fin n → ProtocolRAMEmit.Row) ×
    ProtocolRAMEmit.Geometry (boardLayout x.h (2^v.W) k x.w (CatalystArchive.fuel v.mesh*x.w)) v.radius 1 lines
  have transferred : (⟨report.rows,report.geometry⟩ : T)=⟨native.rows,native.geometry⟩ :=
    eq_of_heq (Sigma.mk.inj_iff.mp eqn).2
  let priced (s : T) := Nonempty (v.FundedCutRows x.h x.w size π.symm raw s.1 s.2 unitCost)
  exact Eq.mpr (congrArg priced transferred) paid

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
