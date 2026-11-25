import OAI.Hierarchy.TaggedWireReportAction
import OAI.Hierarchy.ProtocolRAMCalendarPaidReporter

namespace OAI
/-! # Reading the terminal matrix receipt from the native paid reporter -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.MatrixReceipt
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe WireTelescope ProtocolRAMEmit ProtocolRAM ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
variable {S : PurchaseSampler} {h k d w edges r M den W q goods n count : ℕ} {b : Fin k→ℕ}
    {D : TaggedPrune.Layout h w b} {π : Equiv.Perm (Tagged.Row h)} {place : Site h d k→Fin (D.last+1)}
    (B : Mount (S:=S) π place edges) (C : Chart W q goods) (flag : ℕ) (f : Sink r edges) (src : ℕ)
    (ss : List PaidWidths.Slice) (a : ReserveUse.Archive) (reserve : ℕ) (site : Fin n→Fin count)
    (debit : Fin n→ℕ) (enum : Fin r≃RouteOccurrence B.ordinary B.centers)
    (ci : Commodity (Fin (2^h)) (Stages h d) k→ℕ) (cj : Columns h d×Fin k→ℕ) (m : Memory W)

local notation "finalBank" => paidSource C flag f src ss a reserve site debit m
local notation "nativeRows" => Sink.terminalRows f finalBank enum ci cj
local notation "paidWidth" => PaidWidths.total ss (checkedOut C flag m)
local notation "stockWidth" => fun i=>RouteSettlement.actual f.banks.stock finalBank (ci i)
local notation "reserveWidth" => fun j=>RouteSettlement.actual f.banks.reserved finalBank (cj j)
local notation "usedWidth" => fun j=>RouteSettlement.actual f.banks.used finalBank (cj j)

/-- All local gate reads now refer to the same terminal report that the
paid-width seed, finite reserve debit, and two real core directories produced. -/
theorem paid (G : Geometry D M den nativeRows)
    (ends : ∀i : ActiveRows nativeRows,
      (B.actual.tail i.val=(nativeRows i.val).leftSite (G.fits i) ∧ B.actual.head i.val=(nativeRows i.val).rightSite (G.fits i)) ∨
      (B.actual.tail i.val=(nativeRows i.val).rightSite (G.fits i) ∧ B.actual.head i.val=(nativeRows i.val).leftSite (G.fits i)))
    (fits : ∀s∈ss,s.Fits f.banks.width edges src W) (width : edges≤f.banks.width.size)
    (countFit : edges≤2^W)
    (outside : f.banks.width.base+edges≤f.banks.reserved.base ∧ f.banks.width.base+edges≤f.banks.used.base ∧
        f.banks.width.base+edges≤a.scratch) (source : f.banks.width.base+edges≤f.source)
    (room : ∀e,paidWidth e+(routeLoad B.ordinary stockWidth e+
      routeLoad B.centers (fun j=>(reserveWidth) j-(usedWidth) j) e)<2^W) :
    MatrixReceipt B paidWidth stockWidth reserveWidth usedWidth G where
  report e := paidReporter_width C flag f src ss a reserve site debit enum ci cj m e fits width countFit outside source (room e)
  ends := ends

end Hierarchy.ProbeStage.CoreBoard.MatrixReceipt
end

end OAI
