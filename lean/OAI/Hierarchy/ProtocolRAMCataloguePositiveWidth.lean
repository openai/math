import OAI.Hierarchy.ProtocolRAMCataloguePaidSupport
import OAI.Hierarchy.ProtocolRAMCatalogueRows

namespace OAI
/-! # Active acquired output rows have a positive physical birth flag -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe
open ThreeFlat.RAM
open scoped Fin.CommRing

variable {W q d r n count : ℕ} {I J : Type*} [Fintype I] [Fintype J]

theorem Board.positive_bought (b : Board) (C : Chart W q d) (flag : ℕ) (f : Sink r b.rows)
    (src : ℕ) (ss : List PaidWidths.Slice) (arch : ReserveUse.Archive) (reserve : ℕ)
    (site : Fin n→Fin count) (debit : Fin n→ℕ) (core : I→List (Fin b.coreRows)) (center : J→List (Fin b.coreRows))
    (enum : Fin r≃RouteOccurrence (fun i=>(core i).map b.coreIndex) (fun j=>(center j).map b.coreIndex))
    (ci : I→ℕ) (cj : J→ℕ) (m : Memory W) (j : Fin b.boughtRows)
    (fits : ∀s∈ss,s.Fits f.banks.width b.rows src W) (width : b.rows≤f.banks.width.size) (countFit : b.rows≤2^W)
    (outside : f.banks.width.base+b.rows≤f.banks.reserved.base ∧ f.banks.width.base+b.rows≤f.banks.used.base ∧
      f.banks.width.base+b.rows≤arch.scratch) (source : f.banks.width.base+b.rows≤f.source)
    (room : PaidWidths.total ss (checkedOut C flag m) (b.boughtIndex j)<2^W)
    (support : ∀ s∈ss,b.Supported s (checkedOut C flag m))
    (flagFits : b.bought.flag.Fits W f.banks.width.base) :
    let final := paidSource C flag f src ss arch reserve site debit m
    0<(f.terminalRows final enum ci cj (b.boughtIndex j)).width →
      b.bought.flag.eval final (j.val:Word W)≠0 := by
  intro final positive
  let old := checkedOut C flag m
  have c0 := b.core_route_disjoint core (fun i=>RouteSettlement.actual f.banks.stock final (ci i)) j
  have c1 := b.core_route_disjoint center (fun i=>RouteSettlement.actual f.banks.reserved final (cj i)-
    RouteSettlement.actual f.banks.used final (cj i)) j
  have ledger := paidReporter_width C flag f src ss arch reserve site debit enum ci cj m (b.boughtIndex j) fits
    width countFit outside source (by
      change PaidWidths.total ss old (b.boughtIndex j) +
        (routeLoad (fun i=>(core i).map b.coreIndex) (fun i=>RouteSettlement.actual f.banks.stock final (ci i)) (b.boughtIndex j) +
         routeLoad (fun i=>(center i).map b.coreIndex) (fun i=>RouteSettlement.actual f.banks.reserved final (cj i)-
           RouteSettlement.actual f.banks.used final (cj i)) (b.boughtIndex j))<2^W
      simpa only [c0,c1,Nat.add_zero] using room)
  change (f.terminalRows final enum ci cj (b.boughtIndex j)).width=PaidWidths.total ss old (b.boughtIndex j)+
    routeLoad (fun i=>(core i).map b.coreIndex) (fun i=>RouteSettlement.actual f.banks.stock final (ci i)) (b.boughtIndex j)+
    routeLoad (fun i=>(center i).map b.coreIndex) (fun i=>RouteSettlement.actual f.banks.reserved final (cj i)-
      RouteSettlement.actual f.banks.used final (cj i)) (b.boughtIndex j) at ledger
  rw [c0,c1] at ledger
  have same : b.bought.flag.eval final (j.val:Word W)=b.bought.flag.eval old (j.val:Word W) := by
    apply eval_below _ _ _ _ flagFits
    intro a prev
    change ReserveUse.output arch f.banks reserve site debit (PaidWidths.output f.banks.width b.rows src ss old) a=old a
    rw [ReserveUse.frame _ _ _ _ _ _ a (.inl (by omega)) (.inl (by omega)) (.inl (by omega))]
    exact PaidWidths.frame _ _ _ _ _ a fits prev
  intro off
  have zero := b.no_dormant_load ss old j support (same.symm.trans off)
  omega

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
