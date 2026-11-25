import OAI.Hierarchy.ProtocolRAMCalendarPaidReporter
import Mathlib.Data.List.Count

namespace OAI
/-! # The chronological reporter's returned physical words on the original catalogue -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage.Native
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing

theorem load_at_original {E I : Type*} [DecidableEq E] [Fintype I] {edges : ℕ}
    (ord : E↪Fin edges) (walk : I→List E) (bits : I→ℕ) (e:E) :
    routeLoad (fun i=>(walk i).map ord) bits (ord e)=routeLoad walk bits e := by
  unfold routeLoad
  apply Finset.sum_congr rfl
  intro i _
  rw [List.count_map_of_injective (walk i) ord ord.injective e]

variable {E I J : Type*} [DecidableEq E] [Fintype I] [Fintype J] {W q d r edges n count : ℕ}
variable (ord : E↪Fin edges) (path : I→List E) (central : J→List E)
local notation "core" => fun i=>(path i).map ord
local notation "centers" => fun j=>(central j).map ord

theorem paidReporter_original (C : Chart W q d) (flag : ℕ) (f : Sink r edges) (src : ℕ)
    (ss : List PaidWidths.Slice) (a : ReserveUse.Archive) (reserve : ℕ)
    (site : Fin n→Fin count) (debit : Fin n→ℕ) (enum : Fin r≃RouteOccurrence core centers)
    (ci : I→ℕ) (cj : J→ℕ) (m : Memory W)
    (fits : ∀s∈ss,s.Fits f.banks.width edges src W) (width : edges≤f.banks.width.size) (countFit : edges≤2^W)
    (outside : f.banks.width.base+edges≤f.banks.reserved.base ∧ f.banks.width.base+edges≤f.banks.used.base ∧
      f.banks.width.base+edges≤a.scratch) (source : f.banks.width.base+edges≤f.source)
    (e : E)
    (room : let x:=checkedOut C flag m
      let y:=paidSource C flag f src ss a reserve site debit m
      PaidWidths.total ss x (ord e)+(routeLoad path (fun i=>RouteSettlement.actual f.banks.stock y (ci i)) e+
        routeLoad central (fun j=>RouteSettlement.actual f.banks.reserved y (cj j)-RouteSettlement.actual f.banks.used y (cj j)) e)<2^W) :
    let x:=checkedOut C flag m
    let y:=paidSource C flag f src ss a reserve site debit m
    (f.terminalRows y enum ci cj (ord e)).width=PaidWidths.total ss x (ord e)+
      routeLoad path (fun i=>RouteSettlement.actual f.banks.stock y (ci i)) e+
      routeLoad central (fun j=>RouteSettlement.actual f.banks.reserved y (cj j)-RouteSettlement.actual f.banks.used y (cj j)) e := by
  apply (paidReporter_width C flag f src ss a reserve site debit enum ci cj m (ord e) fits width countFit outside source
    (by simpa only [load_at_original] using room)).trans
  simp only [load_at_original]

end Hierarchy.ProtocolRAM.Calendar

end
end OAI
