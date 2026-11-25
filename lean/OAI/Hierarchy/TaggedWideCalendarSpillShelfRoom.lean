import OAI.Hierarchy.TaggedWideCalendarControlRoom

namespace OAI
/-! # Address bounds of the dated sparse turn shelf in the selected native gate -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat.SignedSites
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard Tagged
open WideStack TaggedPrune TaggedShorterBudget TaggedShorterSupergroups WireTelescope.PassMatrix WideCPU Filter
open scoped Classical
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A δ ξ : ℝ} {u : ℝ→ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short unitCost : ℕ) {x : WideParent κ A}
local notation "g" => v.wideDated x.h x.w ell unitCost
local notation "S" => v.wideInstalledSize x m ell unitCost g
local notation "root" => v.wideInstalledRoot x
local notation "L" => v.wideInstalledLayout x m ell short u δ ξ unitCost g
local notation "U" => (L).pruneScratch+(L).pruneRows+1
local notation "Z" => v.wideSpillDates x.h x.w ell unitCost v.maxBits U
local notation "rank" => v.wideSpillRankEnd x.h x.w v.maxBits U
local notation "endAll" => v.wideCorrectedSpillEnd x.h x.w ell unitCost v.maxBits root S ((g).romEnd root) ((g).workEnd S) U


local notation "old" => (Z).preClip S rank
local notation "now" => fun j=>(g).roleStart S j.succ
local notation "left" => fun j=>(Z).dateRole rank j 1
local notation "right" => fun j=>(Z).dateRole rank j 2
local notation "turns" j => v.wideSpillTurnPage x.h x.w v.maxBits root ((g).romEnd root)
  ((g).workEnd S) U ((Z).endAt rank) old now left right j
local notation "K" => siteLast x.h (2^v.W) k+1
local notation "seats" => WordSeats.room (k:=k) (attempts:=v.wideJobs) v.sampler

theorem calendar_spill_shelf {N : ℕ} (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x)
    (j : Fin (events v.mesh).length) (s : Fin K) (t : Fin seats) (f : Fin 5) :
    WireTelescope.TurnShelf.addr (turns j).base s t f<(v.wideFullGates x m ell short u δ ξ unitCost cpu.room).2.u := by
  let P:=turns j
  have finish : P.stop≤endAll :=
    (v.wide_spill_turn_end x.h x.w v.maxBits root ((g).romEnd root) ((g).workEnd S) U
      ((Z).endAt rank) old now left right j).trans (Nat.add_le_add_left
        (Nat.mul_le_mul_right _ j.isLt) _)
  have area : P.base+5*(K*seats)≤P.stop := by
    exact P.window.bounds.2.2.2.1.trans ((Nat.le_add_right _ _).trans (Nat.le_of_lt P.window.bounds.2.2.2.2))
  exact (v.wideFullGates x m ell short u δ ξ unitCost cpu.room).2.shelf_inside _ s t f
    (area.trans (finish.trans (le_max_right ..)))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat.SignedSites
end

end OAI
