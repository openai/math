import OAI.Hierarchy.ProtocolRAMBoughtCataloguePaid
import OAI.Hierarchy.ProtocolRAMCalendarFeedLifetime

namespace OAI
/-! # Paid public directories on the installed arena's actual event order -/
noncomputable section
namespace Hierarchy.ProtocolRAM.BoughtSockets.Public
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ReportSockets PurchaseCT Calendar
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {h W k attempts R K H n count r edges q goods N : ℕ} {S : PurchaseSampler}

theorem Readback.priced_run {order : Fin R≃Edges S h (2^W) k} {M : ℕ} {groups : Fin K≃AllGroups h (2^W)}
    {packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved h W (copies k attempts)) H}
    {v : Directory attempts} {depth : ℕ} {π : Equiv.Perm (Fin (2^h))} {mid : Boot.Tape h (2^W)}
    (seen : Readback order M groups packed v depth π mid) (c : Mesh) (finish : ℝ) (prices : PhasePrice) (arena : Arena)
    (shape F : Attempt→Format h (2^W) k q goods) (initial width cap : ℕ) (f : Sink r edges)
    (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
    (placement : ∀a,arena.base c (.attempt a)≤ (F a).market.failures.base ∧
      arena.base c (.attempt a)≤ (F a).market.shelf.firstBase ∧ arena.base c (.attempt a)≤ (F a).testsStart)
    (room : let limit := endAddress S (CoreCatalogue.top h W K packed.groups H R) h W k attempts depth
      limit≤ arena.first ∧ limit<2^Native.wordBits h (2^W) Native.copies) :
    let C := pricedInstalled c finish prices F (feedColumns (N:=N) c arena shape initial width cap) f idBase role ids
    mounted C (events c) mid → Readback order M groups packed v depth π (run C (events c) mid) := by
  intro C mounted
  apply seen.frame room.2
  intro x below
  apply run_outside C (events c) mid x mounted
  intro e _
  have floor : arena.first≤ arena.base c e := Nat.le_add_right ..
  exact (priced_event_floor_with (N:=N) c finish prices arena shape F initial width cap f idBase role ids
    placement e x ((below.trans_le room.1).trans_le floor)).2

theorem Readback.priced_source {order : Fin R≃Edges S h (2^W) k} {M : ℕ} {groups : Fin K≃AllGroups h (2^W)}
    {packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved h W (copies k attempts)) H}
    {v : Directory attempts} {depth : ℕ} {π : Equiv.Perm (Fin (2^h))} {mid : Boot.Tape h (2^W)}
    (seen : Readback order M groups packed v depth π mid)
    (c : Mesh) (finish : ℝ) (prices : PhasePrice) (arena : Arena)
    (shape F : Attempt→Format h (2^W) k q goods) (initial width cap : ℕ) (f : Sink r edges)
    (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr) (flag src : ℕ) (slices : List PaidWidths.Slice)
    (arch : ReserveUse.Archive) (reserve : ℕ) (site : Fin n→Fin count) (debit : Fin n→ℕ)
    (placement : ∀ a,arena.base c (.attempt a)≤ (F a).market.failures.base ∧
      arena.base c (.attempt a)≤ (F a).market.shelf.firstBase ∧ arena.base c (.attempt a)≤ (F a).testsStart)
    (sources : ∀s∈slices,s.Fits f.banks.width edges src (Native.wordBits h (2^W) Native.copies))
    (room : let limit := endAddress S (CoreCatalogue.top h W K packed.groups H R) h W k attempts depth
      limit≤ arena.first ∧ limit<2^Native.wordBits h (2^W) Native.copies ∧ limit≤ flag ∧ limit≤ f.banks.width.base ∧
      limit≤ f.banks.reserved.base ∧ limit≤ f.banks.used.base ∧ limit≤ arch.scratch) :
    let C := pricedInstalled c finish prices F (feedColumns (N:=N) c arena shape initial width cap) f idBase role ids
    mounted C (events C.mesh) mid →
      Readback order M groups packed v depth π (paidSource C flag f src slices arch reserve site debit mid) := by
  intro C ready
  apply seen.paid_source C flag f src slices arch reserve site debit ready sources room.2
  intro x below e _
  have floor : arena.first≤ arena.base c e := Nat.le_add_right ..
  exact (priced_event_floor_with (N:=N) c finish prices arena shape F initial width cap f idBase role ids
    placement e x ((below.trans_le room.1).trans_le floor)).2

end Hierarchy.ProtocolRAM.BoughtSockets.Public
end

end OAI
