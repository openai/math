import OAI.Hierarchy.ProtocolRAMCoreRouteImage
import OAI.Hierarchy.ProtocolRAMBoughtCataloguePricedFrame

namespace OAI
/-! # The genuine four settlement hop sources across the paid calendar -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreRoute
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ReportSockets BoughtSockets CatalogueRows
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {z W k attempts R K H n count r edges q goods N : ℕ} {S : PurchaseSampler}

theorem Seen.frame {order : Fin R≃Edges S z (2^W) k} {M : ℕ} {groups : Fin K≃AllGroups z (2^W)}
    {packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) H}
    {v : Directory attempts} {depth : ℕ} {π : Equiv.Perm (Fin (2^z))} {m out : Boot.Tape z (2^W)}
    (seen : Seen order M groups packed v depth π m)
    (word : stop S z W k attempts depth K packed.groups H R<2^Native.wordBits z (2^W) Native.copies)
    (keep : ∀a< stop S z W k attempts depth K packed.groups H R,out a=m a) :
    Seen order M groups packed v depth π out := by
  have top : directoryBase S z W k attempts depth K packed.groups H R≤ stop S z W k attempts depth K packed.groups H R :=
    Nat.le_add_right ..
  exact ⟨seen.board.frame (top.trans_lt word) (fun a hi=>keep a (hi.trans_le top)),seen.padded.frame (fun a _ hi=>keep a hi)⟩

theorem Seen.priced_run {order : Fin R≃Edges S z (2^W) k} {M : ℕ} {groups : Fin K≃AllGroups z (2^W)}
    {packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) H}
    {v : Directory attempts} {depth : ℕ} {π : Equiv.Perm (Fin (2^z))} {mid : Boot.Tape z (2^W)}
    (seen : Seen order M groups packed v depth π mid) (c : Mesh) (finish : ℝ) (prices : PhasePrice) (arena : Arena)
    (shape F : Attempt→Format z (2^W) k q goods) (initial width cap : ℕ) (f : Sink r edges)
    (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
    (placement : ∀a,arena.base c (.attempt a)≤ (F a).market.failures.base ∧
      arena.base c (.attempt a)≤ (F a).market.shelf.firstBase ∧ arena.base c (.attempt a)≤ (F a).testsStart)
    (room : let limit := stop S z W k attempts depth K packed.groups H R
      limit≤ arena.first ∧ limit<2^Native.wordBits z (2^W) Native.copies) :
    let C := pricedInstalled c finish prices F (feedColumns (N:=N) c arena shape initial width cap) f idBase role ids
    mounted C (events c) mid → Seen order M groups packed v depth π (run C (events c) mid) := by
  intro C mounted
  apply seen.frame room.2
  intro x below
  apply run_outside C (events c) mid x mounted
  intro e _
  have floor : arena.first≤ arena.base c e := Nat.le_add_right ..
  exact (priced_event_floor_with (N:=N) c finish prices arena shape F initial width cap f idBase role ids
    placement e x ((below.trans_le room.1).trans_le floor)).2

theorem Seen.priced_source {order : Fin R≃Edges S z (2^W) k} {M : ℕ} {groups : Fin K≃AllGroups z (2^W)}
    {packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) H}
    {v : Directory attempts} {depth : ℕ} {π : Equiv.Perm (Fin (2^z))} {mid : Boot.Tape z (2^W)}
    (seen : Seen order M groups packed v depth π mid) (c : Mesh) (finish : ℝ) (prices : PhasePrice) (arena : Arena)
    (shape F : Attempt→Format z (2^W) k q goods) (initial width cap : ℕ) (f : Sink r edges)
    (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr) (flag src : ℕ) (slices : List PaidWidths.Slice)
    (arch : ReserveUse.Archive) (reserve : ℕ) (site : Fin n→Fin count) (debit : Fin n→ℕ)
    (placement : ∀a,arena.base c (.attempt a)≤ (F a).market.failures.base ∧
      arena.base c (.attempt a)≤ (F a).market.shelf.firstBase ∧ arena.base c (.attempt a)≤ (F a).testsStart)
    (sources : ∀s∈slices,s.Fits f.banks.width edges src (Native.wordBits z (2^W) Native.copies))
    (room : let lim := stop S z W k attempts depth K packed.groups H R
      lim≤ arena.first ∧ lim<2^Native.wordBits z (2^W) Native.copies ∧ lim≤ flag ∧ lim≤ f.banks.width.base ∧
      lim≤ f.banks.reserved.base ∧ lim≤ f.banks.used.base ∧ lim≤ arch.scratch) :
    let C := pricedInstalled c finish prices F (feedColumns (N:=N) c arena shape initial width cap) f idBase role ids
    mounted C (events C.mesh) mid →
      Seen order M groups packed v depth π (paidSource C flag f src slices arch reserve site debit mid) := by
  intro C ready
  refine seen.frame room.2.1 (CoreCatalogue.paid_retains C flag f src slices arch reserve site debit ready ?_ sources room.2.2)
  intro x below e _
  have floor : arena.first≤ arena.base c e := Nat.le_add_right ..
  exact (priced_event_floor_with (N:=N) c finish prices arena shape F initial width cap f idBase role ids
    placement e x ((below.trans_le room.1).trans_le floor)).2

end Hierarchy.ProtocolRAM.Calendar.CoreRoute
end

end OAI
