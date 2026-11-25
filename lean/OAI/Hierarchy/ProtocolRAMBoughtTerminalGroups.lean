import OAI.Hierarchy.ProtocolRAMBoughtEndpointWords
import OAI.Hierarchy.ProtocolRAMCalendarBoot
import OAI.Hierarchy.ProtocolRAMCalendarFeedLifetime

namespace OAI
/-! # Canonical mixed-radix group words in the final observed geometry -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseCT PurchaseFrozen BoughtSockets
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
variable {z d k jobs q goods N r edges : ℕ}

theorem Boot.numbered (v : Fin jobs→Market z d k) {size : ℕ} (layout : Boot.Layout v size) (hd : 1≤d)
    (π : Equiv.Perm (Fin (2^z))) (words : Boot.Tape z d)
    (authentic : ∀i : Fin (2^z),words i.val=((π i).val:Word _)) :
    numberLoaded PurchaseCT.groupNumber π (Boot.booted v size words) :=
  numbered_after π _ (Boot.subdivision v layout hd π words authentic).2

theorem priced_numbered_terminal (c : Mesh) (finish : ℝ) (prices : PhasePrice) (arena : Arena)
    (F : Attempt→Format z d k q goods) (initial width cap : ℕ) (sink : Sink r edges) (idBase : ℕ)
    (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
    (order : ∀a,arena.base c (.attempt a)≤(F a).market.failures.base ∧
      arena.base c (.attempt a)≤(F a).market.shelf.firstBase ∧ arena.base c (.attempt a)≤(F a).testsStart)
    (geoBefore : heapEnd z d Native.copies≤arena.first) (v : Fin jobs→Market z d k) {size : ℕ}
    (layout : Boot.Layout v size) (hd : 1≤d) (π : Equiv.Perm (Fin (2^z))) (words : Boot.Tape z d)
    (authentic : ∀i : Fin (2^z),words i.val=((π i).val:Word _)) :
    let C:=pricedInstalled c finish prices F (feedColumns (N:=N) c arena F initial width cap) sink idBase role ids
    let mem:=Boot.booted v size words
    mounted C (events c) mem → numberLoaded PurchaseCT.groupNumber π (run C (events c) mem) := by
  intro C mem mountedAll
  apply numbered_of_frame _ π mem _ (Boot.numbered v layout hd π words authentic)
  intro a low
  apply run_frame C _ mem a mountedAll
  intro e _
  exact (priced_event_floor_for (N:=N) c finish prices arena F initial width cap sink idBase role ids order e a
    (low.trans_le (geoBefore.trans (Nat.le_add_right ..)))).1

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
