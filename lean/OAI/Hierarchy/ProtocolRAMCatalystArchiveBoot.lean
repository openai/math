import OAI.Hierarchy.ProtocolRAMCatalystBootDirectory
import OAI.Hierarchy.ProtocolRAMCatalystLayoutTypes
import OAI.Hierarchy.ProtocolRAMCatalystArchiveDirectory
import OAI.Hierarchy.ProtocolRAMCalendarFeedBoot

namespace OAI
/-! # Retention of the original permutation and the historical reserve directory -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive

open Calendar Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseFrozen PurchaseStage
open ThreeFlat.RAM
open scoped Fin.CommRing Classical BigOperators

variable {z d k jobs n size : ℕ}

/-- The placed priced calendar protects the physical prefix below its first
event slab. Each bound here comes from the three actual purchase-board anchors. -/
theorem priced_kept {q goods r edges N : ℕ} (v : Fin jobs→Market z d k) (layout : Boot.Layout v size)
    (hd : 1≤d) (π : Equiv.Perm (Fin (2^z))) (a : ReserveUse.Archive)
    (id amt : Fin n→ℕ) (raw : Boot.Tape z d) (c : Mesh) (s : ℝ) (prices : PhasePrice)
    (arena : Arena) (F : Attempt→Format z d k q goods) (initial width cap : ℕ)
    (sink : Sink r edges) (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
    (flag : ℕ) (room : BootRoom v size a n arena.first flag)
    (order : ∀j,arena.base c (.attempt j)≤(F j).market.failures.base ∧
      arena.base c (.attempt j)≤(F j).market.shelf.firstBase ∧ arena.base c (.attempt j)≤(F j).testsStart) :
    let C:=pricedInstalled c s prices F (feedColumns (N:=N) c arena F initial width cap) sink idBase role ids
    let boot:=Boot.booted v size (header π a id amt raw)
    mounted C (events c) boot →
    ∀ u,u<2*n → checkedOut C flag boot (a.kind.base+u)=mount a id amt raw (a.kind.base+u) ∧
      checkedOut C flag boot (a.pointer.base+u)=mount a id amt raw (a.pointer.base+u) := by
  intro C boot active
  exact checked_kept v layout hd π a id amt raw C arena flag room
    (fun e x before => (priced_event_floor_for (N:=N) c s prices arena F initial width cap
      sink idBase role ids order e x before).1) active

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
