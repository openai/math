import OAI.Hierarchy.ProtocolRAMTurnSettlementBanks
import OAI.Hierarchy.TaggedWireNativeOrder

namespace OAI
/-! # The physical rank labels are the loads of the committed matrix report -/
namespace Hierarchy.ProtocolRAM.CatalystArchive.TerminalLayout
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe Calendar Calendar.CatalogueRows RouteSettlement WireTelescope
open scoped Fin.CommRing Classical

variable {w r K : ℕ} {I J : Type} [Fintype I] [Fintype J]
variable (bits : ℕ) (cat : Board) (stock owners : Bank)
    (B : SettledMatrix.Layout K cat.rows I J)
    (enum : Fin r≃RouteOccurrence B.core B.center) (ci : I→ℕ) (cj : J→ℕ)
local notation "b" => settlement bits stock
local notation "S" => cat.sink r b (source bits) (table bits) (destination bits) owners

theorem turn_width (m : Memory w) (fixed : Fin cat.rows→ℕ)
    (stockFits : stock.base+stock.size≤2^bits) (rowsFit : cat.rows≤2^bits) :
    let after:=(S).output m enum ci cj
    B.nativeWidth enum fixed (fun i=>actual (b).stock after (ci i))
      (fun j=>actual (b).reserved after (cj j)) (fun j=>actual (b).used after (cj j)) =
    B.nativeWidth enum fixed (fun i=>actual (b).stock m (ci i))
      (fun j=>actual (b).reserved m (cj j)) (fun j=>actual (b).used m (cj j)) := by
  intro after
  have kept (c : Bank) (hc : c∈[(b).index,(b).kind,(b).stock,(b).reserved,(b).used]) (a : ℕ) :
      actual c after a=actual c m a :=
    congrArg Fin.val (turn_read bits cat stock owners enum ci cj m c hc stockFits rowsFit (a:Word w))
  rw [funext (fun i=>kept (b).stock (by simp) (ci i)),
    funext (fun j=>kept (b).reserved (by simp) (cj j)),funext (fun j=>kept (b).used (by simp) (cj j))]

end Hierarchy.ProtocolRAM.CatalystArchive.TerminalLayout

end OAI
