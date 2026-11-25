import OAI.Hierarchy.ProbeFixedCatalystBirthBefore
import OAI.Hierarchy.ProbeFixedWideSettlement

namespace OAI
/-! # Prefix-causal purchase receipt at the original signed boot -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart StripDirectory PurchaseFrozen
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "B" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "w" => Native.wordBits h D Native.copies
local notation "r" => Fintype.card (Slots h D k)
local notation "cnt" => rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger B v.mesh (P).catalogue (P).routes F A))

def wide_purchased_before (size : ℕ) (extent : (A).endAddress v.mesh ≤ size)
    (stock : Bank) (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (o : Orders h D k) (raw : Boot.Tape h D)
    (phase trial slice inner : ℕ) (prior tail : List Event)
    (split : events v.mesh=prior++Event.attempt (.inner phase trial slice inner)::tail)
    (past : Calendar.mounted (v.wideSignedChart h width stock) prior
      (v.wideSignedMidAt h width size stock M π o raw))
    (word : (A).endAddress v.mesh<2^w) :
    PurchasedBirth ((B).outer phase trial).market.shelf (B).sampler π v.depth ((B).stratumHeader phase trial)
      (run (v.wideSignedChart h width stock) prior (v.wideSignedMidAt h width size stock M π o raw)) k := by
  let mem:=v.wideSignedMidAt h width size stock M π o raw
  let bits:=v.wideSignedPage h width stock
  let owners:=sinkBank (v.catalystStaticStart P h width) cnt r (P).catalogue.rows
  let keys:=BoughtSockets.Public.keyHead v.sampler (P).routes.column h v.W k v.depth
  have pfx:=v.wideGeometryPrefix h width
  have core:=pfx.2.2
  have first:=v.catalyst_initial_le_first P h width
  have edges:=(BoughtSockets.Public.borders v.sampler (P).routes.column h v.W k v.wideJobs v.depth).2
  have room : keys.stop≤(A).first := edges.trans ((Nat.le_add_right ..).trans (core.trans first))
  let receipt:=v.wide_signed_boot_at h width size extent stock M π o raw word
  exact v.catalyst_birth_before P h width r (TerminalLayout.settlement bits stock)
    (TerminalLayout.source bits) (TerminalLayout.table bits) (TerminalLayout.destination bits) owners mem π
    phase trial slice inner prior tail split past receipt.2.1.geometry (pfx.2.1.trans first) room
    receipt.2.2.1.board.rom.keys

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
