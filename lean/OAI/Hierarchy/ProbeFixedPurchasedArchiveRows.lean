import OAI.Hierarchy.ProbeFixedFailureWords
import OAI.Hierarchy.ProbeRetainedLive
import OAI.Hierarchy.ProbeStripDirectory

namespace OAI
/-! # Immutable path and retained-flag reads across an actual purchased-mode row -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StripDirectory PurchaseFrozen PurchaseStage
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "bs" => v.nativeBoards P z width
variable (p₀ h j t : ℕ) (entry : Memory (wordBits z (2^v.W) copies)) (perm : Equiv.Perm (Fin (2^z)))
local notation "ev" => Attempt.inner p₀ h j t
local notation "sh" => ((bs).outer p₀ h).market.shelf
local notation "S" => (bs).sampler
local notation "h₀" => stratumHeader z (2^v.W) k (S).degree v.depth ((bs).stratumHeader p₀ h)
local notation "pre" => (guard C ev).apply entry
local notation "checked" => postSnapshot ((C).layout ev) (repair C ev) (prepared C ev entry)
local notation "stage" => v.stage P z width r banks src tab dst owners ev entry
local notation "tiles[" m "]" => (∀ key : Key z (2^v.W) k,ProtocolRAMPurchaseGateColumns.TileRows
  ((sh).L S v.depth key).source (Shelf.pathRows S perm v.depth key) m)
local notation "flags" => flagBank sh S z (2^v.W) k v.depth

structure PurchasedArchiveRows where
  stock : ℕ
  phase : PhasePrice
  heat : ℝ
  kind : ℕ
  frozen : Memory W
  preHeader : (h₀).Loaded pre
  checkedHeader : (h₀).Loaded checked
  stageHeader : (h₀).Loaded stage
  preTiles : tiles[pre]
  checkedTiles : tiles[checked]
  stageTiles : tiles[stage]
  stageFlags : StoredFlags {sh with stockBase:=stock} S perm v.depth phase heat kind frozen stage k
  flagRead : ∀i : Fin (h₀).count,(flags).read stage (i.val:Word W)=(flags).read pre (i.val:Word W)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
