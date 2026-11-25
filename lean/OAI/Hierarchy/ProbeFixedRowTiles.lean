import OAI.Hierarchy.ProbeFixedRowPages
import OAI.Hierarchy.ProbePurchasedOccurrence
import OAI.Hierarchy.ProbeFixedStripCounts

namespace OAI
/-! # The guard, audit and commit read the same signed stock slots on the recorded DFS tiles -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StockCommit StripDirectory
open PurchaseFrozen ChainStrip
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (z width : ℕ)
local notation "N" => Stages z (2^v.W)
local notation "Goods" => Commodity (Fin (2^z)) N k
local notation "J" => ChainStrip.Axes v.depth k
local notation "W" => wordBits z (2^v.W) copies
local notation "bs" => v.nativeBoards P z width
local notation "fm" => v.nativeFormats P z width
variable (phase trial slice inner : ℕ)
local notation "ev" => Attempt.inner phase trial slice inner
local notation "sh" => ((bs).outer phase trial).market.shelf
local notation "S" => (bs).sampler
local notation "h₀" => stratumHeader z (2^v.W) k (S).degree v.depth ((bs).stratumHeader phase trial)

theorem purchased_raw_rows : (fm ev).market.rows = (h₀).count := by
  change (fm ev).market.rows =
    PurchaseFrozen.count z (2^v.W) k * PurchaseFrozen.paths z (S).degree v.depth
  exact StripChart.candidate_count F v.mesh (v.privateArena P z width) P.joint.initial bs ev

/-- An affirmative DFS row identifies an actual path at this packed ordinal. -/
def PurchasedLiveRow (π : Equiv.Perm (Fin (2^z))) (j : Fin (fm ev).market.rows) : Prop :=
  ∃ marked : StageAt z (2^v.W) → Fin k × Bool → Finset (Fin (2^z)),
    ∃ path : LiveChains S π v.depth marked, (BoughtLocation.relative path).val = j.val

set_option maxHeartbeats 1200000 in
/-- Recover the retained path from the flag word in the archived purchase memory. -/
theorem purchased_live_row (π : Equiv.Perm (Fin (2^z))) (stock : ℕ) (price : PhasePrice)
    (heat : ℝ) (kind : ℕ) (frozen flagMem : Memory W)
    (flags : StoredFlags {sh with stockBase := stock} S π v.depth price heat kind frozen flagMem k)
    (whole : count z (2^v.W) k * PurchaseFrozen.paths z (S).degree v.depth ≤ 2^W)
    (j : Fin (fm ev).market.rows)
    (active : (flagBank sh S z (2^v.W) k v.depth).read flagMem (j.val : Word W) ≠ 0) :
    v.PurchasedLiveRow P z width phase trial slice inner π j := by
  let dated : Shelf := {sh with stockBase := stock}
  let bank := flagBank sh S z (2^v.W) k v.depth
  have bound : j.val < count z (2^v.W) k * PurchaseFrozen.paths z (S).degree v.depth :=
    j.isLt.trans_eq (v.purchased_raw_rows P z width phase trial slice inner)
  have inBank : j.val < bank.size := bound.trans (ProtocolRAMPurchaseSampler.lt_span _)
  have present : flagMem (dated.flagsBase S z (2^v.W) k v.depth + j.val) ≠ 0 := by
    change flagMem (dated.flagsBase S z (2^v.W) k v.depth + (j.val : Word W).val % bank.size) ≠ 0 at active
    rwa [Fin.val_cast_of_lt (bound.trans_le whole), Nat.mod_eq_of_lt inBank] at active
  let Yes := BoughtLocation.Yes (count z (2^v.W) k * PurchaseFrozen.paths z (S).degree v.depth)
    (dated.flagsBase S z (2^v.W) k v.depth) flagMem
  let yes : Yes := ⟨⟨j.val, bound⟩, present⟩
  let packed := BoughtLocation.packedEquiv («S» := S) (π := π) (depth := v.depth)
    dated price heat kind frozen flagMem flags
  refine ⟨actualMarks dated price heat kind frozen, packed.symm yes, ?_⟩
  change (packed (packed.symm yes)).val.val = yes.val.val
  exact congrArg (fun i : Yes => i.val.val) (packed.apply_symm_apply yes)

set_option maxHeartbeats 1200000 in
/-- Both snapshots read the same signed inventory slots of the retained path. -/
theorem purchased_raw_slots (π : Equiv.Perm (Fin (2^z))) (before after : Memory W)
    (first : (h₀).Loaded before) (second : (h₀).Loaded after)
    (preTiles : ∀ key : Key z (2^v.W) k,ProtocolRAMPurchaseGateColumns.TileRows
      ((sh).L S v.depth key).source (Shelf.pathRows S π v.depth key) before)
    (postTiles : ∀ key : Key z (2^v.W) k,ProtocolRAMPurchaseGateColumns.TileRows
      ((sh).L S v.depth key).source (Shelf.pathRows S π v.depth key) after)
    (keyRoom : count z (2^v.W) k≤2^W) (tileRoom : (v.depth+1)*PurchaseFrozen.paths z (S).degree v.depth≤2^W)
    (j : Fin (fm ev).market.rows) (live : v.PurchasedLiveRow P z width phase trial slice inner π j) :
    ∃ hits : J → Goods, (∀ i,(hits i).elim (fun _=>0) (fun _=>1)=1) ∧
      (∀ i,(allChainSlot (z:=z) (d:=2^v.W) sh S v.depth h₀ i).eval before (j.val:Word W)=
        (PurchaseInventory.slot (hits i):Word W)) ∧
      ∀ i,(allChainSlot (z:=z) (d:=2^v.W) sh S v.depth h₀ i).eval after (j.val:Word W)=
        (PurchaseInventory.slot (hits i):Word W) := by
  obtain ⟨marked, path, row⟩ := live
  refine ⟨stripAddress S π v.depth marked path, fun _ => rfl, ?_, ?_⟩
  · intro i
    simpa only [row] using
      (relative_stock sh ((bs).stratumHeader phase trial) marked path before preTiles first keyRoom tileRoom i)
  · intro i
    simpa only [row] using
      (relative_stock sh ((bs).stratumHeader phase trial) marked path after postTiles second keyRoom tileRoom i)



end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
