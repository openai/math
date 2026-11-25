import OAI.Hierarchy.ProbeFixedFailureWords
import OAI.Hierarchy.ProtocolRAMCatalystDateLive
import OAI.Hierarchy.ProtocolRAMPurchaseMarketBelow

namespace OAI
/-! # The real fixed-slab tests, failure mask and label ranges at an outer or purchased date -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StockCommit
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ) (banks : RouteSettlement.Banks)
  (src tab dst : ℕ) (owners : Bank)
local notation "w" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "mkt" => (fun a=>(f a).atTime v.mesh v.finish (v.basePhase width) a)
local notation "s" => v.sized (v.seed P z width) width
local notation "room" => v.slab (v.seed P z width) P width
local notation "arena" => v.privateArena P z width
local notation "cut" => (⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊)

/-- The radius and tariff of the generated test are uniform over all dates. -/
theorem catalyst_test_cut (a : Attempt) : (mkt a).failures.cut=cut := by
  cases a <;> rfl

set_option cleanup.letToHave false in
set_option maxHeartbeats 2000000 in
private theorem catalyst_mask_layout (a : Attempt) :
    let ff:=f a
    let base:=(arena).base v.mesh (.attempt a)
    ff.market.rows=Slab.rows s ∧ ff.market.failures.rows=ff.market.rows ∧
      ff.market.failures.base=base+Slab.selectorSpan s ∧
      ff.market.shelf.firstBase=Slab.first room s base ∧
      ff.indexBits=z+Slab.rowFactor s ∧ ff.market.failures.rowBits=z+Slab.rowFactor s := by
  dsimp only
  simp only [Slab.rows_eq]
  cases a <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem mask_before_outputs (tests : AttemptGate.TestBoard) (first stop : ℕ) (h : stop ≤ first) :
    stop ≤ (PostLayout.placeTests tests first).excess.out ∧
    stop ≤ (PostLayout.placeTests tests first).payload.out ∧
    stop ≤ (PostLayout.placeTests tests first).discrepancy.out := by
  dsimp only [PostLayout.placeTests]
  omega

private theorem mask_end_before_verdict (first bits rows col : ℕ) :
    first+rows≤PostLayout.column first bits rows col+1 := by
  calc
    first+rows ≤ first+2^bits+rows := Nat.add_le_add_right (Nat.le_add_right first _) rows
    _ ≤ first+2^bits+rows+2 := Nat.le_add_right ..
    _ ≤ PostLayout.column first bits rows col := Nat.le_add_right ..
    _ ≤ _ := Nat.le_add_right ..

set_option cleanup.letToHave false in
set_option maxHeartbeats 1200000 in
/-- The failure bank, threshold, and test banks all belong to the current slab. -/
theorem catalystMaskBounds (a : Attempt) (threshold : cut<2^w) :
    (mkt a).MaskBounds (repair C a) (f a).pricedArea (g a) := by
  let ff:=f a
  let s₀:=s
  let base:=(arena).base v.mesh (.attempt a)
  obtain ⟨rowCount,failedRows,failBase,firstBase,indexBits,failIndex⟩ :=
    catalyst_mask_layout v P z width a
  have n := Slab.row_room s₀
  have capacity : ff.market.rows≤2^ff.indexBits := by rw [rowCount,indexBits];exact n
  have prefixRoom : ff.market.failures.base+ff.market.rows≤ff.market.shelf.firstBase := by
    rw [rowCount,failBase,firstBase]
    change base+Slab.selectorSpan s₀+Slab.rows s₀≤base+Slab.selectorSpan s₀+2^(z+Slab.rowFactor s₀)+_
    exact (Nat.add_le_add_left n _).trans (Nat.le_add_right ..)
  have flagRoom : ff.market.failures.base+ff.market.rows≤ff.market.flags :=
    prefixRoom.trans (ff.market.shelf.first_le_flags ff.market.sampler z (2^v.W) k ff.market.depth)
  refine ⟨failedRows.symm.le,?_,capacity,?_,?_,?_,?_,?_⟩
  · change ff.market.rows≤2^ff.market.failures.rowBits
    rw [rowCount,failIndex];exact n
  · rw [v.catalyst_test_cut P z width a]
    exact threshold
  · let tests := (testedBoard ff.market.failures ff.batch).tests
    change ff.market.failures.base+ff.market.rows≤(PostLayout.placeTests tests ff.testsStart).excess.out ∧
      ff.market.failures.base+ff.market.rows≤(PostLayout.placeTests tests ff.testsStart).payload.out ∧
      ff.market.failures.base+ff.market.rows≤(PostLayout.placeTests tests ff.testsStart).discrepancy.out
    exact mask_before_outputs tests ff.testsStart _ (flagRoom.trans (Nat.le_add_right ..))
  · exact priced_mask_space v.mesh v.finish (v.basePhase width) f
      (feedColumns (N:=CoreBoard.Stages z (2^v.W)) v.mesh arena f P.joint.initial width v.keepLimit)
      (P.catalogue.sink r banks src tab dst owners) P.catalogue.idBase
      (fun t=>(StripChart.header F (v.nativeBoards P z width) t).fieldTerm)
      (StripChart.id F (v.nativeBoards P z width) P.catalogue) a capacity
  · change ff.maskStart+ff.market.rows≤PostLayout.column ff.maskStart ff.indexBits ff.market.rows (PostLayout.columnsCount ff.checkedBoard)+1
    exact mask_end_before_verdict _ _ _ _
  · exact Nat.le_add_right ..

/-- An explicit lower bound on the height, determined by the fixed tariff alone, suffices
for every installed date, every choice of public addresses and every execution. -/
theorem catalyst_cut_at_height (calibrated : cut≤z) : cut<2^w := by
  have hz : z≤w := Nat.le_add_left ..
  exact (calibrated.trans_lt (Nat.lt_two_pow_self)).trans_le (Nat.pow_le_pow_right (by decide : 0<2) hz)

theorem catalystMaskBounds_at_height (calibrated : cut≤z) (a : Attempt) :
    (mkt a).MaskBounds (repair C a) (f a).pricedArea (g a) :=
  v.catalystMaskBounds P z width r banks src tab dst owners a (v.catalyst_cut_at_height z calibrated)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
