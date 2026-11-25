import OAI.Hierarchy.ProbeFixedPostings
import OAI.Hierarchy.ProtocolRAMCalendarStripSeen

namespace OAI
/-! # The first, committed and chronological stock addresses of the native sampler -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart StripDirectory PurchaseFrozen
open scoped Fin.CommRing Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
local notation "d" => (2^v.W)
local notation "N" => CoreBoard.Stages z d
local notation "A" => v.privateArena P z width
local notation "B" => v.nativeBoards P z width
local notation "fmt" => v.nativeFormats P z width
local notation "W" => wordBits z d copies

theorem market_capacity (a : Attempt) (scheduled : Event.attempt a∈events v.mesh)
    (capacity : (A).endAddress v.mesh<2^W) :
    let m:=(fmt a).atTime v.mesh v.finish (v.basePhase width) a
    m.flags+m.rows<2^W := by
  have tests : (fmt a).testsStart≤(fmt a).maskStart := by unfold Format.maskStart PostLayout.afterTests;omega
  have mask : (fmt a).maskStart≤(fmt a).board.verdict := by
    change _≤PostLayout.column (fmt a).maskStart _ _ _
    exact (((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans
      (Nat.le_add_right _ 2)).trans (Nat.le_add_right _ _)
  change (fmt a).testsStart<2^W
  exact (tests.trans (mask.trans ((Slab.verdict_before _).le.trans
    ((v.attempt_room P z width a).trans ((A).within v.mesh (.attempt a) scheduled))))).trans_lt capacity

/-- The committed output is beyond its price label bank for every format. -/
private theorem label_before_output {n d₀ k₀ q₀ rows : ℕ} (f : Format n d₀ k₀ q₀ rows) :
    f.labelStart ≤ f.pricedArea.output := by
  have source : f.labelStart ≤ f.pricedArea.start := Nat.le_add_right ..
  have direct : f.pricedArea.start ≤ f.pricedArea.direct := Nat.le_add_right ..
  have cost : f.pricedArea.direct ≤ f.pricedArea.broadcast := Nat.le_add_right ..
  have debit : f.pricedArea.broadcast ≤ f.pricedArea.src := Nat.le_add_right ..
  have clip : f.pricedArea.src ≤ f.pricedArea.clip := Nat.le_add_right ..
  have excess : f.pricedArea.clip ≤ f.pricedArea.excess := Nat.le_add_right ..
  exact source.trans (direct.trans (cost.trans (debit.trans (clip.trans (excess.trans (Nat.le_add_right ..))))))

/-- Both initial stock and each real chronological publication are above the heap. -/
theorem previous_stock_floor {n d₀ k₀ q₀ rows initial floor : ℕ} (c : Mesh) (arena : Arena)
    (f : Attempt → Format n d₀ k₀ q₀ rows) (original : floor ≤ initial) (first : floor ≤ arena.first)
    (labels : ∀t, arena.base c (.attempt t) ≤ (f t).labelStart) (e : Event) :
    floor ≤ previousStock c initial (publishedStock c arena f) e := by
  have published (ev : Event) : floor ≤ publishedStock c arena f ev := by
    cases ev with
    | feed b => exact first.trans (Nat.le_add_right ..)
    | attempt t =>
      exact first.trans ((Nat.le_add_right ..).trans ((labels t).trans (label_before_output (f t))))
  simp only [previousStock]
  split
  · exact published _
  · exact original

/-- At the first trial the previous-stock pointer addresses the initial bank. -/
theorem initial_stock_floor {c : Mesh} {arena : Arena} {f : Event → ℕ} {first padded inventory : ℕ}
    (room : inventory+padded ≤ arena.base c (.attempt (.outer 0 0)))
    (pointer : inventory=previousStock c first f (.attempt (.outer 0 0))) : first ≤ arena.first := by
  have old : inventory=first := pointer.trans (by simp [previousStock,position,trialBase])
  have low := (Nat.le_add_right inventory padded).trans room
  simpa only [old,Arena.base,position,trialBase,Nat.zero_mul,Nat.zero_add,Nat.add_zero] using low

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
