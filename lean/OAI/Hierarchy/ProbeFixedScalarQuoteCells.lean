import OAI.Hierarchy.ProbeFixedStockWindow
import OAI.Hierarchy.ProbeFixedPostings
import OAI.Hierarchy.ProbeFixedStripCounts
import OAI.Hierarchy.ProtocolRAMCalendarEconomicPrices

namespace OAI
/-! # The finite stock and phase cells queried by the real strip tests -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StockCommit StripDirectory PurchaseCT
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (z width : ℕ) (bills : Event → WordRows)
local notation "N" => Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => Commodity (Fin (2^z)) N k
local notation "H" => v.publicHeader P z width
local notation "A" => v.nativeAccount P z width bills
local notation "fs" => v.nativeFormats P z width
local notation "g₀" => JointHeader.scores P.joint z N k
local notation "idx[" a "]" => DeadlineROM.index v.mesh a
local notation "page[" a "]" => DeadlineROM.scorePage v.mesh g₀ z N k a
local notation "prices" => DeadlineROM.prices v.mesh v.finish (v.basePhase width)

def dateInTable (c : Mesh) : Attempt → Prop
  | .outer phase _ => phase≤c.inject+c.cool
  | .inner phase _ slice _ => phase≤c.inject+c.cool ∧ slice≤c.reserveSteps

theorem dateInTable_of_event (c : Mesh) (a : Attempt) (event : Event.attempt a∈events c) :
    dateInTable c a := by
  obtain ⟨p,hp,visit⟩ := List.mem_flatMap.mp event
  rcases List.mem_append.mp visit with attempts | boundary
  · obtain ⟨t,_,trial⟩ := List.mem_flatMap.mp attempts
    rcases List.mem_cons.mp trial with outer | reserve
    · cases outer
      exact (List.mem_range.mp hp).le
    · obtain ⟨j,hj,trial⟩ := List.mem_flatMap.mp reserve
      rcases List.mem_append.mp trial with repairs | boundary
      · obtain ⟨b,_,matchEvent⟩ := List.mem_map.mp repairs
        cases matchEvent
        exact ⟨(List.mem_range.mp hp).le,(List.mem_range.mp hj).le⟩
      · simp at boundary
  · simp at boundary

theorem date_time_positive (a : Attempt) (inside : dateInTable v.mesh a) :
    0<time v.mesh v.finish a := by
  have h : 0<(v.finish:ℝ) := by exact_mod_cast v.clock.finish_pos
  cases a with
  | outer p t => exact h.trans_le (v.real_times inside).1
  | inner p t j b => exact (half_pos h).trans_le ((v.real_times inside.1).2 j)

/-- The genuine scalar page and offset page, with stock cells compared to the
physical account on entry. These reads are sufficient at both the guard memory
and the later stock-commit memory. -/
theorem row_quote_cells (a : Attempt) (entry state : Memory W) (date : dateInTable v.mesh a)
    (scalar : (H).scalar.Resident state)
    (scores : GlobalTests.Resident page[a] z N k (prices idx[a]) state)
    (rowsFit : GlobalTests.rows z N k ≤ 2^W)
    (stock : ∀ t : C, state ((fs a).stockSource.old.base+PurchaseInventory.slot t)=entry ((A).stockAt a t))
    (limit : ∀ t : C, (entry ((A).stockAt a t)).val < (g₀).stride) :
    QuoteCells (deadline v.mesh v.finish (v.basePhase width) a) state ((H).scalar.bank idx[a])
      (GlobalTests.offsets page[a]) (fs a).stockSource.old PurchaseInventory.slot PurchaseInventory.lane
      (fun t : C => (entry ((A).stockAt a t)).val) (g₀).stride := by
  let E := PurchaseInventory.slotEquiv z N k
  have row (t : C) : (E t).val=PurchaseInventory.slot t := rfl
  have rowKind (t : C) : (GlobalTests.kind (E t)).val=PurchaseInventory.lane t := by
    dsimp only [GlobalTests.kind]
    rw [show (PurchaseInventory.slotEquiv z N k).symm (E t)=t from E.symm_apply_apply t]
  have slotCap : GlobalTests.rows z N k ≤ (fs a).stockSource.old.size := by
    rw [v.stock_old_size P z width a]
    exact (ProtocolRAMPurchaseSampler.lt_span _).le
  constructor
  · intro t
    have h := scores.off (E t)
    change state ((page[a]).base+((PurchaseInventory.slot t:ℕ):Word W).val % (2^(GlobalTests.bits z N k)))=_
    rw [←row t,Fin.val_cast_of_lt ((E t).isLt.trans_le rowsFit),
      Nat.mod_eq_of_lt ((E t).isLt.trans_le (GlobalTests.mask_room z N k).1)]
    have stride : (page[a]).stride=(g₀).stride := rfl
    simpa only [rowKind,stride] using h
  · intro t
    unfold Bank.read
    rw [←row t,Fin.val_cast_of_lt ((E t).isLt.trans_le rowsFit),
      Nat.mod_eq_of_lt ((E t).isLt.trans_le slotCap),row,stock,Fin.cast_val_eq_self]
  · intro t
    let j : Fin (GlobalTests.kinds N k) := ⟨PurchaseInventory.lane t,PurchaseInventory.lane_lt _⟩
    let n : Fin (g₀).stride := ⟨(entry ((A).stockAt a t)).val,limit t⟩
    cases a with
    | outer phase trial =>
      exact DeadlineROM.read_outer v.mesh v.finish (v.basePhase width) (H).ports.stop _ _ phase trial state scalar date j n
    | inner phase trial slice tick =>
      exact DeadlineROM.read_inner v.mesh v.finish (v.basePhase width) (H).ports.stop _ _ phase trial slice tick state
        scalar date.1 date.2 j n

/-- The guard stores only its one event-local bit. Each true account word
is below that bit at the concrete event on both outer and reserve dates. -/
theorem guard_quote_stock (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
    (a : Attempt) (entry : Memory W) (t : C) :
    ((guard (v.nativeChart P z width r banks src tab dst owners) a).apply entry)
      ((fs a).stockSource.old.base+PurchaseInventory.slot t) = entry ((A).stockAt a t) := by
  let arena := v.privateArena P z width
  let chart := v.nativeChart P z width r banks src tab dst owners
  let x := (fs a).stockSource.old.base+PurchaseInventory.slot t
  have row := (PurchaseInventory.slotEquiv z N k t).isLt
  change PurchaseInventory.slot t < PurchaseInventory.footprint z N k at row
  have pad := v.stock_padded_old P z width a
  have fits := ProtocolRAMPurchaseSampler.lt_span (PurchaseInventory.footprint z N k)
  have early : x < arena.base v.mesh (.attempt a) := by
    change (fs a).market.shelf.stockBase+PurchaseInventory.slot t < arena.base v.mesh (.attempt a)
    exact (Nat.add_lt_add_left (row.trans fits) _).trans_le pad
  have quiet := (v.event_prefix P z width r banks src tab dst owners (.attempt a) x early).1
  rw [v.stock_pointer P z width bills a t]
  exact ProtocolRAMGeneratedWrite.frame_image (chart.stopAt a) 1 (stop chart.mesh chart.modeAt a) entry x (.inl quiet.1)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
