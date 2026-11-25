import OAI.Hierarchy.ProbeFixedPlacedSpill
import OAI.Hierarchy.ProbeFixedNonrepairSpill
import OAI.Hierarchy.ProbeFixedDatedRepairs
import OAI.Hierarchy.ProbeFixedRepairWordRoom
import OAI.Hierarchy.ProtocolRAMCatalystPurchasedOrigin

namespace OAI
/-! # Born, rejected, failed and quiet trials on a single physical overflow tape -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native CoreBoard AdaptiveProbe AdaptiveProbe.OuterBank
open StripChart StockCommit PurchaseCT PurchaseFrozen CatalystArchive
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  {v : FixedProtocolFormat F k p q Q σ Λ} {P : v.Placement} {z width r : ℕ}
  {banks : RouteSettlement.Banks} {src tab dst : ℕ} {owners : Bank}
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "G" => v.privateArena P z width
local notation "H" => v.publicHeader P z width
variable {π : Equiv.Perm (Fin (2^z))} {mem fixture : Memory (wordBits z (2^v.W) copies)}
  (D : v.ReadbackRun P z width r banks src tab dst owners π mem fixture)


private theorem inner_indices (c : Mesh) (p h j b : ℕ) (incl : Event.attempt (.inner p h j b)∈events c) :
    p<c.inject+c.cool ∧ h<c.outerFuel ∧ j<c.reserveSteps ∧ b<c.innerFuel := by
  obtain ⟨u,hu,phase⟩:=List.mem_flatMap.mp incl
  rcases List.mem_append.mp phase with attempts|endPhase
  · obtain ⟨a,ha,trial⟩:=List.mem_flatMap.mp attempts
    rcases List.mem_cons.mp trial with outer|inside
    · cases outer
    · obtain ⟨v,hv,slice⟩:=List.mem_flatMap.mp inside
      rcases List.mem_append.mp slice with actions|endSlice
      · obtain ⟨t,ht,same⟩:=List.mem_map.mp actions
        cases same
        exact ⟨List.mem_range.mp hu,List.mem_range.mp ha,List.mem_range.mp hv,List.mem_range.mp ht⟩
      · simp at endSlice
  · simp at endPhase

include D in
/-- Outside a repair the excess transfer emits zero. On a repair the emitted
unsigned word is precisely pre-clipped stock minus retained stock, and each
physical account receives at most one ordinary port's issued width. -/
theorem ReadbackRun.attempt_spill (B : RepairWordBounds v P z width) (a : Attempt)
    (prior tail : List Event) (entry : Memory W) (slot : Slot C mem (.attempt a) prior tail entry)
    (i : Fin (v.nativeFormats P z width a).pricedArea.goods) :
    let ar:=(v.nativeFormats P z width a).pricedArea
    let out:=after C (.attempt a) entry
    let excess:=(out (ar.output+ar.goods+ar.goods+i.val)).val
    let mode:=AttemptGate.actual (repair C a).policy
      (PurchaseStage.postSnapshot ((C).layout a) (repair C a) (prepared C a entry))
    excess=(if mode=2 then v.repairRaw P z width r banks src tab dst owners a entry i-(out (ar.output+i.val)).val else 0) ∧
      excess≤v.menu.maximum*width := by
  classical
  let : Nonempty (Fin k):=⟨⟨0,v.positive⟩⟩
  intro ar out excess mode
  have occurs : Event.attempt a∈events v.mesh := by change _∈events (C).mesh; rw [slot.events]; simp
  have layout:=(D.boards a occurs).1
  by_cases failed : mode=2
  · rw [ite_eq_left failed]
    let signed:=RepairSlot.ofWords v P z width r banks src tab dst owners mem D.nativeStock D.valid
      D.resident D.prices D.charges D.digitBudget B.late B.threshold B.alphabet B.rate D.widths
      a prior tail entry slot layout failed
    cases a with
    | outer phase trial =>
      let fit:=v.payload_fit_at_slot P z width r banks src tab dst owners phase trial entry signed D.payload
      exact v.payload_spill_word P z width r banks src tab dst owners phase trial entry fit signed i
    | inner phase trial slice inner =>
      obtain ⟨hp,hh,hj,hb⟩:=inner_indices v.mesh phase trial slice inner occurs
      obtain ⟨_,other⟩:=inner_slot C mem phase trial slice inner hp hh hj hb D.nativeStock.mounted_all
      have same : innerState C mem phase trial slice inner=entry:=other.entryMemory.symm.trans slot.entryMemory
      have born:=D.purchased ⟨phase,hp⟩ ⟨trial,hh⟩ ⟨slice,hj⟩ ⟨inner,hb⟩
      rw [same] at born
      let fit:=v.purchased_fit_at_slot P z width r banks src tab dst owners phase trial slice inner entry signed D.payload
      have low:=((D.keys phase trial).1).trans
        (show (G).first≤(G).base v.mesh (.attempt (.inner phase trial slice inner)) from Nat.le_add_right ..)
      exact v.purchased_spill_word P z width r banks src tab dst owners phase trial slice inner entry fit signed π low born i
  · rw [ite_eq_right failed]
    have idle:=v.nonrepair_spill P z width r banks src tab dst owners a entry slot.currentReady layout failed i
    have zero : excess = 0 := by
      simpa only [Fin.val_zero] using congrArg Fin.val idle
    exact ⟨zero,zero.le.trans (Nat.zero_le _)⟩

/-- Uniform in the public arena, raw selector history, event and original
commodity ordinal. The constant is the maximum individual menu width. -/
theorem attempt_spill_bound (v : FixedProtocolFormat F k p q Q σ Λ) :
    ∀ᶠ z : ℕ in Filter.atTop,∀ (P : v.Placement) (width r : ℕ) (banks : RouteSettlement.Banks)
      (src tab dst : ℕ) (owners : Bank) (π : Equiv.Perm (Fin (2^z)))
      (mem fixture : Memory (wordBits z (2^v.W) copies)),
      v.ReadbackRun P z width r banks src tab dst owners π mem fixture →
      let chart:=v.nativeChart P z width r banks src tab dst owners
      ∀ (a : Attempt) (prior tail : List Event) (entry : Memory (wordBits z (2^v.W) copies)),
        Slot chart mem (.attempt a) prior tail entry →
        let ar:=(v.nativeFormats P z width a).pricedArea
        ∀i : Fin ar.goods,((after chart (.attempt a) entry) (ar.output+ar.goods+ar.goods+i.val)).val≤v.menu.maximum*width := by
  filter_upwards [v.repair_word_room] with z numeric
  intro P width r banks src tab dst owners π mem fixture read chart a prior tail entry cut ar i
  have w:=numeric P width read.payload
  let B : RepairWordBounds v P z width:=⟨w.1,w.2.1,w.2.2.1,w.2.2.2.1,w.2.2.2.2.1,w.2.2.2.2.2⟩
  exact (read.attempt_spill B a prior tail entry cut i).2

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
