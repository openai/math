import OAI.Hierarchy.GridChosenReceiverDescendants
import OAI.Hierarchy.GridChosenReceiverSpending
import OAI.Hierarchy.GridReceiverDirectoryRestore

namespace OAI
/-! # Restoring the genuine installed tick's terminal directory after its cache replay -/

noncomputable section
namespace Hierarchy.GridChosenReceiver
open ThreeFlat Diagonal PhysicalStage RAM RAM.PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open TraceAdmission GridScale GridThrough GridRegisteredSetting GridInstalledEvaluator GridReceiverDirectory Filter
open scoped Classical

open scoped Fin.CommRing
private theorem casted_assignment {W a b d T : ℕ} (n : a=b) (p : Fin a → Fin d → ℕ)
    {ht : 0 < T} {m₀ m₁ : Memory (64*W)} (ok : GridSimulation.Assigned ht p m₀ m₁) :
    GridSimulation.Assigned ht (fun i : Fin b => p (i.cast n.symm)) m₀ m₁ := by subst b; exact ok

private theorem casted_ticked {W w a b d T : ℕ} (n : a=b) (p : Fin a → Fin d → ℕ)
    (B : GridReceiverTickDirectory.Banks) (t : Fin T) (m₀ m₁ : Memory W) :
    GridReceiverTickDirectory.Ticked B (FactorAllocation.factors w p (List.finRange a) t) (t.val:Word W) m₀ m₁ ↔
    GridReceiverTickDirectory.Ticked B (FactorAllocation.factors w (fun i : Fin b => p (i.cast n.symm))
      (List.finRange b) t) (t.val:Word W) m₀ m₁ := by subst b; rfl

variable {F : Type} [Field F] [Fintype F] {Q : ℕ→ℕ} {loss : ℕ→ℝ}
section PerStream
set_option quotPrecheck false
open GridReceiverTickDirectory GridReceiverDirectoryRestore TickWorkspace
variable {blk : Block F} {m A w degree stageRate rootRate tariff power : ℕ}
variable {v : TickSelection F (m+1) A w Q loss} (I : Installed blk m A w degree stageRate rootRate v)
variable (R : GridInstalledFit.Receipt blk m A w degree stageRate rootRate v I tariff power)
local notation "l" => (layout m A w (overhead Q loss w) v.copies degree stageRate rootRate)
local notation "arch" => (GridDescription.capacity w)
local notation "gate" => (26*GridDescription.sector w)
local notation "W" => (64*w)
local notation "rails" => (GridControllerSimGeometry.railCount m (l).sideMinusOne (l).bank)

local notation "D" => I.D
local notation "par" => (GridReceiverDirectory.native I.D l).parameters
local notation "ct" safe:arg => (GridNativeDispatch.actualTable I.D safe).codes
local notation "sr" safe:arg => GridNativeDispatch.selectorRoom I.D l R.table R.selector safe
local notation "sel" z:arg safe:arg => GridReceiverDirectory.InputWindow I.D l z safe (sr safe)
local notation "rooms" recv:arg => (R.rooms recv 0 gate).choose
local notation "ext" => (fun i=>(v.replacement.width_le_size i).trans v.size_le)
local notation "tape" recv:arg safe:arg z:arg x:arg c:arg i:arg => streamInput I recv 0 gate R.text (rooms recv) ext (ct safe) (sr safe) z x c i
local notation "st" recv:arg safe:arg z:arg x:arg c:arg i:arg => GridReceiverDirectory.shifted l w (tape recv safe z x c i)
local notation "orig" recv:arg safe:arg z:arg x:arg c:arg i:arg =>
  GridReceiverDirectory.original I.D l (sel z safe) (tape recv safe z x c i)
local notation "plan" => GridReceiverBanks.pinPlan I.D l
local notation "Q₀" geom:arg recv:arg safe:arg z:arg => streamLayout I R geom recv safe z

local notation "age₀" => TraceAdmission.receiverAge w
local notation "A₀" => GridReceiverTickDirectory.banks w age₀
local notation "rows" => (((20*(w+1)+2)^((m+1)+2))*(par).roots)
local notation "J₀" => GridDescription.sector w
local notation "text₀" => (l).receiverText
local notation "headAt" recv:arg safe:arg z:arg c:arg i:arg => GridReceiverHeader.header text₀ R.text
  (GridDescription.code (q:=w^2) recv I.D.machine) ((GridTicks.index (c,i)).val:Word W)
  (GridNativeDispatch.params I.D l 0 gate) (sel z safe)

/-- The post used by the first terminal row, including the original shifted
input and the newly published caches at their native workspace addresses. -/
def SlotRestored (recv : Machine W arch arch arch) (safe : GridNativeDispatch.WordRoom I.D)
    (z : I.D.trace) (x : GridDiagonal.Pins (Fin rails)) (c : Cell (m+1) (l).sideMinusOne) (i : Fin v.copies)
    (desc restored : Memory W) : Prop :=
  GridReceiverTickDirectory.Ticked A₀ (selectedRoots I.D l z.1 (GridTicks.index (c,i)))
    ((GridTicks.index (c,i)).val:Word W) desc restored ∧
  (∀ a, a < base age₀ 17 ∨ (base age₀ 19 ≤ a ∧ a < 15*J₀) ∨ 16*J₀ ≤ a → restored a=desc a) ∧
  ∀ a < base age₀ 1, restored a=(st recv safe z x c i) a

set_option maxRecDepth 32000 in
set_option maxHeartbeats 4000000 in
theorem slot_rebuild (geom : ElectionRoom I.D l) (recv : Machine W arch arch arch)
    (safe : GridNativeDispatch.WordRoom I.D) (z : I.D.trace) (x : GridDiagonal.Pins (Fin rails))
    (c : Cell (m+1) (l).sideMinusOne) (i : Fin v.copies) {elected desc : Memory W}
    (j : TraceReceiverElectedJournal.Journal I.D l geom safe z (sel z safe) (GridTicks.index (c,i))
      (st recv safe z x c i) (orig recv safe z x c i) elected)
    (scalar : TraceReceiverInstalledScalars.Ready I.D l j)
    (ledger : TraceReceiverElectedCache.published I.D l j (Q₀ geom recv safe z) desc)
    (held : TraceReceiverEntryTables.TableFrame w age₀ (RAM.HistoryStageBody.Physical.libraryWords I.D.block W)
      elected (TraceReceiverTablesMount.output I.D elected))
    (owners : GridPinPublisher.PrefixOwners plan (TraceReceiverTablesMount.output I.D elected)) :
    (GridReceiverTickDirectory.build A₀ W (2+text₀) (par).roots rows).Spec (·=desc)
      (fun _ out => SlotRestored I R recv safe z x c i desc out) (GridChosenReceiver.rebuild I.D l) := by
  let t := GridTicks.index (c,i)
  let fees := I.D.issuedUnit w (l).degree (l).stageRate (l).rootRate
  let p := I.D.costs (GridNativeImage.resources I.D l) z.1 m (l).sideMinusOne (l).bank I.D.issuedCharges fees
  let pᵣ := fun f : Fin (par).roots => p (f.cast j.count.symm)
  let head := headAt recv safe z c i
  have hd : head.length ≤ (l).pinWidth ∧ ∀ b : Fin head.length,
      (tape recv safe z x c i) b.val = head[b.val] :=
    stream_header I recv 0 gate R.text (rooms recv) ext (ct safe) (sr safe) z x c i
  obtain ⟨lower,upper⟩ := TraceAdmission.receiverAge_chart w scalar.big
  have large : 2 ≤ w := (by decide : 2 ≤ 64^10).trans scalar.big
  have width : (l).pinWidth ≤ 2^w := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have chart : 2^w ≤ stride age₀ := by
    change 2^w ≤ (2^(age₀^10))^4
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have wide : 2 ≤ stride age₀ := (show 2^1 ≤ 2^w from Nat.pow_le_pow_right (by decide) (by omega)).trans chart
  have lowHead : 2+head.length ≤ base age₀ 1 := by
    change 2+head.length ≤ 2*stride age₀
    have len := hd.1;omega
  have low : 2+text₀+W ≤ base age₀ 1 := by
    have fit : text₀+W ≤ head.length := by
      dsimp only [head]
      rw [GridReceiverHeader.length]
      apply Nat.add_le_add_left
      exact (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans (Nat.le_add_right ..)
    omega
  have below (a : ℕ) (small : a < base age₀ 1) : j.reg a=(st recv safe z x c i) a := by
    apply j.below
    change a < 21*stride age₀;change a < 2*stride age₀ at small;omega
  have mounted (b : Fin head.length) : j.reg (2+b.val)=((head[b.val]).toNat:Word W) := by
    have hb := b.isLt
    rw [below _ (by omega)]
    let p₀ : Fin (l).pinWidth := ⟨b.val,hb.trans_le hd.1⟩
    have val := TickMountedPins.memory_at (w:=W)
      (fun h : Fin (l).pinWidth => (tape recv safe z x c i) h.val) p₀
    change (st recv safe z x c i) (2+b.val)=_
    rw [show (st recv safe z x c i) (2+b.val)=BitLayout.bitWord W ((tape recv safe z x c i) b.val) from val,hd.2 b]
    cases head[b.val] <;> rfl
  have tickReads := GridReceiverDirectoryRestore.tick_input t geom.ticks R.text
    (GridDescription.code (q:=w^2) recv I.D.machine) (GridNativeDispatch.params I.D l 0 gate) (sel z safe) j.reg mounted
  have budget := scalar.bound
  rw [j.first,j.roots] at budget
  have ownerRoom := TraceReceiverOwnerMount.native_room geom.pos (by omega : 3*w ≤ age₀^10) upper budget
  obtain ⟨bounds,small⟩ := streamLayout_room I R geom z
  have assigned := casted_assignment j.count p j.assigned
  have roster := (casted_ticked (w:=w) j.count p A₀ t j.classified elected).1 j.ticked
  have durable (a : ℕ) (free : TickTerminalRoot.slotKeep age₀ a) : desc a =
      TraceReceiverOwnerMount.output age₀ (par).firstFinal (par).roots (A₀).owners ((A₀).scratch+1)
        ((plan).intervalMemory (base age₀ 5) (TraceReceiverTablesMount.output I.D elected)) a := by
    have old := RAM.HistoryStageBody.Physical.Ledger.durable ledger a free
    simpa only [TraceReceiverDescendantExecution.entry,TraceReceiverDescendantExecution.sliced,
      TraceReceiverLeafSetup.intervalBase,j.first,j.roots] using old
  have groups : ((20*(w+1)+2)^((m+1)+2)) < 2^W := by
    have fit : (20*(w+1)+2)^((m+1)+2) ≤ GridPinArena.slab w := geom.groups
    have cap := GridPinArena.scales w geom.pos;omega
  have run : Procedure.Spec _ _ _ _ := GridReceiverDirectoryRestore.rebuild_from_durable geom.teams_pos pᵣ t bounds ownerRoom
    large lower upper small.bits scalar.librarySize geom.items groups geom.ticks geom.room low
    assigned roster held owners durable tickReads
  intro pcs regs pubs machine
  refine Procedure.Spec.mono (post' := fun _ out => SlotRestored I R recv safe z x c i desc out)
    @run (fun _ yes=>yes) ?_ le_rfl machine
  rintro _ out ⟨returned,inputFrame⟩
  refine ⟨(casted_ticked (w:=w) j.count p A₀ t desc out).2 returned,?_,?_⟩
  · exact GridReceiverDirectoryRestore.rebuild_frame geom.pos upper (by have := ownerRoom.fixed; omega)
      geom.teams_pos pᵣ t (2+text₀) geom.room returned
  · exact fun a ha => (inputFrame a ha).trans (below a ha)

/-- Recover the same journal used by the descendant cache and invoke its actual
registered restoration. -/
theorem slot_rebuild_cache (geom : ElectionRoom I.D l) (recv : Machine W arch arch arch)
    (safe : GridNativeDispatch.WordRoom I.D) (z : I.D.trace) (x : GridDiagonal.Pins (Fin rails))
    (c : Cell (m+1) (l).sideMinusOne) (i : Fin v.copies) {elected desc : Memory W}
    (cache : slotCache I R geom recv safe z x c i elected desc)
    (ready : ∀ j : TraceReceiverElectedJournal.Journal I.D l geom safe z (sel z safe) (GridTicks.index (c,i))
      (st recv safe z x c i) (orig recv safe z x c i) elected, TraceReceiverInstalledScalars.Ready I.D l j) :
    (GridReceiverTickDirectory.build A₀ W (2+text₀) (par).roots rows).Spec (·=desc)
      (fun _ out => SlotRestored I R recv safe z x c i desc out) (GridChosenReceiver.rebuild I.D l) := by
  obtain ⟨j,ledger,held,owners,_⟩ := cache
  exact slot_rebuild I R geom recv safe z x c i j (ready j) ledger held owners

end PerStream
end Hierarchy.GridChosenReceiver
end

end OAI
