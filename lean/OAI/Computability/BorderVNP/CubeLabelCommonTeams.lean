import OAI.Computability.BorderVNP.CubeTeamOwnedLabelWords
import OAI.Computability.BorderVNP.CubeGroupDirectoryBalances

/-! # The same physical label and demand at all teams

The native chooser and interval pass read each team's own local RAM. Equal original
traffic and public cell numbering give the same chosen label and incoming width in
every returned memory, even with relocated sparse rows and different dummy endpoints.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open VPVNP.BurstRAM RoutingISA RoutingISA.LocalRow Crossing Physical MeanChoice LabelIndex Finset
open scoped BigOperators Classical
variable {D : ℕ} {P : Type*} {bits : P → ℕ} {Cell : Type} [Fintype Cell] [DecidableEq Cell] {A : Type*} [Fintype A]
variable (N : Network D P bits) (cell : N.Site → Cell) (recv : A → Cell) (width : A → ℕ)

/-- Read back the mathematical label and total incoming original delivery width from
one actual pair of output arrays. Empty inserted rows and zero-width originals contribute zero. -/
theorem DirectoryWords.network {dir : LabelIndex.Layout} {before after : ℕ → ℕ} {ep : Endpoints dir before}
    {z lab : ℕ} (out : DirectoryWords dir before ep z lab after) (cells : Cell ≃ Fin dir.cells)
    {edges : N.CrossingEdge cell ↪ Fin dir.cableCount} {data : A ↪ Fin dir.deliveryCount}
    (place : RowPlacement (networkRows N cell recv width) (fromTables dir before ep) cells (edges.sumMap data))
    (c : Cell) :
    after (lab+(cells c).val) = (meanPackedCodes N cell recv width ((List.finRange dir.cells).map cells.symm) z c).val ∧
    after (dir.data+(cells c).val) = ∑ j, if recv j=c then width j else 0 := by
  refine ⟨?_,?_⟩
  · rw [out.labels,tableCodes_eq_meanPackedCodes N cell recv width dir before ep cells place]
    simp
  · rw [out.demands]
    symm
    apply Fintype.sum_of_injective data data.injective
    · intro j miss
      have unused := place.unused (.inr j) (by
        rintro ⟨e|a,eq⟩
        · contradiction
        · exact miss ⟨a,Sum.inr.inj eq⟩)
      change (deliveryAt dir before j.val).2 = 0 at unused
      simp [unused]
    · intro a
      have row := place.live (.inr a)
      change rowEquivalent (.delivery ⟨(deliveryAt dir before (data a).val).1,_⟩ (deliveryAt dir before (data a).val).2)
        (.delivery (cells (recv a)) (width a)) at row
      rcases row with eq | ⟨left,right⟩
      · obtain ⟨loc,sz⟩ := Traffic.delivery.inj eq
        have key := congrArg Fin.val loc
        change (deliveryAt dir before (data a).val).1 = (cells (recv a)).val at key
        have same : (cells (recv a)).val=(cells c).val ↔ recv a=c := ⟨fun h => cells.injective (Fin.ext h),fun h => h ▸ rfl⟩
        simp only [key,sz,same]
      · change (deliveryAt dir before (data a).val).2 = 0 at left
        change width a = 0 at right
        simp [left,right]

/-- Identical results of the actual two-stage assembly on arbitrary teams that share
one original packed network, delivery placement and ascending public cell order. -/
theorem common_selected_words {T : Type*} {w : ℕ} (pub : T → Arg → Word w) (mac : T → TeamOpcode.Macros w 8)
    (bank : T → Bank w) (mem selected : T → Memory w) (events : T → List (TeamRAM.Event w)) (post : T → Bank w)
    (run : ∀ t, Runs (pub t) (mac t) (.seq LabelIndex.directoryProgram NativeIntervals.prepare)
      (bank t) (mem t) (events t) (post t) (selected t))
    (fit : ∀ t, LabelPrefixFits (pub t 0).val w (readings (mem t))) (z : ℕ) (order : List Cell) :
    let dir := fun t => LabelIndex.layout (pub t 0).val (readings (mem t))
    let lab := fun t => readings (mem t) ((pub t 0).val+48)
    ∀ (cells : ∀ t, Cell ≃ Fin (dir t).cells) (edges : ∀ t, N.CrossingEdge cell ↪ Fin (dir t).cableCount)
      (data : ∀ t, A ↪ Fin (dir t).deliveryCount),
      (∀ t, RowPlacement (networkRows N cell recv width) (fromTables (dir t) (readings (mem t)) (fit t).endpoints)
        (cells t) ((edges t).sumMap (data t))) →
      (∀ t, (List.finRange (dir t).cells).map (cells t).symm = order) →
      (∀ t, (dir t).labels-1 = z) → (∀ t, (dir t).data+(dir t).cells ≤ readings (mem t) ((pub t 0).val+57)) →
      ∀ t u c, readings (selected t) (lab t+(cells t c).val) = readings (selected u) (lab u+(cells u c).val) ∧
        readings (selected t) ((dir t).data+(cells t c).val) = readings (selected u) ((dir u).data+(cells u c).val) := by
  intro dir lab cells edges data placement ascending symbols room t u c
  have one (i : T) := (labelDirectoryWords_of_run (pub i) (mac i) (bank i) (mem i) (run i) (fit i) (room i)).network
    N cell recv width (cells i) (placement i) c
  have get (i : T) : readings (selected i) (lab i+(cells i c).val) = (meanPackedCodes N cell recv width order z c).val ∧
      readings (selected i) ((dir i).data+(cells i c).val) = ∑ j, if recv j=c then width j else 0 := by
    have h := one i
    change readings (selected i) (lab i+(cells i c).val) =
      (meanPackedCodes N cell recv width ((List.finRange (dir i).cells).map (cells i).symm) ((dir i).labels-1) c).val ∧ _ at h
    rwa [ascending,symbols] at h
  exact ⟨(get t).1.trans (get u).1.symm,(get t).2.trans (get u).2.symm⟩

end Cube.GroupWeights

end BorderVNP
end Computability
end OAI
