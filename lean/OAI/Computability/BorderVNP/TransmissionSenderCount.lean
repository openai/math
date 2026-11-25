import OAI.Computability.BorderVNP.TransmissionImageReturns
import OAI.Computability.BorderVNP.TransmissionSenderStable
import Mathlib.SetTheory.Cardinal.Finite

/-! # Counting histories when the physical sender words are read-only -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM
open scoped Classical

variable {w : ℕ}

/-- A protected origin and exterior region make the acceptance of the sender comparisons
independent of the locally guessed slots. Hence either all fixed-width words return,
one history per word, or the physical source/link comparison rejects them all. -/
theorem senderWords_card {f : BroadcastFrame} (rows : ℕ → Range w) (pub : Arg → Word w)
    (m : Memory w) (frame : f.At (readings pub) (readings m)) (fit : f.Fits w (pub 0).val)
    (sep : ∀ i < (directoryFrame pub m 13).val, (rows i).scheduleSeparated (directoryFrame pub m 0) pub m f.teams)
    (peer : ∀ i < (directoryFrame pub m 13).val, (rows i).teamB.val < f.teams)
    (protectedReads : ∀ k < (directoryFrame pub m 13).val,
      (rows k).selected (directoryFrame pub m 0) = some (some .sendData) → ∀ j < (rows k).width.val,
        ∀ i < k, (rows i).protectsCell (directoryFrame pub m 0) ((rows k).source.val+j) ∧
          (rows i).protectsCell (directoryFrame pub m 0) ((rows k).senderAddress pub m j)) :
    let team := directoryFrame pub m 0
    let count := (directoryFrame pub m 13).val
    Nat.card (SenderWords rows pub m) =
      if ∀ i < count, (rows i).senderMatches team pub m then 2 ^ choiceOffset rows team count else 0 := by
  let team := directoryFrame pub m 0
  let count := (directoryFrame pub m 13).val
  let WordBits := Fin (choiceOffset rows team count) → Bool
  have ht : team.val = f.team := by simpa [team,directoryFrame,frameField,readings] using frame.1
  have iffCheck (b : WordBits) (i : ℕ) (hi : i < count) :
      (rows i).senderMatches team pub
        (tableMemory rows team pub m (decodeChoices rows team (List.ofFn b)) i) ↔
        (rows i).senderMatches team pub m :=
    table_senderMatches_stable rows team pub m _ i frame fit ht
      (fun j hj => sep j (hj.trans hi)) (peer i hi) (protectedReads i hi)
  dsimp only
  by_cases ok : ∀ i < count, (rows i).senderMatches team pub m
  · rw [ite_eq_left ok]
    let allWords : WordBits ≃ SenderWords rows pub m := {
      toFun := fun b => ⟨b, fun i hi => (iffCheck b i hi).mpr (ok i hi)⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    rw [← Nat.card_congr allWords, Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, Fintype.card_bool]
  · rw [ite_eq_right ok]
    exact Nat.card_eq_zero.mpr (.inl ⟨fun b => ok (fun i hi => (iffCheck b.val i hi).mp (b.property i hi))⟩)

/-- The same all-or-none count on native returning traces of the constructed schedule.
In the passing case every history has positive sign and its private slot assignment is
recorded exactly once by `image_sender_equiv`. -/
theorem image_return_card {l : TableLayout} {row : ℕ → TableRow}
    {before : ℕ → ℕ} {m : Memory w} (image : l.Image row before (readings m))
    (al : l.Allocated w) (rowsFit : l.RowsFit w row) (initial : l.recordsMatch row before)
    (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (s : Bank w)
    (hf : (pub 0).val = l.frame) (loaded : l.frameFields before)
    (f : BroadcastFrame) (frame : f.At (readings pub) (readings m))
    (fit : f.Fits w (pub 0).val) (teams : f.teams = l.teams)
    (capacity : ∀ u v, f.header + Routing.legLoad al.teamCount (l.widthMatrix row) u v +
      Routing.legLoad al.teamCount (l.widthMatrix row) v u ≤ f.capacity)
    (directory : ∀ i < l.count, (tableRange l m i).directorySeparated (directoryFrame pub m 0) l)
    (sep : ∀ i < l.count, (tableRange l m i).scheduleSeparated (directoryFrame pub m 0) pub m f.teams)
    (sourceFit : ∀ i < l.count, (tableRange l m i).selected (directoryFrame pub m 0) = some (some .sendData) →
      (tableRange l m i).source.val+(tableRange l m i).width.val ≤ 2^w)
    (protectedReads : ∀ k < l.count,
      (tableRange l m k).selected (directoryFrame pub m 0) = some (some .sendData) →
      ∀ j < (tableRange l m k).width.val, ∀ i < k,
        (tableRange l m i).protectsCell (directoryFrame pub m 0) ((tableRange l m k).source.val+j) ∧
        (tableRange l m i).protectsCell (directoryFrame pub m 0) ((tableRange l m k).senderAddress pub m j)) :
    let team := directoryFrame pub m 0
    let rows := tableRange l m
    Nat.card (TableReturn pub macros s m) =
      if ∀ i < l.count, (rows i).senderMatches team pub m then 2 ^ choiceOffset rows team l.count else 0 := by
  obtain ⟨E, _⟩ := image_sender_equiv image al rowsFit initial pub macros s hf loaded f frame fit teams capacity
    directory sep sourceFit
  rw [← Nat.card_congr E]
  have count := image_count image al pub hf loaded
  have inside {i : ℕ} (hi : i < (directoryFrame pub m 13).val) : i < l.count := count ▸ hi
  simpa only [count] using senderWords_card (tableRange l m) pub m frame fit
    (fun i hi => sep i (inside hi))
    (fun _ hi => (ScheduledRange.of_table image al rowsFit initial f teams (inside hi)).second)
    (fun i hi => protectedReads i (inside hi))

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
