import OAI.Computability.NearSquareRoot.ScheduleRegisterSelectMix
import OAI.Computability.NearSquareRoot.KernelScaleSpectator
import OAI.Computability.IntegerMultiplication.Match

/-! # Tag-independent transport commands for the scale bank

Expanding spectator positions and zipping scalar tags with records operate on
whole encoded trees. Their register bound is independent of the number of tags.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RegisterSelect
open IntegerMultiplication Code Filter RegisterWitness KernelScaleSpectator

/-- Replacing payloads by their literal tree encodings changes no input symbol. -/
theorem send_erase {X : Type*} [Codec X] (xs : List X) : send (xs.map send) = send xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,send_cons,ih]
    rfl

private abbrev SpectatorInput := ℕ+ × ℕ+ × List Tree

/-- The very same instruction tree expands every record encoding and both
counts. The clock is a single absolute multiple of the repeated input volume. -/
theorem spectator_command : ∀ᶠ R in atTop, ∃ (cmd : Cmd) (C : ℕ), CommonRegisters.Within R cmd ∧
    ∀ {X : Type} [Codec X] (p b : ℕ) (xs : List X), 0 < p → 0 < b → ∀ env,
    Fits.value env cmd 0 (send ((tally p,tally b),xs)) (send (expand p b xs)) (C*(p*b*size xs+1)) := by
  let run := expandPositive (fun k : SpectatorInput => k.1.val) (fun k => k.2.1.val) (fun k => k.2.2)
    (fun k => k.1.property) (fun k => k.2.1.property)
  filter_upwards [checked_eventually run] with R h
  obtain ⟨cmd,hr,C,hc⟩ := h
  refine ⟨cmd,C,hr,?_⟩
  intro X inst p b xs hp hb env
  let j : SpectatorInput := (⟨p,hp⟩,⟨b,hb⟩,xs.map send)
  have e := hc j env
  change Fits.value env cmd 0 (send ((tally p,tally b),xs.map send)) (send (expand p b (xs.map send)))
    (C*(p*b*size (xs.map send)+1)) at e
  have output : send (expand p b (xs.map send)) = send (expand p b xs) :=
    (congrArg send (map_expand send p b xs)).symm.trans (send_erase (expand p b xs))
  rw [output] at e
  simpa only [size,send_prod,send_erase] using e

theorem spectators : ∀ᶠ R in atTop, ∀ {I X : Type} [Codec X] (p b : I → ℕ) (xs : I → List X),
    (∀ i, 0 < p i) → (∀ i, 0 < b i) →
    Timed R (fun i => p i*b i*size (xs i)) (fun i => send ((tally (p i),tally (b i)),xs i))
      (fun i => send (expand (p i) (b i) (xs i))) := by
  filter_upwards [spectator_command] with R h
  obtain ⟨cmd,C,hr,run⟩ := h
  intro I X inst p b xs hp hb
  exact ⟨cmd,hr,C,fun i => run _ _ _ (hp i) (hb i)⟩

private theorem map_zip_left {X Z Y : Type*} (g : X → Z) (xs : List X) (ys : List Y) :
    (xs.map g).zip ys = (xs.zip ys).map (fun p => (g p.1,p.2)) := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih => cases ys <;> simp [ih]

private theorem map_zipFair {X Z Y : Type} (g : X → Z) (x : X) (y : Y) (xs : List X) (ys : List Y) :
    zipFair (g x) y (xs.map g,ys) = (zipFair x y (xs,ys)).map (fun p => (g p.1,p.2)) := by
  simp only [zipFair,cutLists,ruler_length,zipSafe,List.length_map]
  rw [← List.map_replicate, ← List.map_append, map_zip_left,List.map_take]

private theorem send_map_pairs {X Y : Type} [Codec X] [Codec Y] (xs : List (X × Y)) :
    send (xs.map (fun p => (send p.1,p.2))) = send xs := by
  induction xs with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons,send_cons,ih,send_prod]; rfl

/-- The compiled zip sees an encoded zero tag in the padding position.
That tree is identical for every nonempty tag type used by the scale pass. -/
theorem zipTags : ∀ᶠ R in atTop, ∀ q : ℕ,
    RegisterWitness.Easy R (zipFair (0 : Fin (2^q)) (([],[]) : Dusk.Pair)) := by
  let blank := send (tally 0)
  filter_upwards [easy_eventually (easy_zip blank (([],[]) : Dusk.Pair))] with R h
  intro q
  let j (p : List (Fin (2^q)) × List Dusk.Pair) := (p.1.map send,p.2)
  apply (Timed.on h j).conform <;> intro p
  · simp [j,size,send_erase]
  · simp [j,send_erase]
  · change send (zipFair (send (0 : Fin (2^q))) _ (p.1.map send,p.2)) = _
    rw [map_zipFair,send_map_pairs]

end RegisterSelect

end NearSquareRoot
end Computability
end OAI
