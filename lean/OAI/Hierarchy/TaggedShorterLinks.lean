import OAI.ThreeFlat.Routing.SpillSlots
import OAI.ThreeFlat.Routing.CallBatches
import OAI.ThreeFlat.Routing.BatchEndpointLinks

namespace OAI
/-! # Labelled link occurrences through a compaction board

A link occurrence has a distinct identifier within its batch. Distinct
occurrences may read the same source or target payload. Conservation of the
complete words then gives an embedding of the occurrences into the packed
rows, recovering their common identifiers on both sides.
-/

noncomputable section
namespace Hierarchy.TaggedShorterLinks
open ThreeFlat Routing Spill
open scoped Classical BigOperators

variable {A : Type*} [Fintype A] {D H m : ℕ}

def named (f : A ↪ Fin D) (word : A → Fin m → Bool) : RecordPins D m → Bool :=
  Function.uncurry (BatchEndpointLinks.output f word)

theorem named_occupied (f : A ↪ Fin D) (word : A → Fin m → Bool) :
    occupied (named f word) = Finset.univ.map f := by
  ext i
  simp only [occupied,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map]
  change BatchEndpointLinks.output f word i none = true ↔ ∃ a, f a = i
  by_cases hi : i ∈ Set.range f
  · obtain ⟨a,rfl⟩ := hi
    simp
  · simp only [BatchEndpointLinks.output_idle f word i hi,Bool.false_eq_true,false_iff]
    rintro ⟨a,eqn⟩
    exact hi ⟨a,eqn⟩

theorem named_payloads (f : A ↪ Fin D) (word : A → Fin m → Bool) :
    payloads (named f word) = Finset.univ.val.map word := by
  unfold payloads
  rw [named_occupied]
  change (Finset.univ.val.map f).map _ = _
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro a _
  funext j
  exact BatchEndpointLinks.output_at f word a (some j)

/-- Recover a position for every named occurrence using its identifier. The
surjectivity conclusion covers all occupied slots, including the empty case. -/
theorem positions (word : A ↪ (Fin m → Bool)) (out : RecordPins H m → Bool)
    (conserves : payloads out = Finset.univ.val.map word) :
    ∃ pos : A ↪ Fin H,
      (∀ i, out (i,none) = true ↔ i ∈ Set.range pos) ∧
      ∀ a j, out (pos a,some j) = word a j := by
  classical
  have hit (a : A) : ∃ i : occupied out, (fun j => out (i.val,some j)) = word a := by
    have mem : word a ∈ payloads out := by rw [conserves]; exact Multiset.mem_map.mpr ⟨a,Finset.mem_univ _,rfl⟩
    obtain ⟨i,hi,he⟩ := Multiset.mem_map.mp mem
    exact ⟨⟨i,hi⟩,he⟩
  choose f hf using hit
  have inj : Function.Injective f := by
    intro a b eqn
    exact word.injective ((hf a).symm.trans ((congrArg (fun z : occupied out => fun j => out (z.val,some j)) eqn).trans (hf b)))
  have card : Fintype.card A = Fintype.card (occupied out) := by
    simpa only [card_payloads,Multiset.card_map,←Finset.card_def,Finset.card_univ,
      Fintype.card_coe] using (congrArg Multiset.card conserves).symm
  have onto := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨inj,card⟩).2
  let pos : A ↪ Fin H := ⟨fun a => (f a).val,fun _ _ h => inj (Subtype.ext h)⟩
  refine ⟨pos,?_,fun a j => congrFun (hf a) j⟩
  intro i
  constructor
  · intro on
    obtain ⟨a,eq⟩ := onto ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,on⟩⟩
    exact ⟨a,congrArg Subtype.val eq⟩
  · rintro ⟨a,rfl⟩
    exact (Finset.mem_filter.mp (f a).property).2

/-- Canonical consecutive batches and their active units are determined by
the ordered list of occurrence numbers in each supergroup. -/
abbrev Batch {G : Type*} (count : G → ℕ) (B : ℕ) := CallPool.Batch count B
abbrev Unit {G : Type*} (count : G → ℕ) (B : ℕ) (s : Batch count B) := CallPool.Unit count B s

theorem batch_units {G : Type*} (count : G → ℕ) {B : ℕ} (pos : 0<B) (s : Batch count B) :
    Fintype.card (Unit count B s) ≤ B := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_embedding (CallPool.offset pos s)

theorem all_units {G : Type*} (count : G → ℕ) {B : ℕ} (pos : 0<B)
    (test : (g : G) → Fin (count g) → Prop) :
    (∀ s : Batch count B, ∀ a : Unit count B s, test s.1 a.val) ↔
      ∀ g a, test g a := by
  constructor
  · intro ok g a
    exact ok (CallPool.batchIndex pos g a) ⟨a,rfl⟩
  · intro ok s a
    exact ok s.1 a.val

end Hierarchy.TaggedShorterLinks

end
end OAI
