import OAI.Computability.BorderVNP.PackedHistoryDenseProgram
import OAI.Computability.BorderVNP.PackedHistoryCorrect

/-! # Actual public histogram words on the sorted adaptive layouts -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.Program

open Cover Crossing Packing BankCircuit Shortening Shortening.Adaptive Physical
open scoped Classical

variable {D m k b : ℕ} [NeZero D] {K : Type*} [Field K] {I P : Type} [Fintype I]
    {bits : P → ℕ} {A : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
    {e : PaidIdentity K D m}
    {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    (F : Normalized.Program (B := B) e view) {w : ℕ → ℕ}

/-- Every sorted interval allocator can represent its matched block count in its public word. -/
def Fits (w : ℕ → ℕ) : Prop := ∀ i c a, (F.stage i c).matched a < 2^w i.val

/-- Counts measured before stable sorting suffice for the same word room. -/
theorem fits_of_counts (hm : 0 < m) (room : ∀ i c a, SeedIntervals.count
    (raw (fun j => view i.val (c j))).layout (F.stage i c).bin a < 2^w i.val) : F.Fits w := by
  intro i c a
  rw [Stage.matched_eq]
  exact (CombiningStep.blocks_le_donor _ _ _ hm a).trans_lt (room i c _)

/-- An accepted histogram on the sorted physical source names precisely one attained term. -/
noncomputable def indices (room : F.Fits w) (i : Fin b) (c : Fin k → A i.val) :
    {u : HistogramBits e (A := Seed I B depth i) (w i.val) // Accepted e (F.stage i c).matched u} ≃
      (F.system.choose i.val i.isLt c).Index :=
  branches e (F.stage i c).matched (room i c)

/-- The fixed-slot local encoder of the dense-before-cut system. -/
noncomputable def codec (room : F.Fits w) : Codec F.system (Pin I B depth e.count w) where
  word j h c q := (fields (B := B) (depth := depth) (I := I) (e := e) w ⟨j,h⟩).symm
    ((F.indices room ⟨j,h⟩ c).symm q).val
  injective j h c := (fields (B := B) (depth := depth) (I := I) (e := e) w ⟨j,h⟩).symm.injective.comp
    (Subtype.val_injective.comp (F.indices room ⟨j,h⟩ c).symm.injective)

/-- The static encoded count at every seed and identity term is the physical count used
by the selected replacement. This equality drives every successor serializer. -/
theorem word_count (room : F.Fits w) (i : Fin b) (c : Fin k → A i.val)
    (q : (F.system.choose i.val i.isLt c).Index) (a : Seed I B depth i) (t : Fin e.count) :
    (q a).val t = ParseBatchSort.value (fields (e := e) w i ((F.codec room).word i.val i.isLt c q) a t) := by
  let E := F.indices room i c
  let u := E.symm q
  have hq := branches_count e (F.stage i c).matched (room i c) u a t
  change (E u a).val t = _ at hq
  rw [show E u = q from E.apply_symm_apply q] at hq
  let f := fields (e := e) (B := B) (depth := depth) (I := I) w i
  change (q a).val t = ParseBatchSort.value (f (f.symm u.val) a t)
  rwa [f.apply_symm_apply]

/-- The exact image of the public count encoder is the predicate tested by the physical
bank circuit after the disjoint input cable rows are sorted. -/
theorem word_image (room : F.Fits w) (i : Fin b) (c : Fin k → A i.val) (g : Pin I B depth e.count w i.val → Bool) :
    (∃ q, g = (F.codec room).word i.val i.isLt c q) ↔
      Accepted e (F.stage i c).matched (fields (e := e) w i g) := by
  let E := F.indices room i c
  let f := fields (e := e) (B := B) (depth := depth) (I := I) w i
  constructor
  · rintro ⟨q,rfl⟩
    change Accepted e (F.stage i c).matched (f (f.symm (E.symm q).val))
    rw [f.apply_symm_apply]
    exact (E.symm q).property
  · intro h
    let u : {v // Accepted e (F.stage i c).matched v} := ⟨f g,h⟩
    refine ⟨E u,?_⟩
    change g = f.symm (E.symm (E u)).val
    rw [E.symm_apply_apply]
    exact (f.symm_apply_apply g).symm

/-- Local correctness of a checked physical pass is reduced to its real bank guard and
its physical row representation under the matching count values. No equality of layouts
from different interval orders is required. -/
theorem checked_local {W : ℕ → Type} [∀ j, Fintype (W j)] (room : F.Fits w)
    (rep : Represents A W) (steps : Steps k b W (Pin I B depth e.count w))
    (guard : ∀ (i : Fin b) (c : Fin k → A i.val) (y : Fin k → W i.val → Bool)
      (g : Pin I B depth e.count w i.val → Bool), (∀ j, rep i.val (y j) (c j)) →
      ((steps i.val i.isLt).eval (Sum.elim (fun p => y p.1 p.2) g) (.inr ()) = true ↔
        Accepted e (F.stage i c).matched (fields (e := e) w i g)))
    (rows : ∀ (i : Fin b) (c : Fin k → A i.val) (y : Fin k → W i.val → Bool)
      (g : Pin I B depth e.count w i.val → Bool) (q : (F.stage i c).Index e),
      (∀ j, rep i.val (y j) (c j)) →
      (∀ a t, (q a).val t = ParseBatchSort.value (fields (e := e) w i g a t)) →
      rep (i.val+1) ((steps i.val i.isLt).eval (Sum.elim (fun p => y p.1 p.2) g) ∘ Sum.inl)
        (F.advance i c q)) :
    LocalCorrect (F.codec room) rep steps where
  valid j h c y g hy := (guard ⟨j,h⟩ c y g hy).trans (F.word_image room ⟨j,h⟩ c g).symm
  next j h c y g q hy he := by
    subst g
    exact rows ⟨j,h⟩ c y _ q hy (F.word_count room ⟨j,h⟩ c q)

end PackedHistoryCircuit.Normalized.Program

end BorderVNP
end Computability
end OAI
