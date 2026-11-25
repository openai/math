import OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Reader

/-!
# Ordinary input bits beside ordered messages

The message bank occupies one address region. The other region holds
advice, guesses, exposed bits and scratch space. The upload uses one
write per ordinary input and does not enumerate the address space.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
open Coloring

namespace Scatter.Upload

variable {X I Z : Type} {w : ℕ}

private def lift (b : X ⊕ Bool) : (X ⊕ Z) ⊕ Bool := Sum.map Sum.inl id b

private theorem lift_read (x : X → Bool) (y : Z → Bool) (b : X ⊕ Bool) :
    Sum.elim (Sum.elim x y) id (lift b) = Sum.elim x id b := by cases b <;> rfl

def withInputs (u : Upload X I w) (loc : Z ↪ B w) : Upload (X ⊕ Z) (I ⊕ Z) w where
  address := Sum.elim (fun i b => lift (u.address i b))
    (fun z b => .inr ((Control.decode w).symm (loc z) b))
  enabled := Sum.elim (lift ∘ u.enabled) (fun _ => .inr true)
  source := Sum.elim (lift ∘ u.source) (fun z => .inl (.inr z))

private theorem withInputs_left (u : Upload X I w) (loc : Z ↪ B w) (x : X → Bool) (y : Z → Bool) (i : I) :
    (u.withInputs loc).addr (Sum.elim x y) (.inl i) = u.addr x i :=
  congrArg (Control.decode w) (funext fun b => lift_read x y (u.address i b))

private theorem withInputs_right (u : Upload X I w) (loc : Z ↪ B w) (x : X → Bool) (y : Z → Bool) (z : Z) :
    (u.withInputs loc).addr (Sum.elim x y) (.inr z) = loc z :=
  (Control.decode w).apply_symm_apply _

theorem withInputs_fits (u : Upload X I w) (loc : Z ↪ B w) (x : X → Bool) (y : Z → Bool)
    (m : B w → Bool) (hm : u.Fits x m)
    (apart : ∀ i, Sum.elim x id (u.enabled i) = true → u.addr x i ∉ Set.range loc) :
    (u.withInputs loc).Fits (Sum.elim x y) (Function.extend loc y m) where
  agrees := by
    rintro (i|z) hi
    · have h : Sum.elim x id (u.enabled i) = true := (lift_read x y _).symm.trans hi
      rw [withInputs_left, Function.extend_apply' _ _ _ (apart i h)]
      exact (hm.agrees i h).trans (lift_read x y _).symm
    · rw [withInputs_right, loc.injective.extend_apply]
      rfl
  covers := by
    intro a ha
    by_cases h : a ∈ Set.range loc
    · obtain ⟨z, rfl⟩ := h
      exact ⟨.inr z, rfl, withInputs_right u loc x y z⟩
    · rw [Function.extend_apply' _ _ _ h] at ha
      obtain ⟨i, hi, he⟩ := hm.covers a ha
      exact ⟨.inl i, (lift_read x y _).trans hi, (withInputs_left u loc x y i).trans he⟩

end Scatter.Upload

namespace Strings

theorem inputMemory_input {Z : Type} (A : Format) (k M : ℕ) (place : Z ↪ B (width A k M - 1))
    (z : Z → Bool) (m : B (width A k M) → Bool) (i : Z) :
    inputMemory A k M place z m (workspace A k M (place i)) = z i :=
  (place.trans (workspace A k M)).injective.extend_apply _ _ _

theorem inputMemory_message {Z : Type} (A : Format) (k M : ℕ) (place : Z ↪ B (width A k M - 1))
    (z : Z → Bool) (m : B (width A k M) → Bool) (i : (Position M).obj × (Body A k).pins) :
    inputMemory A k M place z m (address A k M i) = m (address A k M i) := by
  exact Function.extend_apply' _ _ _ (fun ⟨x, hx⟩ => workspace_ne A k M (place x) i hx)

/-- A single clocked program for every compatible message bank and every
assignment of advice, guess and exterior input bits. -/
theorem simulate_with_inputs (A : Format) (k M : ℕ) {Z Y : Type} [Fintype Z] [Fintype Y]
    (C : Controller Z Y (width A k M)) (place : Z ↪ B (width A k M - 1)) (j : ℕ) :
    let X := fun T => Bank A k M T ⊕ Z
    let t := fun T => clock (Fintype.card (Events A k M T) + Fintype.card Z) (Fintype.card Y) j C.size
    ∃ (P : (T : ℕ) → RAM.Program (X T) (t T) (width A k M) 4)
      (tap : (T : ℕ) → Y → RAM.Source (X T) (t T)),
      ∀ (I : Type) (n T : I → ℕ) (row : Rows A n) (p : Layout row M k T) (hm : ∀ i, n i ≤ M)
        (i : I) (z : Z → Bool) (y : Y),
        (P (T i)).eval (Sum.elim (bank row p hm i) z) (tap (T i) y) =
          ((C.cycle^[2 ^ j]) ⟨C.initial, inputMemory A k M place z (memory k M row i)⟩).mem (C.output y) := by
  intro X t
  let loc := place.trans (workspace A k M)
  have go (T : ℕ) : ∃ (P : RAM.Program (X T) (t T) (width A k M) 4)
      (tap : Y → RAM.Source (X T) (t T)),
      ∀ x m, ((upload A k M T).withInputs loc).Fits x m → ∀ y,
        P.eval x (tap y) = ((C.cycle^[2 ^ j]) ⟨C.initial, m⟩).mem (C.output y) := by
    dsimp only [X, t]
    rw [← Fintype.card_sum]
    exact Scatter.simulate ((upload A k M T).withInputs loc) C j
  choose P tap good using go
  refine ⟨P, tap, fun _ _ _ row p hm i z y => good _ _ _ ?_ y⟩
  apply Scatter.Upload.withInputs_fits _ _ _ _ _ (sparse row p hm i)
  intro e _ he
  obtain ⟨v, hv⟩ := he
  obtain ⟨q, hq⟩ := write_in_range row p hm i e
  exact workspace_ne A k M (place v) q (hv.trans hq.symm)

end Strings
end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
