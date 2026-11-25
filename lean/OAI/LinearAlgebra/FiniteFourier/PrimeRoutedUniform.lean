import OAI.LinearAlgebra.FiniteFourier.PrimeTemplateProgram.PrimeRoutedProgram

/-! # Uniform linear local work across varying digit lengths -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {K : Type*} [CommSemiring K]

/-- Programs on fixed row banks with local work linear in the varying length of a row.
The gate constant and the call bound are common to all positive digit lengths. -/
def LinearRowTemplate (ℓ : ℕ) (F : ℕ → ℕ) (ζ : K) (X : ℕ → Type) [∀ f, Fintype (X f)]
    {D E : Type} (M : (f : ℕ) → Matrix (E × X f) (D × X f) K) (s : ℕ) : Prop :=
  ∃ C : ℕ, ∀ f : ℕ, 0 < f → ∃ c ≤ C * Fintype.card (X f), ∃ t ≤ s,
    PrimeTemplateProgram ℓ f (F f) ζ (M f) c t

namespace LinearRowTemplate

variable {ℓ : ℕ} {F : ℕ → ℕ} {ζ : K} {X : ℕ → Type} [∀ f, Fintype (X f)]
variable {D E H : Type} {M N : (f : ℕ) → Matrix (E × X f) (D × X f) K} {s t : ℕ}

theorem congr (h : LinearRowTemplate ℓ F ζ X M s) (hMN : ∀ f, M f = N f) :
    LinearRowTemplate ℓ F ζ X N s := funext hMN ▸ h

theorem mono (h : LinearRowTemplate ℓ F ζ X M s) (hst : s ≤ t) :
    LinearRowTemplate ℓ F ζ X M t := by
  obtain ⟨C, h⟩ := h
  refine ⟨C, fun f hf => ?_⟩
  obtain ⟨c, hc, a, ha, p⟩ := h f hf
  exact ⟨c, hc, a, ha.trans hst, p⟩

/-- Addition uses at most one extra gate per output coordinate. -/
theorem add [Fintype D] [Fintype E]
    (hM : LinearRowTemplate ℓ F ζ X M s) (hN : LinearRowTemplate ℓ F ζ X N t) :
    LinearRowTemplate ℓ F ζ X (fun f => M f + N f) (s + t) := by
  obtain ⟨C, hM⟩ := hM
  obtain ⟨B, hN⟩ := hN
  refine ⟨C + B + Fintype.card E, fun f hf => ?_⟩
  obtain ⟨a, ha, u, hu, p⟩ := hM f hf
  obtain ⟨b, hb, v, hv, q⟩ := hN f hf
  refine ⟨a + b + Fintype.card (E × X f), ?_, u + v, Nat.add_le_add hu hv, p.add q⟩
  rw [Nat.add_mul, Nat.add_mul, Fintype.card_prod]
  exact Nat.add_le_add_right (Nat.add_le_add ha hb) _

/-- Serial composition adds the uniform gate constants and the call bounds. -/
theorem serial [Fintype E] {P : (f : ℕ) → Matrix (H × X f) (E × X f) K}
    (hP : LinearRowTemplate ℓ F ζ X P t) (hM : LinearRowTemplate ℓ F ζ X M s) :
    LinearRowTemplate ℓ F ζ X (fun f => P f * M f) (t + s) := by
  obtain ⟨B, hP⟩ := hP
  obtain ⟨C, hM⟩ := hM
  refine ⟨B + C, fun f hf => ?_⟩
  obtain ⟨b, hb, v, hv, q⟩ := hP f hf
  obtain ⟨a, ha, u, hu, p⟩ := hM f hf
  exact ⟨b + a, (Nat.add_le_add hb ha).trans_eq (Nat.add_mul ..).symm, v + u,
    Nat.add_le_add hv hu, q.serial p⟩

/-- A finite collection of uniform programs can be summed with a new uniform constant. -/
theorem sum_finset {L : Type*} [Fintype D] [Fintype E] (u : Finset L)
    {A : L → (f : ℕ) → Matrix (E × X f) (D × X f) K} {s : L → ℕ}
    (h : ∀ l ∈ u, LinearRowTemplate ℓ F ζ X (A l) (s l)) :
    LinearRowTemplate ℓ F ζ X (fun f => ∑ l ∈ u, A l f) (∑ l ∈ u, s l) := by
  classical
  induction u using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨0, fun f _ => ⟨0, Nat.zero_le _, 0, le_rfl, .localCircuit ?_⟩⟩
    exact ⟨0, le_rfl, ⟨.nil, fun _ => .zero⟩, by ext; rfl⟩
  | @insert l u hl ih =>
    simpa [Finset.sum_insert hl] using
      (h l (Finset.mem_insert_self ..)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end LinearRowTemplate

end FiniteFourier
end LinearAlgebra
end OAI
