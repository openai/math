import OAI.Computability.IntegerMultiplication.Port.Lag
import OAI.Computability.NearSquareRoot.InterchangeStar

/-!
# Performing an aligned transvection batch using controlled shifts

Matrices act on columns. Thus the transvections of a matrix product are
executed from right to left. Spectator fields are allowed to be occupied.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

open IntegerMultiplication.Port Matrix

variable {I J : Type} [DecidableEq I] [DecidableEq J] [Fintype I] {p : ℕ}

/-- The prime-power specialization of an elementary address change. -/
def encodedTransvection (code : ℚ → Pinpoint p) (f : ℕ)
    (a : TransvectionStruct I ℚ) : Matrix I I (Tower p f) :=
  Matrix.transvection a.i a.j ((code a.c).stamp f)

/-- The physical additions for an assigned layout, in execution order. -/
def gatherProgram (slot : I → Spot J) (code : ℚ → Pinpoint p) :
    List (TransvectionStruct I ℚ) → List (Lag J p)
  | [] => []
  | a :: s => gatherProgram slot code s ++ [.gather (slot a.i) (slot a.j) (code a.c)]

omit [DecidableEq I] [DecidableEq J] [Fintype I] in
theorem gatherProgram_free (slot : I → Spot J) (rank : J → ℕ) (code : ℚ → Pinpoint p)
    (s : List (TransvectionStruct I ℚ))
    (h : ∀ a ∈ s, Lag.early rank (slot a.j) (slot a.i)) :
    (∀ a ∈ gatherProgram slot code s, a.legal rank) ∧
      ((gatherProgram slot code s).map Lag.prices).sum = 0 := by
  induction s with
  | nil => simp [gatherProgram]
  | cons a s ih =>
    obtain ⟨h₁,h₂⟩ := ih (fun b hb => h b (.tail _ hb))
    exact ⟨fun b hb => (List.mem_append.mp hb).elim (h₁ b) (fun hb => by
      have he : b = .gather (slot a.i) (slot a.j) (code a.c) := List.mem_singleton.mp hb
      subst b
      exact h a (.head ..)), by simp [gatherProgram, h₂, Lag.prices]⟩

/-- Along selected fields the executed shifts realize the specialized matrix
product; every field outside the layout retains its original contents. -/
theorem gatherProgram_effect (slot : I → Spot J) (inj : Function.Injective slot)
    (code : ℚ → Pinpoint p) (s : List (TransvectionStruct I ℚ)) (f : ℕ)
    (x : Duplex J (Tower p f)) :
    let y := (gatherProgram slot code s).foldl (Lag.fire f) x
    (∀ i : I, hear y (slot i) =
      (((s.map (encodedTransvection code f)).prod) *ᵥ (fun j => hear x (slot j))) i) ∧
    (∀ w, (∀ i, w ≠ slot i) → hear y w = hear x w) := by
  induction s with
  | nil => simp [gatherProgram]
  | cons a s ih =>
    obtain ⟨ih₁,ih₂⟩ := ih
    simp only [gatherProgram, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.map_cons, List.prod_cons]
    constructor
    · intro i
      rw [← Matrix.mulVec_mulVec, encodedTransvection, Matrix.transvection, Matrix.add_mulVec,
        Matrix.one_mulVec, Matrix.single_mulVec]
      by_cases he : i = a.i
      · subst i
        simp [Lag.fire, ih₁]
      · simp [Lag.fire, inj.ne he, he, ih₁, Function.update_of_ne]
    · intro w hw
      simpa [Lag.fire, hw] using ih₂ w hw

/-- Conjugate a gather program by a physical layout swap. The swap is
charged twice, irrespective of the length of the batch. -/
theorem gatherProgram_conjugate (slot : I → Spot J) (inj : Function.Injective slot)
    (rank : J → ℕ) (code : ℚ → Pinpoint p) (s : List (TransvectionStruct I ℚ))
    (a b : Spot J) (l : List (Lag J p)) (hl : ∀ v ∈ l, v.legal rank)
    (hc : (l.map Lag.prices).sum ≤ 3)
    (he : ∀ f (x : Duplex J (Tower p f)) w,
      hear (l.foldl (Lag.fire f) x) w = hear x (Equiv.swap a b w))
    (hord : ∀ t ∈ s, Lag.early rank (Equiv.swap a b (slot t.j)) (Equiv.swap a b (slot t.i))) :
    ∃ program : List (Lag J p), (∀ v ∈ program, v.legal rank) ∧
      (program.map Lag.prices).sum ≤ 6 ∧
      ∀ f (x : Duplex J (Tower p f)),
        let y := program.foldl (Lag.fire f) x
        (∀ i : I, hear y (slot i) =
          ((s.map (encodedTransvection code f)).prod *ᵥ (fun j => hear x (slot j))) i) ∧
        (∀ w, (∀ i, w ≠ slot i) → hear y w = hear x w) := by
  let σ := Equiv.swap a b
  let slot' := σ ∘ slot
  have hss (w : Spot J) : σ (σ w) = w := Equiv.swap_apply_self a b w
  obtain ⟨h₁,h₂⟩ := gatherProgram_free slot' rank code s hord
  refine ⟨l ++ gatherProgram slot' code s ++ l, ?_, ?_, ?_⟩
  · intro v hv
    rcases List.mem_append.mp hv with hv|hv
    · exact (List.mem_append.mp hv).elim (hl v) (h₁ v)
    · exact hl v hv
  · simp only [List.map_append, List.sum_append, h₂]
    omega
  · intro f x
    dsimp only
    rw [List.foldl_append, List.foldl_append]
    let z := l.foldl (Lag.fire f) x
    have hz : (fun i => hear z (slot' i)) = (fun i => hear x (slot i)) := by
      funext i
      exact (he f x (slot' i)).trans (congrArg (hear x) (hss (slot i)))
    obtain ⟨main, spec⟩ := gatherProgram_effect slot' (σ.injective.comp inj) code s f z
    rw [hz] at main
    constructor
    · intro i
      rw [he]
      exact main i
    · intro w hw
      rw [he]
      have eq : hear ((gatherProgram slot' code s).foldl (Lag.fire f) z) (σ w) =
          hear z (σ w) := spec (σ w) (fun i => σ.injective.ne (hw i))
      exact eq.trans ((he f x (σ w)).trans (congrArg (hear x) (hss w)))

end Interchange

end NearSquareRoot
end Computability
end OAI
