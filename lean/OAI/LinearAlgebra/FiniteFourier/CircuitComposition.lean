import OAI.LinearAlgebra.FiniteFourier.CircuitLinearity

/-!
# Composition and shared inputs for binary linear circuits

Readouts, including zero readouts, can be substituted into later gates.
The old registers remain available throughout the simulation.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {K I J O P : Type*}

section Semiring

variable [Semiring K]

/-- A freely readable scalar-valued function of the inputs. -/
def Available {r : ℕ} (p : Program K I r) (f : (I → K) → K) : Prop :=
  ∃ z : Readout K (I ⊕ Fin r), ∀ x, z.eval (Sum.elim x (p.value x)) = f x

private theorem available_step {r : ℕ} {p : Program K I r} (g : BinaryGate K (I ⊕ Fin r))
    {f : (I → K) → K} (hf : Available p f) : Available (p.step g) f := by
  obtain ⟨z, hz⟩ := hf
  cases z with
  | zero => exact ⟨.zero, hz⟩
  | scaled c w =>
    cases w with
    | inl i => exact ⟨.scaled c (.inl i), hz⟩
    | inr j => exact ⟨.scaled c (.inr j.succ), hz⟩

private theorem available_scale {r : ℕ} {p : Program K I r} {f : (I → K) → K}
    (c : K) (hf : Available p f) : Available p (fun x => c * f x) := by
  obtain ⟨z, hz⟩ := hf
  cases z with
  | zero => exact ⟨.zero, fun x => by simp [← hz x, Readout.eval]⟩
  | scaled d w => exact ⟨.scaled (c * d) w, fun x => by simp [← hz x, Readout.eval, mul_assoc]⟩

theorem available_combine {r : ℕ} (p : Program K I r)
    {f g : (I → K) → K} (a b : K) (hf : Available p f) (hg : Available p g) :
    ∃ n ≤ r + 1, ∃ q : Program K I n, (∀ u, Available p u → Available q u) ∧
      Available q (fun x => a * f x + b * g x) := by
  obtain ⟨z, hz⟩ := hf
  obtain ⟨w, hw⟩ := hg
  cases z with
  | zero =>
    refine ⟨r, Nat.le_succ _, p, fun _ h => h, ?_⟩
    simpa only [← hz, Readout.eval, mul_zero, zero_add] using available_scale b ⟨w, hw⟩
  | scaled c i =>
    cases w with
    | zero =>
      refine ⟨r, Nat.le_succ _, p, fun _ h => h, ?_⟩
      simpa only [← hw, Readout.eval, mul_zero, add_zero] using available_scale a ⟨.scaled c i, hz⟩
    | scaled d j =>
      let gate : BinaryGate K (I ⊕ Fin r) := ⟨i, j, a * c, b * d⟩
      exact ⟨r + 1, le_rfl, p.step gate, fun _ h => available_step gate h,
        .scaled 1 (.inr 0), fun x => by simp [← hz x, ← hw x, Readout.eval,
          Program.value, BinaryGate.eval, gate, mul_assoc]⟩

/-- Append the second program, given a free readout for each of its input values. -/
private theorem simulate {s t : ℕ} (p : Program K I s) (q : Program K J t)
    (y : (I → K) → J → K) (hin : ∀ j, Available p (fun x => y x j)) :
    ∃ n ≤ s + t, ∃ r : Program K I n, (∀ u, Available p u → Available r u) ∧
      (∀ w : J ⊕ Fin t, Available r (fun x => Sum.elim (y x) (q.value (y x)) w)) := by
  induction q with
  | nil =>
    refine ⟨s, le_rfl, p, fun _ h => h, ?_⟩
    rintro (j | j)
    · exact hin j
    · exact j.elim0
  | @step t q g ih =>
    obtain ⟨m, hm, r, hkeep, hav⟩ := ih
    obtain ⟨n, hn, r', hkeep', hnew⟩ := available_combine r g.leftCoeff g.rightCoeff
      (hav g.left) (hav g.right)
    refine ⟨n, by omega, r', fun u h => hkeep' u (hkeep u h), ?_⟩
    rintro (j | j)
    · exact hkeep' _ (hkeep _ (hin j))
    · refine Fin.cases ?_ (fun k => ?_) j
      · exact hnew
      · exact hkeep' _ (hav (.inr k))

private theorem available_output {t n : ℕ} {r : Program K I n} {q : Program K J t}
    {y : (I → K) → J → K}
    (h : ∀ w : J ⊕ Fin t, Available r (fun x => Sum.elim (y x) (q.value (y x)) w))
    (z : Readout K (J ⊕ Fin t)) :
    Available r (fun x => z.eval (Sum.elim (y x) (q.value (y x)))) := by
  cases z with
  | zero => exact ⟨.zero, fun _ => rfl⟩
  | scaled c w => exact available_scale c (h w)

/-- Serial execution of two arbitrary circuits costs at most their combined sizes. -/
theorem circuit_comp {s t : ℕ} (p : Circuit K I J s) (q : Circuit K J O t) :
    ∃ n ≤ s + t, ∃ r : Circuit K I O n, ∀ x, r.eval x = q.eval (p.eval x) := by
  obtain ⟨n, hn, r, _, hv⟩ := simulate p.program q.program p.eval
    (fun j => ⟨p.output j, fun _ => rfl⟩)
  choose z hz using fun o => available_output hv (q.output o)
  exact ⟨n, hn, ⟨r, z⟩, fun x => funext fun o => hz o x⟩

/-- Execute two circuits on shared inputs while retaining all outputs. -/
theorem circuit_fanout {s t : ℕ} (p : Circuit K I O s) (q : Circuit K I P t) :
    ∃ n ≤ s + t, ∃ r : Circuit K I (O ⊕ P) n, ∀ x, r.eval x = Sum.elim (p.eval x) (q.eval x) := by
  obtain ⟨n, hn, r, hk, hv⟩ := simulate p.program q.program id
    (fun j => ⟨.scaled 1 (.inl j), fun x => by simp [Readout.eval]⟩)
  choose z₁ hz₁ using fun o => hk (fun x => p.eval x o) ⟨p.output o, fun _ => rfl⟩
  choose z₂ hz₂ using fun o => available_output hv (q.output o)
  refine ⟨n, hn, ⟨r, Sum.elim z₁ z₂⟩, fun x => funext fun o => ?_⟩
  cases o with
  | inl j => exact hz₁ j x
  | inr j => exact hz₂ j x

end Semiring

variable [Semiring K]

/-- Matrix multiplication is realized by serial circuit composition. -/
theorem RealizableAtMost.mul [Fintype J] {M : Matrix O J K} {N : Matrix J I K}
    {s t : ℕ} (hM : RealizableAtMost M s) (hN : RealizableAtMost N t) :
    RealizableAtMost (M * N) (s + t) := by
  classical
  obtain ⟨t', ht, p, rfl⟩ := hN
  obtain ⟨s', hs, q, rfl⟩ := hM
  obtain ⟨n, hn, r, he⟩ := circuit_comp p q
  refine ⟨n, by omega, r, ?_⟩
  ext o i
  change r.eval (Pi.single i 1) o = _
  rw [he, q.eval_eq_mulVec]
  rfl

end FiniteFourier
end LinearAlgebra
end OAI
