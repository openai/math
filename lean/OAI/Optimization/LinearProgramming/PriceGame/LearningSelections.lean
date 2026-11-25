import OAI.Optimization.LinearProgramming.PriceGame.LearningAdaptive
import OAI.Optimization.LinearProgramming.PriceGame.LearningExperts

/-! # Selecting the actually generated expert for the hidden integer assignment -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning

open Finset

namespace Selections

/-- Total table lookup for the cell of `z`. For hidden assignments in the box the
fallback is unreachable, as proved by `table_spec`. -/
def table {n} (R : ℕ) (a : Fin n) (s : Experts.Feature n → Finset ℚ) (z : Fin n → ℤ) :
    Paths.Table n :=
  (cellTable R a (Experts.trueObservations s fun i => (z i : ℚ))).getD
    (Paths.tabulate fun _ _ => 0)

theorem table_spec {n} {R : ℕ} {a : Fin n} {z : Fin n → ℤ} (s : Experts.Feature n → Finset ℚ)
    (ha : z a = 0) (hb : ∀ i, boxLower a i ≤ z i ∧ z i ≤ boxUpper R a i) :
    cellTable R a (Experts.trueObservations s fun i => (z i : ℚ)) = some (table R a s z) := by
  obtain ⟨t,ht⟩ := Experts.trueTable_exists R a s z ha hb
  simp [table,ht]

/-- This rational assignment is used only in the proof to identify a generated entry. -/
def selected {p} (R : ℕ) (a : Fin (p+1)) (s : Experts.Feature (p+1) → Finset ℚ)
    (z : Fin (p+1) → ℤ) : Fin (p+1) → ℚ := representative (Paths.read (table R a s z)) a

theorem selected_mem {p R : ℕ} {a : Fin (p+1)} {z : Fin (p+1) → ℤ}
    (s : Experts.Feature (p+1) → Finset ℚ) (ha : z a = 0)
    (hb : ∀ i, boxLower a i ≤ z i ∧ z i ≤ boxUpper R a i) :
    selected R a s z ∈ Experts.generate R a s :=
  Experts.trueTable_selected_mem_generate (table_spec s ha hb)

theorem selected_agrees {p R : ℕ} {a : Fin (p+1)} {z : Fin (p+1) → ℤ}
    (s : Experts.Feature (p+1) → Finset ℚ) (ha : z a = 0)
    (hb : ∀ i, boxLower a i ≤ z i ∧ z i ≤ boxUpper R a i)
    (f : Experts.Feature (p+1)) (θ : ℚ) (hθ : θ ∈ s f) :
    compare (selected R a s z f.1 - selected R a s z f.2) θ =
    compare ((z f.1 : ℚ) - (z f.2 : ℚ)) θ := by
  let o : Observation (p+1) := ⟨f.1,f.2,θ,compare ((z f.1 : ℚ) - (z f.2 : ℚ)) θ⟩
  have ho : o ∈ Experts.trueObservations s (fun i => (z i : ℚ)) :=
    (Experts.mem_trueObservations_iff _ _ _).mpr ⟨hθ,rfl⟩
  exact accepts_sound ((representative_inCell (table_spec s ha hb)).2.2 o ho)

/-- Exception count for thresholds and raw observations, with the actual representative
selected in the hidden cell. Feasibility of all successive compilations is derived from
the same integral hidden assignment. -/
theorem number_of_changes {S : Type*} [Fintype S] [DecidableEq S]
    (p : S → ℕ) (R T : ℕ) (hR : 0 < R) (a : ∀ s, Fin (p s + 1))
    (z : ∀ s, Fin (p s + 1) → ℤ) (ha : ∀ s, z s (a s) = 0)
    (hb : ∀ s i, boxLower (a s) i ≤ z s i ∧ z s i ≤ boxUpper R (a s) i)
    (seen : ∀ s, ℕ → Experts.Feature (p s+1) → Finset ℚ)
    (retain : ∀ s t, t < T → ∀ f, seen s t f ⊆ seen s (t+1) f)
    (charged : ℕ → S) (feature : ∀ t, Experts.Feature (p (charged t)+1)) (θ : ℕ → ℚ)
    (new : ∀ t, t < T → θ t ∈ seen (charged t) (t+1) (feature t))
    (wrong : ∀ t, t < T →
      let f := feature t
      let v := selected R (a (charged t)) (seen (charged t) t) (z (charged t))
      compare (v f.1 - v f.2) (θ t) ≠
        compare ((z (charged t) f.1 : ℚ) - (z (charged t) f.2 : ℚ)) (θ t)) :
    (T : ℝ) ≤ ∑ s : S, ((p s + 1 : ℕ) : ℝ)^2 *
      (1 + ((p s : ℝ) + 1) * Real.log (2*R)) := by
  let q (s : S) (i : Fin (p s+1)) : ℚ := z s i
  let os (s : S) (t : ℕ) := Experts.trueObservations (seen s t) (q s)
  let o (t : ℕ) : Observation (p (charged t)+1) :=
    ⟨(feature t).1,(feature t).2,θ t,compare (q (charged t) (feature t).1 - q (charged t) (feature t).2) (θ t)⟩
  apply adaptive_exception_bound p R T hR a os (fun s t => table R (a s) (seen s t) (z s))
    (fun s t => table_spec _ (ha s) (hb s))
    (fun s t ht => Experts.trueObservations_mono _ (retain s t ht)) charged o
  · intro t ht
    exact (Experts.mem_trueObservations_iff _ _ _).mpr ⟨new t ht,rfl⟩
  · exact wrong

end Selections

end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
