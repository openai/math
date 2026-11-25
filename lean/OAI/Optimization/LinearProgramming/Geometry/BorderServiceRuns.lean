import OAI.Optimization.LinearProgramming.Geometry.BorderServiceHistory
import OAI.Optimization.LinearProgramming.Geometry.RecordedHistory

/-! Lift admissibility of the persistent service from typed histories to a physical scalar
oracle RAM execution. In particular one common extension fits every answer in an epoch. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open Contract OracleSpec OracleSpec.MinorLog RAM Matrix

variable {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}

theorem Follows.answers {o : ScalarOracle ℚ} {events : List (Index D E × Option ℚ)} (h : Follows o events) :
    answersMatch o (wireHistory events) := by
  induction h with
  | nil => trivial
  | append u q prev ret ih =>
    rw [wireHistory_snoc]
    exact ⟨ret.symm,ih⟩

theorem follows_of_answers {o : ScalarOracle ℚ} (events : List (Index D E × Option ℚ))
    (h : answersMatch o (wireHistory events)) : Follows o events := by
  induction events using List.reverseRecOn with
  | nil => exact .nil
  | append_singleton xs event ih =>
    obtain ⟨u,q⟩ := event
    rw [wireHistory_snoc] at h
    exact .append u q (ih h.2) h.1.symm

/-- A physical history remains a valid service interaction at every chronological prefix. -/
theorem Follows.prefix {o : ScalarOracle ℚ} (xs tail : List (Index D E × Option ℚ)) (h : Follows o (xs++tail)) :
    Follows o xs := by
  have good := h.answers
  have order : wireHistory (xs++tail)=wireHistory tail++wireHistory xs := by simp [wireHistory]
  rw [order] at good
  exact follows_of_answers xs (answersMatch_suffix o _ _ good)

/-- In a physical RAM run, the final encoded history alone identifies the typed service
run; the caller need not separately prove that every one of its returned answers is legal. -/
theorem follows_of_physical_run {p : OracleProgram} {o : ScalarOracle ℚ} {initial final : Config ℚ} {cost : ℕ}
    (run : OracleRun p o initial cost final) (old : answersMatch o initial.history)
    (events : List (Index D E × Option ℚ)) (wire : final.history=wireHistory events) : Follows o events :=
  follows_of_answers events (wire ▸ answersMatch_run run old)

/-- A complete finite caller run together with the service's persistent RAM calculations,
including the installation cost of every minor request and the complete height/epoch contract. -/
theorem Service.certify_execution (S : Service D E) {p : OracleProgram} {initial final : Config ℚ}
    {callerCost : ℕ} (run : OracleRun p S.oracle initial callerCost final)
    (initialGood : answersMatch S.oracle initial.history) (events : List (Index D E × Option ℚ))
    (wire : final.history=wireHistory events) :
    (∃ last serviceCost, ServiceTrace (fun u : Index D E => words u.val) S.program S.clock S.height
        S.outputBits S.ready events serviceCost last ∧
      callerCost+serviceCost ≤ callerCost+events.length*S.clock) ∧
    restartCount events ≤ S.restartBudget ∧
    ∀ j ≤ events.length, extension n S.outputBits (logarithm D E) (events.take j) := by
  obtain ⟨⟨t,k,hk,cap⟩,restart,model⟩ := (follows_of_physical_run run initialGood events wire).spec
  exact ⟨⟨t,k,hk,Nat.add_le_add_left cap callerCost⟩,restart,model⟩

private theorem agrees_with_answers {ι : Type} (f : ι → ℚ) (xs : List (ι × ℚ)) (past : List (ι × Option ℚ))
    (h : agreesSinceRestart f ((xs.map (fun e => (e.1,some e.2))).reverse++past)) :
    ∀e∈xs, f e.1=e.2 := by
  induction xs using List.reverseRecOn with
  | nil => simp
  | append_singleton xs a ih =>
    obtain ⟨u,q⟩ := a
    simp only [List.map_append,List.map_cons,List.map_nil,List.reverse_append,List.reverse_cons,
      List.reverse_nil,List.nil_append,List.cons_append,agreesSinceRestart] at h
    intro e he
    rcases List.mem_append.mp he with e₁ | e₂
    · exact ih h.2 _ e₁
    · obtain rfl := List.mem_singleton.mp e₂
      exact h.1

/-- After any history, the continuing replies since its most recent restart all belong
to one total rational assignment with the original magnitude and clipped four-term bounds. -/
theorem Follows.epoch {S : Service D E} (prior : List (Index D E × Option ℚ)) (new : List (Index D E × ℚ))
    (h : Follows S.oracle (prior++new.map (fun e => (e.1,some e.2)))) :
    ∃ f : Index D E → ℚ, (∀e∈new,f e.1=e.2) ∧
      (∀ u, |(f u : ℝ)| ≤ (2:ℝ)^S.outputBits) ∧
      ∀ a : Index D E →₀ ℤ, a.sum (fun _ c => c.natAbs) ≤ 4 →
        |clip (threshold n) (a.sum (fun u c => (c:ℝ)*(f u:ℝ))) -
          clip (threshold n) (a.sum (fun u c => (c:ℝ)*logarithm D E u))| ≤ (1/2:ℝ)^(threshold n) := by
  have final := h.spec.2.2 _ (Nat.le_refl _)
  rw [List.take_length] at final
  obtain ⟨f,fit,hmag,clip⟩ := final
  rw [List.reverse_append] at fit
  exact ⟨f,agrees_with_answers f new prior.reverse fit,hmag,clip⟩

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
