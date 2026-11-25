import OAI.ThreeFlat.Diagonal.PhysicalRecordFamily

namespace OAI
/-! # Final chronological depth of a selected physical run -/

namespace ThreeFlat.Diagonal.PhysicalStage
noncomputable section
variable {F : Type} [Field F]

namespace Run
def endLevel : {d l : ℕ} → {A : State d l} → (r : Run F A) → (h : r.plan.History) → ℕ → ℕ
  | _,_,_,.done _,_,depth=>depth
  | _,_,_,.step R next,h,depth=>(next h.1).endLevel (tailHistory R next h) (depth+1)

end Run

theorem Run.endLevel_stageLength {d l : ℕ} {X : State d l} (r : Run F X) (h : r.plan.History)
    (depth n : ℕ) (length : r.StageLength n) : r.endLevel h depth=depth+n := by
  induction r generalizing depth n with
  | done=>
    change n=0 at length
    simp [endLevel,length]
  | step R next ih=>
    cases n with
    | zero=>exact False.elim length
    | succ n=>
      exact (ih h.1 (tailHistory R next h) (depth+1) n (length h.1)).trans (by omega)

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
