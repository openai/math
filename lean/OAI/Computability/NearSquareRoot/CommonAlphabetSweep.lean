import OAI.Computability.NearSquareRoot.CommonAlphabetMachine

/-! # Building a physical trace of a block sweep from its individual transitions -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet
open IntegerMultiplication
variable {G P I : Type}

theorem sweep (m : TM.Rule G P I) (n : ℕ) (stage : ℕ → P)
    (Inv : ℕ → (I → TM.Tape G) → Prop) (S : I → TM.Tape G) (start : Inv 0 S)
    (step : ∀ j, j < n → ∀ T, Inv j T → ∃ T',
      TM.advance m ⟨stage j,T⟩ = some ⟨stage (j+1),T'⟩ ∧ Inv (j+1) T') :
    ∃ T', Trace (TM.advance m) ⟨stage 0,S⟩ n ⟨stage n,T'⟩ ∧ Inv n T' := by
  suffices h : ∀ j ≤ n, ∃ T', Trace (TM.advance m) ⟨stage 0,S⟩ j ⟨stage j,T'⟩ ∧ Inv j T' from
    h n le_rfl
  intro j hj
  induction j with
  | zero => exact ⟨S, .nil _, start⟩
  | succ j ih =>
    obtain ⟨T,run,hT⟩ := ih (by omega)
    obtain ⟨T',next,hT'⟩ := step j (by omega) T hT
    exact ⟨T',run.trans (.single next),hT'⟩

theorem sweepAt {w : ℕ} (hw : 0 < w) (m : TM.Rule G P I) (stage : Fin w → P) (done : P)
    (Inv : ℕ → (I → TM.Tape G) → Prop) (S : I → TM.Tape G) (start : Inv 0 S)
    (step : ∀ j : Fin w, ∀ T, Inv j.val T → ∃ T',
      TM.advance m ⟨stage j,T⟩ = some ⟨atIndex w stage done (j.val+1),T'⟩ ∧ Inv (j.val+1) T') :
    ∃ T', Trace (TM.advance m) ⟨stage ⟨0,hw⟩,S⟩ w ⟨done,T'⟩ ∧ Inv w T' := by
  have h := sweep m w (atIndex w stage done) Inv S start fun j hj T hT => by
    simpa only [atIndex, hj, ↓reduceDIte] using step ⟨j,hj⟩ T hT
  simpa only [atIndex, hw, ↓reduceDIte, Nat.lt_irrefl] using h

end CommonAlphabet

end NearSquareRoot
end Computability
end OAI
