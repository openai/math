import OAI.Computability.NearSquareRoot.InterchangeROMStageTableCoverage
import OAI.Computability.NearSquareRoot.InterchangeROMStageMoves

/-! # Intermediate semantic banks of the eleven-stage rectangle script -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace InterchangeROMStage.Frame.Realization
open Interchange StageRoute StageScript InterchangeROMStageTable InterchangeROMRepair

variable {g : Frame} (r : Realization g) {X : Type}

/-- Input boundaries of the six movement instructions. -/
def routePos : Fin 6 → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 5
  | 4 => 7
  | 5 => 9

def srcAt : (k : Fin 6) → r.Boundary (routePos k+1) → r.Boundary (routePos k)
  | 0 => Sum.elim id Sigma.fst
  | 1 => Sum.map id Prod.snd
  | 2 => Sum.elim id (fun (j,t) => gatherFrom r.rect (r.sel true) j t)
  | 3 => Sum.map id (fun (j,t) => (j,t.1))
  | 4 => Sum.map id (fun (j,e) => (j,e.2.1))
  | 5 => id

def moveAt : (k : Fin 6) → r.Boundary (routePos k+1) → r.NativeMove
  | 0 => Sum.elim (fun _ => .idle) .prepare
  | 1 => Sum.elim (fun _ => .idle) (fun (j,e) => .align j e)
  | 2 => Sum.elim (fun _ => .idle) (fun (j,t) => .gather j t)
  | 3 => Sum.elim (fun _ => .idle) (fun (j,t) => .distribute j t)
  | 4 => Sum.elim (fun _ => .idle) (fun (j,e) => .unalign j e)
  | 5 => Sum.elim (fun _ => .idle) .restore

theorem correctRoute_at (k : Fin 6) : r.CorrectRoute (routePos k) (r.srcAt k) (r.moveAt k) := by
  fin_cases k
  · exact r.prepare_correct
  · exact r.align_correct
  · exact r.gather_correct
  · exact r.distribute_correct
  · exact r.unalign_correct
  · exact r.restore_correct

variable (p lanes : ℕ) [Fact p.Prime]
  (minor base : ℕ → ℕ → ℕ) (query : ℕ → ℕ → ℕ → ℕ)

private def wideGate :
    (tag : Fin 5) → (r.Boundary (inputBoundary tag) → Fin lanes → ZMod p) →
        r.Boundary (inputBoundary tag+1) → Fin lanes → ZMod p
  | 0 => partialTable r.rect
  | 1 => mixTable r.rect (r.sel true) (fun i k : Fin r.rank => (minor i k : ZMod p))
  | 2 => scatterTable r.rect (r.sel false)
  | 3 => sumQueries r.rect (mixerMap (fun i k : Fin lanes => (base i k : ZMod p)))
      (fun q : Fin g.queries => mixerMap (fun i k : Fin lanes => (query q i k : ZMod p)))
  | 4 => finishTable r.rect

private theorem wideGate_eq (tag : Fin 5) :
    r.wideGate p lanes minor base query tag = gateNative r p lanes minor base query tag := by
  funext v k d
  fin_cases tag
  · rcases k with k|⟨j,b⟩
    · rfl
    · exact Finset.sum_apply ..
  · rcases k with k|⟨j,i⟩
    · rfl
    · simp [wideGate,gateNative,mixTable,applyRows,Finset.sum_apply,mul_add]
  · rcases k with (v'|⟨j,w⟩)|⟨j,b⟩
    · rfl
    · simp [wideGate,gateNative,scatterTable,Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : w = r.sel false k <;> simp [h]
    · simp [wideGate,gateNative,scatterTable,Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : r.sel false k ∈ (r.rect b).sources <;> simp [h]
  · rfl
  · simp [wideGate,gateNative,finishTable,Finset.sum_apply]

private def pull (π : r.NativeMove → Equiv.Perm X) (k : Fin 6)
    (v : r.Boundary (routePos k) → X → Fin lanes → ZMod p)
    (u : r.Boundary (routePos k+1)) (a : X) :=
  v (r.srcAt k u) ((π (r.moveAt k u)).symm a)

private def point (tag : Fin 5) (v : r.Boundary (inputBoundary tag) → X → Fin lanes → ZMod p)
    (u : r.Boundary (inputBoundary tag+1)) (a : X) :=
  r.wideGate p lanes minor base query tag (fun k => v k a) u

variable (π : r.NativeMove → Equiv.Perm X) (data : Fin g.labels → X → Fin lanes → ZMod p)

private def transition : (n : ℕ) → (r.Boundary n → X → Fin lanes → ZMod p) →
      r.Boundary (n+1) → X → Fin lanes → ZMod p
  | 0 => r.pull p lanes π 0
  | 1 => r.pull p lanes π 1
  | 2 => r.point p lanes minor base query 0
  | 3 => r.pull p lanes π 2
  | 4 => r.point p lanes minor base query 1
  | 5 => r.pull p lanes π 3
  | 6 => r.point p lanes minor base query 2
  | 7 => r.pull p lanes π 4
  | 8 => r.point p lanes minor base query 3
  | 9 => r.pull p lanes π 5
  | 10 => r.point p lanes minor base query 4
  | _+11 => id

/-- Native values in the twelve boundary banks. -/
def states : (n : ℕ) → r.Boundary n → X → Fin lanes → ZMod p :=
  Nat.rec (motive:=fun n => r.Boundary n → X → Fin lanes → ZMod p) data
    (r.transition p lanes minor base query π)

@[simp] theorem states_initial : r.states p lanes minor base query π data 0 = data := rfl

theorem states_route (k : Fin 6) (u : r.Boundary (routePos k+1)) (a : X) :
    r.states p lanes minor base query π data (routePos k+1) u a =
      r.states p lanes minor base query π data (routePos k) (r.srcAt k u) ((π (r.moveAt k u)).symm a) := by
  fin_cases k <;> rfl

theorem states_gate (tag : Fin 5) (u : r.Boundary (inputBoundary tag+1)) (a : X) :
    r.states p lanes minor base query π data (inputBoundary tag+1) u a =
      gateNative r p lanes minor base query tag
        (fun k => r.states p lanes minor base query π data (inputBoundary tag) k a) u := by
  rw [← r.wideGate_eq]
  fin_cases tag <;> rfl

/-- At exit this trajectory is precisely the grouped mathematical stage. -/
theorem states_final :
    r.states p lanes minor base query π data 11 =
      eval π (stage r.rect (r.sel true) (r.sel false)
        (fun i k : Fin r.rank => (minor i k : ZMod p))
        (mixerMap (fun i k : Fin lanes => (base i k : ZMod p)))
        (fun q : Fin g.queries => mixerMap (fun i k : Fin lanes => (query q i k : ZMod p)))) data := rfl

end InterchangeROMStage.Frame.Realization

end

end NearSquareRoot
end Computability
end OAI
