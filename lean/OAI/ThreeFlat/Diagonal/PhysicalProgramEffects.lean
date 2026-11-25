import OAI.ThreeFlat.Diagonal.PhysicalTotals
import OAI.ThreeFlat.Diagonal.PhysicalBlockSchedule

namespace OAI
/-! # Energy and site counts along the chronological physical program -/

namespace ThreeFlat.Diagonal.PhysicalStage

open scoped Classical
noncomputable section
variable {F : Type} [Field F]

def Program.effects (cost : ShrinkMotif.Table F → ℕ → ℕ → ℝ) :
    {s : ℕ} → Program F s → List Effect
  | _, .done _ => []
  | _, .shrink s t T _ tail => ⟨126/127,max 0 (cost T s (2^t)),true⟩ :: effects cost tail
  | _, .refresh _ _ h pad _ _ C T _ _ _ _ _ _ _ tail =>
    ⟨max 0 ((1+h+pad:ℕ) + 2*C : ℝ),T.error,false⟩ :: effects cost tail

@[simp] theorem Program.effects_cast (cost : ShrinkMotif.Table F → ℕ → ℕ → ℝ) {a b : ℕ}
    (e : a=b) (P : Program F a) : Program.effects cost (e ▸ P : Program F b) = P.effects cost := by
  cases e
  rfl

/-- A property holds at the end of every admitted sequence of real histogram choices. -/
def Run.AllLeaves (post : ℝ → ℕ → Prop) : {d l : ℕ} → {A : State d l} → Run F A → Prop
  | _, _, _, .done A => post A.energy A.positions
  | _, _, _, .step _ next => ∀ i, (next i).AllLeaves post

theorem Run.allLeaves_mono (post post' : ℝ → ℕ → Prop)
    (h : ∀ e n, post e n → post' e n) {d l : ℕ} {A : State d l} (r : Run F A) :
    r.AllLeaves post → r.AllLeaves post' := by
  induction r with
  | done A => exact h _ _
  | step R next ih => exact fun p i => ih i (p i)

@[simp] theorem Program.allLeaves_recast (post : ℝ → ℕ → Prop) {d l l' : ℕ}
    (e : l=l') (A : State d l) (r : Run F (e ▸ A : State d l')) :
    (recast e A r).AllLeaves post ↔ r.AllLeaves post := by
  cases e
  rfl

@[simp] theorem State.energy_cast_lanes {d l l' : ℕ} (e : l=l') (A : State d l) :
    (e ▸ A : State d l').energy = A.energy := by cases e; rfl

@[simp] theorem State.positions_cast_lanes {d l l' : ℕ} (e : l=l') (A : State d l) :
    (e ▸ A : State d l').positions = A.positions := by cases e; rfl

theorem Move.map_bound_degree {d l D D' L : ℕ} {A : State d l} (e : D = D') (R : Move F A D L)
    (p : ℝ → ℕ → Prop) (all : ∀ i,p (R.next i).energy (R.next i).positions) :
    ∀ i,p (((Program.recastMove e R).next i).energy) (((Program.recastMove e R).next i).positions) := by
  cases e
  exact all

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
