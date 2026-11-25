import OAI.ThreeFlat.Diagonal.PhysicalStage

namespace OAI
/-! # State observables at every stage of an admitted physical history -/

namespace ThreeFlat.Diagonal.PhysicalStage.Run
open HistoryContraction
noncomputable section
variable {F : Type} [Field F] {α : Type*}

def historyOfCast {X Y : Shape} (e : X=Y) (P : Plan F X)
    (h : (e ▸ P : Plan F Y).History) : P.History := by
  cases e
  exact h

def tailHistory {d l D L : ℕ} {A : State d l} (R : Move F A D L)
    (next : ∀ i,Run F (R.next i)) (h : (Run.step R next).plan.History) :
    (next h.1).plan.History :=
  historyOfCast (R.target_eq h.1).symm (next h.1).plan h.2

/-- Observations in chronological order, including input and terminal state. -/
def readStages (read : ∀ {d l : ℕ}, State d l → α) :
    {d l : ℕ} → {A : State d l} → (r : Run F A) → r.plan.History → List α
  | _, _, A, .done _, _ => [read A]
  | _, _, A, .step R next, h => read A :: (next h.1).readStages read (tailHistory R next h)

/-- The observable of the state whose graph is the terminal graph of the plan. -/
def readTerminal (read : ∀ {d l : ℕ}, State d l → α) :
    {d l : ℕ} → {A : State d l} → (r : Run F A) → r.plan.History → α
  | _, _, A, .done _, _ => read A
  | _, _, _, .step R next, h => (next h.1).readTerminal read (tailHistory R next h)

theorem terminal_shape {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) :
    r.readTerminal (fun X => X.shape) h = r.plan.finish h := by
  induction r with
  | done A => rfl
  | step R next ih =>
    change _ = ((R.target_eq h.1).symm ▸ (next h.1).plan : Plan F (R.rules.target h.1)).finish h.2
    rw [show (Run.step R next).readTerminal (fun X => X.shape) h =
        (next h.1).readTerminal (fun X => X.shape) (tailHistory R next h) from rfl,ih]
    have eq {X Y : Shape} (e : X=Y) (P : Plan F X) (g : (e ▸ P : Plan F Y).History) :
        P.finish (historyOfCast e P g) = (e ▸ P : Plan F Y).finish g := by cases e; rfl
    exact eq (R.target_eq h.1).symm _ _

theorem terminal_relation {β : Type*} (f : ∀ {d l}, State d l → α)
    (g : ∀ {d l}, State d l → β) (rel : α → β → Prop)
    (all : ∀ {d l} (A : State d l),rel (f A) (g A)) {d l : ℕ} {A : State d l}
    (r : Run F A) (h : r.plan.History) : rel (r.readTerminal f h) (r.readTerminal g h) := by
  induction r with
  | done A => exact all A
  | step R next ih => exact ih h.1 (tailHistory R next h)

end
end ThreeFlat.Diagonal.PhysicalStage.Run

end OAI
