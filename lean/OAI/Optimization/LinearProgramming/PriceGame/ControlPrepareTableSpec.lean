import OAI.Optimization.LinearProgramming.PriceGame.MarketFlowMachineModel
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialPackets

/-! The packed market and the trial read the same expert rows. The dummy option is
column zero, followed in order by every real good. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native
namespace PrepareTable

open Market.FlowMachine Trial

variable {m g : ℕ}

theorem map_range {α : Type} (n : ℕ) (f : ℕ → α) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro k _ _; simp

theorem map_roster {α β : Type} [Inhabited α] (xs : List α) (f : α → β) :
    xs.map f = List.ofFn (fun i : Fin xs.length => f (atD xs i.val)) := by
  apply List.ext_getElem
  · simp
  · intro k h _
    have hk : k < xs.length := by simpa using h
    simp [atD]

private theorem option_row {α : Type} (f : Option (Fin g) → α) :
    List.ofFn (fun j : Fin (g+1) => f (finSuccEquiv g j)) =
      f none :: List.ofFn (fun i : Fin g => f (some i)) := by
  rw [List.ofFn_succ]
  simp

/-- Row-by-row construction of any expert-dependent cell table, including the outside option. -/
theorem roster_cells {α β : Type} [Inhabited α] (xs : List α) (g : ℕ)
    (f : α → Option (Fin g) → β) (d : α → β) (real : α → ℕ → β)
    (hn : ∀ x, f x none = d x) (hs : ∀ x i, f x (some i) = real x i.val) :
    (xs.map (fun x => d x :: (List.range g).map (real x))).flatten =
      packedCells (fun (e : Fin xs.length) (o : Option (Fin g)) => f (atD xs e.val) o) := by
  rw [map_roster,Rows.packedCells_eq_flatten]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext e
  rw [option_row, hn, map_range]
  simp only [hs]

/-- The packed word read at column `j+1` omits the outside option in each expert row. -/
theorem real_cells (f : Fin m → Option (Fin g) → ℚ) :
    (List.range m).map (fun e => (List.range g).map fun i =>
      atD (packedCells f) (e*(g+1)+(i+1))) =
        List.ofFn (fun e => List.ofFn fun i => f e (some i)) := by
  rw [map_range]
  apply congrArg List.ofFn
  funext e
  rw [map_range]
  apply congrArg List.ofFn
  funext i
  have h := Rows.read_packedCells (default : ℚ) f e (some i)
  simpa [Rows.read, atD] using h

end PrepareTable
end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
