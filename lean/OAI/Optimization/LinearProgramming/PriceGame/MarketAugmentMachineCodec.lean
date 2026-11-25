import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentMachineEncoding
import OAI.Optimization.LinearProgramming.PriceGame.MarketSolverBounds

/-! Encoding the terminal reward update at the selected expert. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace Augment
namespace Machine

open OAI.Optimization.LinearProgramming.PriceGame.Market.Graph Potentials NumberBounds
variable {m g : ℕ}

private theorem replace_ofFn {k : ℕ} (f : Fin k → ℤ) (i : Fin k) (z : ℤ) :
    replaceCell ((i.val,z),List.ofFn f) = List.ofFn (fun j => if j=i then z else f j) := by
  simp only [replaceCell, List.length_ofFn, map_range_fin]
  apply congrArg List.ofFn
  funext j
  change (if j.val = i.val then z else FlowMachine.Rows.read 0 (List.ofFn f) j.val) = _
  rw [FlowMachine.Rows.read_ofFn]
  simp only [Fin.val_inj]

variable (n : Network (Fin m) (Fin g)) (D : ℕ) (π : Vertex n → ℚ) (i : Fin m)

@[simp] theorem isSupply_packSeed : isSupply (packSeed n D π i) = n.pos i :=
  FlowMachine.Rows.read_ofFn false n.pos i

theorem sourceIndex_packSeed :
    sourceIndex (packSeed n D π i) = (vertexIndex n (start n i)).val := by
  rw [sourceIndex,isSupply_packSeed,FlowMachine.Rows.start_index]
  simp only [packSeed,List.length_ofFn]

theorem newTerminal_packSeed :
    newTerminal (packSeed n D π i) = Grid.scaleInput D (π (start n i)) + (D : ℤ) := by
  have he := FlowMachine.Rows.read_ofFn (0 : ℤ) (fun e => Grid.scaleInput D (π (.expert e))) i
  have ho := FlowMachine.Rows.read_ofFn (0 : ℤ)
    (fun j : Fin (g+1) => Grid.scaleInput D (π (.opt (finSuccEquiv g j)))) 0
  simp only [FlowMachine.Rows.read, Fin.val_zero, List.drop_zero, finSuccEquiv_zero] at he ho
  rw [newTerminal,isSupply_packSeed]
  cases h : n.pos i with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, packSeed, packBanks, start, h, ho]
  | true => simp only [↓reduceIte, packSeed, packBanks, start, h, he]

theorem scale_target (hD : 0 < D) (hg : ∀ v, OnGrid D (π v)) (v : Vertex n) :
    Grid.scaleInput D (targetReward n.weight π (direct n i).toPath v) =
      if v = finish n i then Grid.scaleInput D (π (start n i)) + (D : ℤ)
      else Grid.scaleInput D (π v) := by
  by_cases hv : v = finish n i
  · subst v
    rw [ite_eq_left rfl, targetReward_at, direct_cost, sub_zero, Grid.scaleInput_eq hD ((hg _).add (grid_one D)),
      Grid.scaleInput_eq hD (hg _), Grid.coordinate_add (hg _) (grid_one D)]
    simp [Grid.coordinate]
  · simp [targetReward, hv]

theorem terminalBanks_packSeed (hD : 0 < D) (hg : ∀ v, OnGrid D (π v)) :
    terminalBanks (packSeed n D π i) =
      packBanks n D (targetReward n.weight π (direct n i).toPath) := by
  have hr := scale_target n D π i hD hg
  cases h : n.pos i
  · simp only [terminalBanks, isSupply_packSeed, h, Bool.false_eq_true, ↓reduceIte, newTerminal_packSeed]
    change (replaceCell ((i.val,_),_),_) = _
    simp only [packSeed, packBanks, replace_ofFn]
    congr 1 <;> apply congrArg List.ofFn <;> funext j <;> rw [hr]
    · simp [start, finish, h]
    · simp [finish, h]
  · simp only [terminalBanks, isSupply_packSeed, h, ↓reduceIte, newTerminal_packSeed]
    simp only [packSeed, packBanks]
    rw [show (0 : ℕ) = (0 : Fin (g+1)).val from rfl, replace_ofFn]
    congr 1 <;> apply congrArg List.ofFn <;> funext j <;> rw [hr]
    · simp [finish, h]
    · simp [start, finish, h, finSuccEquiv_eq_none]

theorem makeRowsInput_packEnv (I : Input m g) (s : State m g) (i : Fin m) (D : ℕ)
    (hD : 0 < D) (hg : ∀ v, OnGrid D (combine (I.network s) s.pe s.po v)) :
    makeRowsInput (i.val,packEnv I D s) =
      FlowMachine.Rows.encodeRaw (I.network s) (I.decideAcceptance s) D
        (targetReward (I.network s).weight (combine (I.network s) s.pe s.po)
          (direct (I.network s) i).toPath) := by
  change (_,(_,terminalBanks (packSeed (I.network s) D _ i))) = (_,(_,packBanks (I.network s) D _))
  rw [terminalBanks_packSeed _ _ _ _ hD hg]
  rfl

end Machine
end Augment
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
