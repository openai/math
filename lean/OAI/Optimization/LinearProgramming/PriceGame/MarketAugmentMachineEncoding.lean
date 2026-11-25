import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentMachineStep
import OAI.Optimization.LinearProgramming.PriceGame.MarketFlowMachineModel
import OAI.Optimization.LinearProgramming.PriceGame.MarketActionsMachine

/-! The flow, dual banks and expert address at each step of the market machine. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace Augment
namespace Machine

open OAI.Optimization.LinearProgramming.PriceGame.Market.Graph Potentials NumberBounds
variable {m g : ℕ}

def packBanks (n : Network (Fin m) (Fin g)) (D : ℕ) (π : Vertex n → ℚ) : Banks :=
  (List.ofFn (fun e => Grid.scaleInput D (π (.expert e))),
   List.ofFn (fun j : Fin (g+1) => Grid.scaleInput D (π (.opt (finSuccEquiv g j)))))

/-- The concrete state word uses a single denominator throughout the bit-scaling schedule. -/
def packEnv (I : Input m g) (D : ℕ) (s : State m g) : Environment :=
  let n := I.network s
  let raw := FlowMachine.Rows.encodeRaw n (I.decideAcceptance s) D (combine n s.pe s.po)
  (((D : ℤ), raw.1), raw.2)

abbrev actionNumber {m : ℕ} (a : Option (Fin m)) : ℕ := ScheduleMachine.actionNumber a

def packSeed (n : Network (Fin m) (Fin g)) (D : ℕ) (π : Vertex n → ℚ) (i : Fin m) : Seed :=
  (i.val, (List.ofFn n.pos, ((D : ℤ), packBanks n D π)))

theorem makeSeed_packEnv (I : Input m g) (D : ℕ) (s : State m g) (i : Fin m) :
    makeSeed (i.val, packEnv I D s) =
      packSeed (I.network s) D (combine (I.network s) s.pe s.po) i := rfl

theorem map_range_fin {α : Type*} (k : ℕ) (f : ℕ → α) :
    (List.range k).map f = List.ofFn (fun i : Fin k => f i.val) := by
  apply List.ext_getElem <;> simp

theorem horizon_pack (I : Input m g) (D : ℕ) (s : State m g) :
    horizon (packEnv I D s) = m+(g+1)-1 := by simp [horizon,packEnv,FlowMachine.Rows.encodeRaw]

end Machine
end Augment
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
