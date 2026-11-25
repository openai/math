import OAI.Optimization.LinearProgramming.PriceGame.ControlData
import OAI.Optimization.LinearProgramming.PriceGame.LearningPathMachine

/-! Canonical bit-stack encodings of the first-order trial data. Lists use one element
marker and one framed payload per entry. Product fields occur in declaration order. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure (boolCode)
open Learning.BitMachine (optionCode)

def packedQueryCode (q : PackedQuery) : List Bool :=
  prodCode (listCode ratCode) Nat.bits (q.prices, q.index)

def packedProbeCode (p : PackedProbe) : List Bool :=
  prodCode Nat.bits (prodCode (listCode ratCode) (listCode (listCode ratCode)))
    (p.level, p.prices, p.history)

def pivotCode : Option (ℕ × ℕ) → List Bool := optionCode (prodCode Nat.bits Nat.bits)

def packedExpertCode (e : PackedExpert) : List Bool :=
  prodCode Nat.bits (prodCode boolCode (prodCode (listCode Nat.bits)
    (prodCode pivotCode (listCode ratCode)))) (e.level,e.positive,e.tuple,e.pivot,e.raw)

def packedRoundCode (r : PackedRound) : List Bool :=
  prodCode (listCode ratCode) (prodCode (listCode Nat.bits) (listCode packedProbeCode))
    (r.prices,r.scores,r.log)

def packedPopulationCode (p : PackedPopulation) : List Bool :=
  prodCode (listCode packedExpertCode) (listCode ratCode) (p.experts,p.weights)

end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
