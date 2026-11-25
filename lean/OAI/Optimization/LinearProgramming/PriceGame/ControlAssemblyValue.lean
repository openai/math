import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialPackets

/-! Numeric assembly using the visible frame lengths. The output loops range over
an actual coordinate row and expert array, so their lengths are bounded on every input. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open Trial TrialExecution Moment

structure AssemblyFrame where
  experts : List PackedExpert
  input : NodeInput
  calls : List Completed
deriving Inhabited

def medianValue (xs : List ℚ) : ℚ :=
  TrialExecution.median fun i : Fin xs.length => xs[i]

def finalRows (r : ℕ) (x : AssemblyFrame) := x.calls.drop r

def outputWidth (r : ℕ) (x : AssemblyFrame) : ℕ :=
  ((finalRows r x).headD default).mapped.length

def priceAt (r : ℕ) (x : AssemblyFrame) (i : ℕ) : ℚ :=
  medianValue ((finalRows r x).map fun c => atD c.mapped i)

def scoreAt (r : ℕ) (x : AssemblyFrame) (e : ℕ) : ℕ :=
  if (atD x.experts e).level = x.input.level then
    rationalScore scaleQ sigmaQ (((x.calls.take r).map fun c => atD c.gains e).sum / (r : ℚ))
  else
    rationalScore scaleQ sigmaQ
      ((x.calls.map fun c => ((atD c.child.scores e : ℕ) : ℚ)).sum / ((2*r : ℕ) : ℚ))

def frameLog (r : ℕ) (x : AssemblyFrame) : List PackedProbe :=
  ((x.calls.take r).flatMap fun c =>
    ⟨x.input.level, c.baseline, x.input.history⟩ :: c.child.log) ++
    ((x.calls.drop r).flatMap fun c => c.child.log)

def assembleValue (r : ℕ) (x : AssemblyFrame) : PackedRound where
  prices := (List.range (outputWidth r x)).map (priceAt r x)
  scores := (List.range x.experts.length).map (scoreAt r x)
  log := frameLog r x

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
