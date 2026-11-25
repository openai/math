import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialSourceNode

/-! Local proof obligations for invariants of all reachable numeric packet fields. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

open States.Mass Moment TrialExecution

/-- A completed prefix of the real dependent schedule. The source validator or
weight bound can inspect both the certified rows and the actual word-level trace. -/
structure SeenPrefix {N ne : ℕ} (r R : ℕ) (experts : Fin ne → Expert N)
    (c : SourceNode N ne) (k j : ℕ) where
  calls : Schedule (fun (n : ℕ) (xs : Fin n → Call N ne r c.level) a => StepOK experts c.weights xs a) j
  transcript : List (PackedQuery × Bool)
  observed : Emits (c.schedule r R experts k j) transcript calls

/-- All conditions are local to an actual source input, prefix, or child output.
The two user predicates may describe numeric size or a primitive's exact action. -/
structure SourceMarks {N ne : ℕ} (r R : ℕ) (experts : Fin ne → Expert N)
    (pcOK : PC NodeInput Prepared PackedRound Completed → Prop)
    (frameOK : Frame NodeInput Prepared Completed → Prop) where
  NodeGood : ℕ → SourceNode N ne → Prop
  enter : ∀ {k c}, NodeGood k c → pcOK (.enter k c.input)
  leaf : ∀ {c}, NodeGood 0 c → pcOK (.returned ((fixedKernel R r experts).leaf c.input))
  schedule : ∀ {k c j}, NodeGood (k+1) c → j ≤ 2*r → ∀ p : SeenPrefix r R experts c k j,
    pcOK (.schedule k (2*r-j) c.input (c.rows p.calls.val))
  frame : ∀ {k c j}, NodeGood (k+1) c → j < 2*r → ∀ p : SeenPrefix r R experts c k j,
    frameOK (c.frame R experts k (2*r-(j+1)) p.calls.val)
  child : ∀ {k c j}, NodeGood (k+1) c → j < 2*r → ∀ p : SeenPrefix r R experts c k j,
    NodeGood k (c.next experts p.calls.val)
  feedback : ∀ {k c j}, NodeGood (k+1) c → j < 2*r → ∀ (p : SeenPrefix r R experts c k j)
    {tr ch}, Emits ((c.next experts p.calls.val).exec r R experts k) tr ch → ∀ tape,
    pcOK (.feedback (c.frame R experts k (2*r-(j+1)) p.calls.val) (codeOutput ch.val) tape)
  assembled : ∀ {k c}, NodeGood (k+1) c → ∀ p : SeenPrefix r R experts c k (2*r),
    pcOK (.returned ((fixedKernel R r experts).assemble c.input (c.rows p.calls.val)))

end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
