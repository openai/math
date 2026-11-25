import OAI.Optimization.LinearProgramming.RAM.Code

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Block
namespace Eval

/-- Weaken the invariant on the very same instruction execution and intermediate memories. -/
theorem weaken {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {P Q : Memory K → Prop} {b : Block} {s t : Memory K} {k : Nat}
    (run : Eval P b s k t) (h : ∀ u, P u → Q u) : Eval Q b s k t := by
  induction run with
  | skip hs => exact .skip (h _ hs)
  | op hs ht step => exact .op (h _ hs) (h _ ht) step
  | seq _ _ a b => exact a.seq b
  | branchTrue hc _ a => exact .branchTrue hc a
  | branchFalse hc _ a => exact .branchFalse hc a
  | loopFalse hc hs => exact .loopFalse hc (h _ hs)
  | loopTrue hc _ _ a b => exact .loopTrue hc a b

end Eval
end Block
end RAM
end LinearProgramming
end Optimization
end OAI

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Execution

/-- Enlarge the intermediate-state invariant of a concrete instruction execution. -/
theorem weaken {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {p : Program} {P Q : State K → Prop} {s t : State K} {k : Nat}
    (run : Execution p P s k t) (h : ∀ u, P u → Q u) : Execution p Q s k t := by
  induction run with
  | done s hs => exact .done s (h _ hs)
  | next hs step _ ih => exact .next (h _ hs) step ih

end Execution
end RAM
end LinearProgramming
end Optimization
end OAI
