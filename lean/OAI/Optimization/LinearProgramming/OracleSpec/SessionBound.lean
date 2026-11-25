import OAI.Optimization.LinearProgramming.OracleSpec.DialogueProof

/-! Monotonicity of the size bound on an oracle dialogue. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec
namespace Dialogue

theorem Session.raiseLimit {I C : Type} {ei : I → Word} {ec : C → Word}
    {dispatch : I ⊕ (Bool × C) → Bool ⊕ (Word × C)} {reply : Transcript → Word → Bool}
    {L L' : ℕ} {s h b out n}
    (run : Session ei ec dispatch reply L s h b out n) (hle : L ≤ L') :
    Session ei ec dispatch reply L' s h b out n := by
  induction run with
  | done step size => exact .done step (size.trans hle)
  | query step size packet _ ih => exact .query step (size.trans hle) (packet.trans hle) ih

end Dialogue
end OracleSpec
end LinearProgramming
end Optimization
end OAI
