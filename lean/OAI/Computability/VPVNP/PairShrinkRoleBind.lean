import OAI.Computability.VPVNP.PairShrinkRoleStages

/-! # Reassociating native parser stages and deterministic setup traces -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

variable {w endAddr : ℕ} {α β γ : Type*}

theorem bind_assoc (a : Reader w endAddr α) (b : α → Reader w endAddr β)
    (c : β → Reader w endAddr γ) :
    bind (bind a b) c = bind a (fun v => bind (b v) c) := by
  funext node saved bits
  cases ha : a node saved bits with
  | none => simp [bind, ha]
  | some pair =>
    obtain ⟨x, tail⟩ := pair
    cases hb : b x.value node x.updated tail with
    | none => simp [bind, ha, hb]
    | some pair =>
      obtain ⟨y, rest⟩ := pair
      cases hc : c y.value node y.updated rest with
      | none => simp [bind, ha, hb, hc]
      | some pair =>
        obtain ⟨z, last⟩ := pair
        simp [bind, ha, hb, hc, List.append_assoc]

theorem Setup.seq_reader (a b : Setup w endAddr) :
    (a.seq b).reader = bind a.reader (fun _ => b.reader) := rfl

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
