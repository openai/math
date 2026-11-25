import OAI.Hierarchy.DescentCanonicalFrontSources

namespace OAI
/-! # The dated stem scene with its literal actor-directory addresses -/
namespace Hierarchy.DescentDatedAddressBook
open DescentResetLocalRoster ProtocolRAM
open scoped Classical
noncomputable section
namespace ResetOutput
theorem issued_is_original (v : ResetOutput) (b : ℕ) (old : v.OriginalOperands b) :
    let dir:=v.actor.directory (v.middle.stop b)
    v.issuedScene b old=v.front.fromOriginals (v.actorEnd b) old dir.flags dir.count dir.inverse := rfl

/-- Renaming the public front transports its genuine input producer and the resulting scene together. -/
theorem issued_original_at (v : ResetOutput) (b : ℕ) (A : CandidateFront) (shape : v.front=A)
    (old : A.Originals (v.actorEnd b)) :
    let dir:=v.actor.directory (v.middle.stop b)
    HEq (v.issuedScene b (cast (congrArg (fun a : CandidateFront => a.Originals (v.actorEnd b)) shape.symm) old))
      (A.fromOriginals (v.actorEnd b) old dir.flags dir.count dir.inverse) :=by
  subst A
  rfl

/-- The compiled phase, its running time and output image agree at both physical dates. -/
theorem issued_phases_at {w : ℕ} (v : ResetOutput) (b : ℕ) (A : CandidateFront)
    (shape : v.front=A) (old : A.Originals (v.actorEnd b))
    (literal : v.front.SceneRoom (v.actorEnd b) (v.issuedScene b (cast (congrArg (fun a : CandidateFront => a.Originals (v.actorEnd b)) shape.symm) old)) w)
    (calibrated : A.SceneRoom (v.actorEnd b) (A.fromOriginals (v.actorEnd b) old
      (v.actor.directory (v.middle.stop b)).flags (v.actor.directory (v.middle.stop b)).count
      (v.actor.directory (v.middle.stop b)).inverse) w) :
    v.front.received (v.actorEnd b) _ literal=A.received (v.actorEnd b) _ calibrated ∧
      v.front.trunkScene (v.actorEnd b) _ literal=A.trunkScene (v.actorEnd b) _ calibrated :=by
  subst A
  exact ⟨rfl,rfl⟩

end ResetOutput
end
end Hierarchy.DescentDatedAddressBook

end OAI
