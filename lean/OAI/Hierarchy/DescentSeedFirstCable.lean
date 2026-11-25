import OAI.Hierarchy.DescentSeedOriginIdentity
import OAI.Hierarchy.DescentOriginalArgumentPointer

namespace OAI
/-! The semantic pointer for every original static seed operand on the actual initialized branch. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Origin
open DescentCompiler DescentColonies DescentInitialHost DescentPackedSeed DescentSeedRoot DescentOperandStateBanks
open Computability.BorderVNP.Crossing Catalyst
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins)
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k s z wire : ℕ}
    {c : (initialGroup X S.copies s).Choice} {digits : Fin S.copies≃Fin (S.groupCount 0)×Block k}
    (o : Origin X (G:=G) (S:=S) (q:=q) (fee:=ε) (z:=z) (wire:=wire) c digits)

theorem first_cable {p : ℕ} (hp : 0<p) (j : Fin S.copies) (v : Vertex X)
    (e : {f : Cable X // DescentInitialHost.source X.network.copyGraph f=v ∨ DescentInitialHost.target X.network.copyGraph f=v}) (chunk : ℕ)
    (fits : (chunk+1)*p≤((initialGroup X S.copies s).state c).graph.width ⟨j,e.val⟩) :
    o.raw.firstCable hp ⟨j,v⟩ (Signed.Plane.liftCable X c j v e) chunk fits=
      .cable (Signed.seedPeer X v e.val) (Signed.seedParallel X v e.val) chunk :=by
  let edge:=Signed.Plane.liftCable X c j v e
  have alive : 0<o.raw.placement.grainCount edge.val:=by
    by_contra! empty
    have width:=o.raw.placement.grainCount_fit S o.raw.valid edge.val
    rw [show o.raw.placement.grainCount edge.val=0 by omega,Nat.zero_mul] at width
    have possible : (chunk+1)*p≤((initialGroup X S.copies s).state c).graph.width edge.val:=fits
    have noRoom : (chunk+1)*p ≤ 0 := possible.trans_eq width
    exact (Nat.not_lt_of_ge noRoom) (Nat.mul_pos (Nat.zero_lt_succ chunk) hp)
  have words:=o.seed.cables o.raw.valid j v e alive
  exact congrArg₂ (fun a b=>Pointer.cable a b chunk) words.1 words.2

end
end Hierarchy.DescentSixParty.SeedNamed.Origin

end OAI
