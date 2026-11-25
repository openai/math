import OAI.Computability.BorderVNP.FiniteEvaluatorCubeTripleFold
import OAI.Computability.BorderVNP.CubeTeamVertexDirectoryFrame
import OAI.Computability.BorderVNP.CubeTeamOwnedPhysicalRoles

/-! # Directory progress at the genuine allocated row endpoints -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeTriple

open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.TeamRows BorderVNP.Cube.Padding.Banks
open BorderVNP.Cube.TeamRowSources BorderVNP.Cube.Tally VPVNP.BurstRAM RoutingISA RoutingISA.OwnedStages

variable {w n blocks b h K s : ℕ} {l : TeamRowPrepare.Layout} {A : Data n l.d blocks b h K s}
variable {owner : Fin l.d → ℕ} {power base stop actual claimed : ℕ} {rows : Sym2 (Fin l.d) → Fin (n+1) → ℕ}
variable {pub : Arg → Word w} {original m mt : Memory w} {r t : Bank w}
variable (P : PhysicalSetup A owner power base stop actual claimed rows pub original)
include P

/-- Each concrete callback of the allocated scanner extends the full chronological
triple column. Separation from previous triples follows from the actual bank,
checker and cursor allocation and does not require them in the immutable inputs. -/
theorem stage (v : Fin l.d × Fin l.d) (owned : owner v.1 = l.teamID)
    (cursor : readings r 7 = base+3*vertexPrefix l (wordOwner owner) n blocks (key v))
    (old : Past (l := l) A owner base (key v) m)
    (done : PhysicalStages A power actual pub r m t mt v) : Past (l := l) A owner base (key v+1) mt := by
  cases done with
  | strict p high out ready result =>
    let q := finProdFinEquiv (oriented p high)
    have atPair : pairAt l.d q = oriented p high := finProdFinEquiv.symm_apply_apply _
    have actualCursor : out = base+3*vertexPrefix l (wordOwner owner) n blocks q.val :=
      ready.output.symm.trans cursor
    let D := A.packet p high (l.view q.val) (l.crossing q.val)
    let S := A.side power l.header out
    have subtotal : actual+(n+1) ≤ A.packetBase := P.checker.beforeClaim.trans ((Nat.le_add_right ..).trans P.checker.beforeBank)
    have packets : A.packetBase ≤ A.singleBase := (Nat.le_add_right ..).trans P.allocation.orderPackets
    have singles : A.singleBase ≤ base := (Nat.le_add_right ..).trans P.allocation.orderSingles
    have room : base ≤ out := actualCursor ▸ Nat.le_add_right ..
    apply old.strict q p high atPair (atPair ▸ owned)
    · intro x lo hi
      exact P.strict_directory_word p high _ _ out ready result lo (hi.trans_eq actualCursor.symm)
    · rw [← actualCursor]
      exact strict_stored D S ready result (subtotal.trans (packets.trans (singles.trans room)))
        (P.afterScratch.trans (singles.trans room))
  | diagonal g verified =>
    let q := finProdFinEquiv (g,g)
    have atPair : pairAt l.d q = (g,g) := finProdFinEquiv.symm_apply_apply _
    apply old.diagonal q (by rw [atPair])
    intro x lo _
    exact diagonalRole_directory g (l.view q.val) (l.crossing q.val) P.allocation P.checker P.afterScratch verified lo

/-- Every actual strict or diagonal callback keeps all words beyond the reserved
vertex column. A fixed deck placed there survives both scatters and the two
temporary arrays of the local declaration verifier. -/
theorem stage_above (v : Fin l.d × Fin l.d) (owned : owner v.1 = l.teamID)
    (cursor : readings r 7 = base+3*vertexPrefix l (wordOwner owner) n blocks (key v))
    (done : PhysicalStages A power actual pub r m t mt v) (a : ℕ) (upper : stop ≤ a) : mt a=m a := by
  have finalRoom : base ≤ stop := (Nat.le_add_right ..).trans P.capacity
  have singleRoom := P.allocation.orderSingles.trans (finalRoom.trans upper)
  have singles : A.singleBase ≤ a := (Nat.le_add_right ..).trans singleRoom
  have subtotal : actual+(n+1) ≤ A.packetBase := P.checker.beforeClaim.trans ((Nat.le_add_right ..).trans P.checker.beforeBank)
  have packets : A.packetBase ≤ A.singleBase := (Nat.le_add_right ..).trans P.allocation.orderPackets
  cases done with
  | strict p high out ready ret =>
    let q := key (oriented p high)
    let D := A.packet p high (l.view q) (l.crossing q)
    let S := A.side power l.header out
    have outEq : out=base+3*vertexPrefix l (wordOwner owner) n blocks q := ready.output.symm.trans cursor
    have ends : out+(2*blocks*(l.d.choose 2)^n)*(3*2^n) ≤ a := by
      rw [outEq]
      exact (P.strictRoom p high owned).trans upper
    obtain ⟨u,mu,side,check⟩ := ret.stages
    have above := OwnedVertex.rowImage_above (blocks := blocks) A.axis p high A.packetBase
      (bankWidth n b h K s) (selectorWidth n K h) out (readings (scattered D S m)) (Physical.Owned.packetTrials n l.d blocks)
    dsimp only at above
    rw [OwnedVertex.rowImage_cursor,OwnedVertex.selectedPrefix_end] at above
    have unchanged := scattered_after_singletons D S m a ready.stride.ge ready.packetsBeforeSingletons singleRoom
    exact Fin.ext ((check.outside a ⟨.inr (subtotal.trans (packets.trans singles)),.inr (P.afterScratch.trans singles)⟩).trans
      ((congrFun side.image a).trans ((above a ends).trans (congrArg Fin.val unchanged))))
  | diagonal g verified =>
    exact diagonalRole_directory g _ _ P.allocation P.checker P.afterScratch verified (finalRoom.trans upper)

/-- The machine-word count slot precedes the whole vertex directory in this
actual physical setup. -/
theorem frame_before : l.frame+46 < base := by
  have h₁ := P.allocation.frame
  have h₂ := P.allocation.orderPackets
  have h₃ := P.allocation.orderSingles
  omega

end FiniteEvaluator.CubeTriple

end BorderVNP
end Computability
end OAI
