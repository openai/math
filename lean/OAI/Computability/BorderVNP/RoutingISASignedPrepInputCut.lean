import OAI.Computability.BorderVNP.RoutingISASignedPrepOwnedPhysical
import OAI.Computability.BorderVNP.RoutingISASignedPrepReportTail

/-! # The ownership and report cuts inside the genuine signed cell-input builder -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM BorderVNP.Cube DiagonalTallyCellReports
open private simultaneous from OAI.Computability.BorderVNP.RoutingISASignedPrepJoint

variable {n b h K symbols w : ℕ} (id : TableEntry n b h K symbols → ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) {s : Bank w} {m : Memory w}

/-- The constant installer takes no choices. Its fitted real return fixes the
owned scanner's initial state for all possible subsequent local continuations. -/
noncomputable def inputCut (c : Returns (CubeConstants.install id) pub mac s m) :
    Returns (signedInputs id (TeamRows.ownedGroups n b h K symbols)) pub mac s m ≃
      (Σ o : Returns (TeamRows.ownedGroups n b h K symbols) pub mac c.val.2.1 c.val.2.2,
        LocalTail pub mac o.val.2.1 o.val.2.2) := by
  let next (x : Returns (CubeConstants.install id) pub mac s m) :=
    Σ o : Returns (TeamRows.ownedGroups n b h K symbols) pub mac x.val.2.1 x.val.2.2,
      LocalTail pub mac o.val.2.1 o.val.2.2
  have empty : c.val.1.flatMap TeamRAM.Event.choices=[] := List.flatMap_eq_nil_iff.mpr fun e he =>
    (c.property.unsigned_events (CubeConstants.install_unsigned id).1 e he).1
  have once : next c ≃ (Σ x, next x) := Equiv.ofBijective (Sigma.mk c) ⟨
    fun _ _ eq => eq_of_heq (Sigma.mk.inj eq).2,
    fun ⟨x,y⟩ => by
      obtain rfl := return_eq_of_empty pub mac ((CubeConstants.install id).nativeOnly_of_unsigned
        (CubeConstants.install_unsigned id).1) c x empty
      exact ⟨y,rfl⟩⟩
  exact (inputVisitsEquiv id pub mac _ s m).symm.trans once.symm

variable {U : Type*} (pubs : U → Arg → Word w) (macs : U → TeamOpcode.Macros w 8)
    (regs : U → Bank w) (memory : U → Memory w)

/-- The joint cell-input builder is indexed by its true all-team owned-group
histories. The local tails start at each original resulting memory. -/
noncomputable def jointInputCut
    (c : ∀ u, Returns (CubeConstants.install id) (pubs u) (macs u) (regs u) (memory u)) :
    ((u : U) → Returns (signedInputs id (TeamRows.ownedGroups n b h K symbols)) (pubs u) (macs u) (regs u) (memory u)) ≃
      (Σ z : (u : U) → Returns (TeamRows.ownedGroups n b h K symbols) (pubs u) (macs u) (c u).val.2.1 (c u).val.2.2,
        (u : U) → LocalTail (pubs u) (macs u) (z u).val.2.1 (z u).val.2.2) :=
  (Equiv.piCongrRight fun u => inputCut id (pubs u) (macs u) (c u)).trans simultaneous

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
