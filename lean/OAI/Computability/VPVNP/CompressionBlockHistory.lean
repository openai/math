import OAI.Computability.VPVNP.CompressionBlock
import OAI.Computability.VPVNP.CompressionProcedureHistory

/-!
# Local records for one compression block

The record list at each site comes from the actual shrinking or refresh
kernel. Composition follows the same indexed schedule as the energy and
position estimates. A maximum over the finitely many substep constants
bounds every local record, and each branch takes at most one step per
shrinking degree followed by one refresh.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

variable {R : Type*} [CommSemiring R]

/-- Transport the chosen records along equal presentations of a procedure's
degrees, lane length, divisor and energy coefficient. -/
def Procedure.RecordBounds.reindex {a b k p a' b' k' p' C s : ℕ} {μ μ' : ℝ}
    {P : Procedure R a b k p μ} (B : P.RecordBounds C s)
    {ha : a = a'} {hb : b = b'} {hk : k = k'} {hp : p = p'} {hμ : μ = μ'} :
    (P.reindex ha hb hk hp hμ).RecordBounds C s := by
  subst a' b' k' p' μ'
  exact B

namespace BlockSchedule

variable {k : Type*} [Field k] (S : BlockSchedule k)

private noncomputable def prefixRecordBounds {C : ℕ} (shrink : S.ShrinkProcedures R)
    (hs : ∀ i : Fin S.steps, (shrink i).RecordBounds C 1) (j : ℕ) (hj : j ≤ S.steps) :
    (S.shrinkPrefix shrink j hj).RecordBounds C j :=
  match j with
  | 0 => by
    rw [shrinkPrefix]
    exact (Procedure.RecordBounds.id R _ C).reindex
  | j + 1 => by
    rw [shrinkPrefix]
    apply Procedure.RecordBounds.reindex
    apply Procedure.RecordBounds.mono _ (max_le (le_refl C) (le_refl C)) le_rfl
    exact (prefixRecordBounds shrink hs j (by omega)).seq (hs ⟨j, hj⟩).reindex

/-- The bound records the actual kernels passed into `assembleBlock` and
is independent of the network order, widths, and chosen execution path. -/
noncomputable def assembleBlockRecords (shrink : S.ShrinkProcedures R)
    (refresh : S.RefreshProcedure R) {C : Fin S.steps → ℕ} {D : ℕ}
    (hs : ∀ i : Fin S.steps, (shrink i).RecordBounds (C i) 1) (hr : refresh.RecordBounds D 1) :
    (S.assembleBlock shrink refresh).RecordBounds (max (Finset.univ.sup C) D) (S.steps + 1) := by
  unfold assembleBlock
  apply Procedure.RecordBounds.reindex
  apply Procedure.RecordBounds.seq _ hr
  apply Procedure.RecordBounds.reindex
  exact S.prefixRecordBounds shrink (fun i ↦ (hs i).mono (Finset.le_sup (Finset.mem_univ i)) le_rfl)
    S.steps le_rfl

end BlockSchedule
end Compression

end VPVNP
end Computability
end OAI
