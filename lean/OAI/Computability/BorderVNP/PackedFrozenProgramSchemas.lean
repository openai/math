import OAI.Computability.BorderVNP.PackedFrozenFormats
import OAI.Computability.BorderVNP.PackedHistoryPrivateNamedRows

/-! # Complete frozen public schemas through a selected combining path

At each active level the child directory is copied exactly once for each
branch of the parallel node. Its new record blocks use the node's genuine
tile/bin seed type and the same nested exterior-port naming as the named
private-program replay.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.ProgramSchemas

open Crossing Shortening Shortening.PublicDenseReceipt PackedHistoryCircuit.Normalized

variable {D m b : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} {h H ν : ℝ}
    (path : SourcePath b e h H ν) (last high k : ℕ) (E : ℕ → ℕ) (np w : ℕ)

/-- The actual public seed type of the stage that writes the new intrinsic rows. -/
noncomputable abbrev Seeds (i : Fin b) :=
  PublicDenseReceipt.Seed (path.pattern i).bins (path.asPath.depth last high (i.val+1))

/-- One active selected node, with the exact public joined edge and port capacities. -/
noncomputable def innerRound (i : Fin b) (prior : Format) : Format :=
  Format.round e (Seeds path last high i) k (k*E i.val) (Parallel.nestedCapacity k np (i.val+1)) w prior

/-- The installed frozen format at each level of this finite path. An index past its end
refers to the terminal format, so only the path's actual stages introduce fresh rows. -/
noncomputable def inner (base : Format) : ℕ → Format
  | 0 => base
  | j+1 => let prior := inner base j
           if hj : j < b then innerRound path last high k E np w ⟨j,hj⟩ prior else prior

/-- The source state includes exactly its existing chronology before the first node. -/
@[simp] theorem inner_zero (base : Format) : inner path last high k E np w base 0 = base := rfl

/-- At every attained physical stage, the next format is its four-way public node schema. -/
theorem inner_next (base : Format) (i : Fin b) :
    inner path last high k E np w base (i.val+1) =
      innerRound path last high k E np w i (inner path last high k E np w base i.val) := by
  rw [inner,dite_eq_left i.isLt]

/-- Stages beyond the finite path have no associated physical node. -/
theorem inner_past (base : Format) {j : ℕ} (hj : b ≤ j) :
    inner path last high k E np w base (j+1) = inner path last high k E np w base j := by
  rw [inner,dite_eq_right (Nat.not_lt.mpr hj)]

/-- The product-copy port rectangle agrees numerically with the true nested port shape. -/
theorem nested_ports (k np : ℕ) (j : ℕ) : Parallel.nestedCapacity k np j = k^j*np := by
  induction j with
  | zero => simp [Parallel.nestedCapacity]
  | succ j ih => rw [Parallel.nestedCapacity,ih,pow_succ',Nat.mul_assoc]

end Packing.Inherited.FrozenTape.ProgramSchemas

end BorderVNP
end Computability
end OAI
