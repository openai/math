import OAI.Computability.BorderVNP.PackedHistoryCompilerRows
import OAI.Computability.BorderVNP.PackedHistoryFlatPrivateSites

/-! # Compiler bounds of the flattened private programs returned by an epoch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Crossing Cover Epoch.Round Shortening Shortening.Adaptive Packing Packing.Inherited
open Diagonal.ExternalSew Diagonal.CellEntries
open scoped Classical
attribute [local instance] portFintype

variable {D k : ℕ} {K : Type*} {P : Type} [Fintype P] {bits : P → ℕ} {X : Type*} (leaf : X → Pack D P bits K)

/-- Flattening the input site banks in row-major order preserves every
pointwise property of their current executable programs. -/
theorem nestedPrivatePrograms_forall (Q : Site → Prop) (n : ℕ) (flat : Fin (k^n) → X)
    (initial : ∀ i, Site.Programs (leaf (flat i)).layout) (h : ∀ i v, Q (initial i v).program) :
    ∀ v, Q ((nestedPrivatePrograms leaf n flat initial v).program) := by
  induction n with
  | zero => exact h 0
  | succ n ih =>
    rintro ⟨j,v⟩
    exact ih (fun z => flat (copyIndex k n (j,z))) (fun z => initial (copyIndex k n (j,z)))
      (fun z => h (copyIndex k n (j,z))) v

namespace Program

variable {m rounds : ℕ} [NeZero D] {K : Type} [Field K] {I : Type} [Fintype I]
    {A : ℕ → Type*} {B : Fin rounds → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
    {e : PaidIdentity K D m} {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    (F : Program (B := B) e view) (store : F.SaveNames) (rows : F.SiteRows) (number : e.Entry → ℕ)
    (flat : Fin (k^rounds) → A 0) (initial : ∀ i, Site.Programs (view 0 (flat i)).pack.layout) (q : F.Hist flat)

/-- All flattened output programs meet the fixed compiler row bounds of the
paid identity when the actual independent input banks do. -/
theorem flatPrivatePrograms_compilerRows (base : ∀ i v, (initial i v).program.CompilerRows e) :
    ∀ v, (F.flatPrivatePrograms store rows number flat initial q v).program.CompilerRows e :=
  F.replayPrivatePrograms_compilerRows store rows number rounds le_rfl (leavesEquiv k _ rounds flat)
    (nestedPrivatePrograms _ _ flat initial)
    (nestedPrivatePrograms_forall (fun x => (view 0 x).pack) (fun s => s.CompilerRows e) _ flat initial base) q

/-- Local scalar fields and global IDs retain their separate uniform scales
through the actual dense save and flattening at the end of the epoch. -/
theorem flatPrivatePrograms_splitFields {V U : ℕ} (localSize : tableLimit e ≤ V)
    (ids : ∀ z, number z ≤ U) (base : ∀ i v, (initial i v).program.SplitFields V U) :
    ∀ v, (F.flatPrivatePrograms store rows number flat initial q v).program.SplitFields V U :=
  F.replayPrivatePrograms_splitFields store rows number localSize ids rounds le_rfl (leavesEquiv k _ rounds flat)
    (nestedPrivatePrograms _ _ flat initial)
    (nestedPrivatePrograms_forall (fun x => (view 0 x).pack) (fun s => s.SplitFields V U) _ flat initial base) q

end Program

end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
