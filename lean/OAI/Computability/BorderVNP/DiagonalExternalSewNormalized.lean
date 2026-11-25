import OAI.Computability.BorderVNP.DiagonalExternalSewAncestry
import OAI.Computability.BorderVNP.DiagonalSpecializedDense

/-! # Host retention when sorting the incoming cables before every cut -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Shortening Adaptive Packing CellEntries PackedHistoryCircuit.Normalized
open scoped Classical

variable {k D m d d' : ℕ} [NeZero D] {P I K B : Type} [Fintype I] [Fintype B] [Field K]
    {bits : P → ℕ} {child : Fin k → PlacedPack D P bits K I d} (e : PaidIdentity K D m)

/-- The input sort, cut, and sewn profile keep every old host and port.
The sorted cable order affects which bits are cut but not the attachment
of an external port. -/
noncomputable def normalizedStage (s : Stage m B d' child) (q : s.Index e) :
    Retains (raw child).layout (s.result e q).pack.layout :=
  (Retains.store (Storage.dense (raw child).layout s.slot)).trans
    (⟨⟨Sum.inl,Sum.inl_injective⟩,fun _ => rfl⟩ : Retains s.input.layout (s.result e q).pack.layout)

variable {steps : ℕ} {A : ℕ → Type*} {Bin : Fin steps → Type} [∀ i, Fintype (Bin i)]
    {depth : ℕ → ℕ} {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    {e} (F : PackedHistoryCircuit.Normalized.Program (B := Bin) e view) (save : DenseReplay.Saved F)

private noncomputable def savedState (n : ℕ) (hn : n ≤ steps) (a : Leaves k (A 0) n)
    (q : (F.system.histories n hn a).Index) := (F.system.layer n).state ((F.system.histories n hn a).term q)

/-- Every prior sort and every actual public histogram in the normalized
history contributes its own real vertex address map. -/
noncomputable def normalizedAncestry :
    (n : ℕ) → (hn : n ≤ steps) → (a : Leaves k (A 0) n) →
    (q : (F.system.histories n hn a).Index) →
    Retains (parallelLeaves (fun x => (view 0 x).pack) n a).layout (view n (savedState F n hn a q)).pack.layout
  | 0, _, _, _ => Retains.id _
  | n+1, hn, a, q => by
    let hj := Nat.lt_of_succ_le hn
    let i : Fin steps := ⟨n,hj⟩
    let c := fun j : Fin k => savedState F n hj.le (a j) (q.1 j)
    exact (Retains.parallel fun j => normalizedAncestry n hj.le (a j) (q.1 j)).trans
      ((normalizedStage e (F.stage i c) q.2).trans (Retains.store (save i c q.2)))

/-- Flattened original vertex addresses on the actual densely saved
terminal layout of this normalized history. -/
noncomputable def normalizedHosts (a : Fin (k^steps) → A 0)
    (q : (F.system.histories steps le_rfl (leavesEquiv k (A 0) steps a)).Index) :
    Retains (parallelPacks fun i => (view 0 (a i)).pack).layout
      (flattenPack steps (view steps (savedState F steps le_rfl (leavesEquiv k (A 0) steps a) q)).pack).layout :=
  (flatOriginal (fun x => (view 0 x).pack) steps a).trans
    (normalizedAncestry F save steps le_rfl (leavesEquiv k (A 0) steps a) q).flat

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
