import OAI.Computability.BorderVNP.PackedHistoryPrivateSites
import OAI.Computability.BorderVNP.PackedInheritedFlatValue
import OAI.Computability.BorderVNP.DiagonalExternalSewEnriched

/-! # Full private programs on the actual flat ports of an enriched epoch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Crossing Cover Epoch.Round Shortening Shortening.Adaptive Packing Packing.Inherited
open Diagonal.ExternalSew Diagonal.CellEntries
open scoped Classical
attribute [local instance] portFintype

variable {D k : ℕ} {K : Type*} {P : Type} [Fintype P] {bits : P → ℕ} {X : Type*} (leaf : X → Pack D P bits K)

/-- Present the initial private banks in the nested child order of the actual history. -/
noncomputable def nestedPrivatePrograms :
    (n : ℕ) → (flat : Fin (k^n) → X) → (∀ i, Site.Programs (leaf (flat i)).layout) →
    Site.Programs (parallelLeaves leaf n (leavesEquiv k _ n flat)).layout
  | 0, _, initial => fun v => (initial 0 v).castWidth (incoming_instances _ _)
  | n+1, flat, initial => fun ⟨j,v⟩ => by
    let sub := fun i : Fin k => fun z => flat (copyIndex k n (i,z))
    let children := fun i : Fin k => (parallelLeaves leaf n (leavesEquiv k _ n (sub i))).layout
    let prior := nestedPrivatePrograms n (sub j) (fun z => initial (copyIndex k n (j,z))) v
    exact prior.castWidth ((Inherited.Parallel.incoming_eq children j v).symm.trans (incoming_instances _ _))

/-- The nested original site names resolve to the original private bank of that flat leaf. -/
theorem nestedPrivatePrograms_birth (n : ℕ) (flat : Fin (k^n) → X)
    (initial : ∀ i, Site.Programs (leaf (flat i)).layout)
    (v : (parallelLeaves leaf n (leavesEquiv k _ n flat)).layout.Site) :
    let u := originalNames leaf n flat v
    (nestedPrivatePrograms leaf n flat initial v).birth = (initial u.1 u.2).birth := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases v with ⟨j,v⟩
    exact ih (fun z => flat (copyIndex k n (j,z))) (fun z => initial (copyIndex k n (j,z))) v

namespace Program

variable {m rounds : ℕ} [NeZero D] {K : Type} [Field K] {I : Type} [Fintype I]
    {A : ℕ → Type*} {B : Fin rounds → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
    {e : PaidIdentity K D m} {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    (F : Program (B := B) e view) (store : F.SaveNames) (rows : F.SiteRows) (number : e.Entry → ℕ)
    (flat : Fin (k^rounds) → A 0) (initial : ∀ i, Site.Programs (view 0 (flat i)).pack.layout) (q : F.Hist flat)

/-- The completed inner history's site programs, on the flattened ports of this output epoch. -/
noncomputable def flatPrivatePrograms : Site.Programs (flattenPack rounds (F.terminal flat q).pack).layout := by
  let src := nestedPrivatePrograms (fun z => (view 0 z).pack) rounds flat initial
  let final := F.replayPrivatePrograms store rows number rounds le_rfl (leavesEquiv k _ rounds flat) src q
  exact fun v => (final v).castWidth ((incoming_instances _ _).trans (Flat.incoming_eq rounds (F.terminal flat q).pack v).symm)

/-- The flat retained site of each original leaf still executes the private work fiber
of that leaf's very own birth program. -/
theorem flatPrivatePrograms_birth (j : Fin (k^rounds)) (v : (view 0 (flat j)).pack.layout.Site) :
    (F.flatPrivatePrograms store rows number flat initial q
      ((normalizedHosts F (namesStorage F store) flat q).site ⟨j,v⟩)).birth = (initial j v).birth := by
  let leaf := fun z => (view 0 z).pack
  let old := (originalNames leaf rounds flat).symm ⟨j,v⟩
  let src := nestedPrivatePrograms leaf rounds flat initial
  have saved : F.siteStorage store = namesStorage F store := rfl
  have h := F.replayPrivatePrograms_birth store rows number rounds le_rfl (leavesEquiv k _ rounds flat) src q old
  rw [saved] at h
  refine h.trans ?_
  have hb := nestedPrivatePrograms_birth leaf rounds flat initial old
  exact hb.trans (congrArg (fun u : (parallelPacks fun i => leaf (flat i)).layout.Site => (initial u.1 u.2).birth)
    ((originalNames leaf rounds flat).apply_symm_apply ⟨j,v⟩))

end Program
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
