import OAI.Computability.BorderVNP.DiagonalExternalSewEnrichedOuter
import OAI.Computability.BorderVNP.DiagonalEnrichedTerminal

/-! # Exact original host of a tracked power slot throughout normalized shortening -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.DenseReplay

open Crossing Shortening Shortening.Adaptive Packing PackedHistoryCircuit.Normalized Diagonal.ExternalSew
open scoped Classical
set_option maxHeartbeats 1200000

variable {k steps exp D m : ℕ} [NeZero D] {I P Team Param Gadget K E : Type}
    [Fintype I] [Fintype Team] [Fintype Param] [Field K] [Field E]
    {bits : P → ℕ} {A : ℕ → Type*} {B : Fin steps → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
    {e : PaidIdentity K D m} {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    (F : PackedHistoryCircuit.Normalized.Program (B := B) e view) (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0) (pos : e.Entry → Gadget) (save : Saved F)

/-- The finite team digits of the normalized power-slot owner. -/
local instance hostPowerTeams {n : ℕ} : Fintype (Port k Team n) := Replay.batchFinite k Team n

/-- Original unary owner as a vertex of the nested disjoint union of the exact leaf packs. -/
noncomputable def originalPowerSite (leaf : A 0 → Pack D P bits K) :
    (n : ℕ) → (a : Leaves k (A 0) n) → Replay.Inputs (fun z => (leaf z).layout) Team Param Gadget exp n a →
      PowerSlot (Port k Team n) Param exp → (parallelLeaves leaf n a).layout.Site
  | 0, _, t, w => t.words.site w
  | n+1, a, t, w => ⟨w.1.1,originalPowerSite (leaf := leaf) n (a w.1.1) (t w.1.1) (w.1.2,w.2)⟩

private noncomputable abbrev leaf := fun z => (view 0 z).pack
private noncomputable abbrev net := fun n (z : A n) => (view n z).pack.layout

/-- The selected private tables, arbitrary specialization of the scalar IDs, dense input
order and dense output save all preserve the true original power-slot owner. -/
theorem replay_power_site (n : ℕ) (hn : n ≤ steps) (a : Leaves k (A 0) n)
    (input : Replay.Inputs (net (view := view) 0) Team Param Gadget exp n a)
    (q : (F.system.histories n hn a).Index) (w : PowerSlot (Port k Team n) Param exp) :
    (Replay.publicReplay F.system (net (view := view)) (move F y hy pos save) n hn a input q).words.site w =
      (normalizedAncestry F save n hn a q).site (originalPowerSite (leaf (view := view)) n a input w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let h := Nat.lt_of_succ_le hn
    let i : Fin steps := ⟨n,h⟩
    let c := fun j : Fin k => (F.system.layer n).state ((F.system.histories n h.le (a j)).term (q.1 j))
    let host := (normalizedStage e (F.stage i c) q.2).trans (Retains.store (save i c q.2))
    exact congrArg (fun v => host.site ⟨w.1.1,v⟩) (ih h.le (a w.1.1) (input w.1.1) (q.1 w.1.1) (w.1.2,w.2))

omit [NeZero D] [Field K] in
/-- The nested original owner resolves to the correct flat leaf and its own private
power position, using the same row-major child digits as the physical outer ports. -/
theorem originalPowerSite_flat (leaf : A 0 → Pack D P bits K) (n : ℕ) (flat : Fin (k^n) → A 0)
    (input : ∀ j, Tracked Team Param Gadget exp (leaf (flat j)).layout)
    (w : PowerSlot (Port k Team n) Param exp) :
    let z := portEquiv k Team n w.1
    originalNames leaf n flat (originalPowerSite leaf n (leavesEquiv k _ n flat)
      (Replay.flatInputs (fun a => (leaf a).layout) n flat input) w) =
      ⟨z.1,(input z.1).words.site (z.2,w.2)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let sub := fun j => flat (copyIndex k n (w.1.1,j))
    have h := ih sub (fun j => input (copyIndex k n (w.1.1,j))) (w.1.2,w.2)
    exact congrArg (fun z : (j : Fin (k^n)) × (leaf (sub j)).layout.Site =>
      (⟨copyIndex k n (w.1.1,z.1),z.2⟩ : (parallelPacks fun j => leaf (flat j)).layout.Site)) h

/-- Actual owner site of a power bit on a flattened, saved, publicly selected epoch. -/
theorem flat_power_site (flat : Fin (k^steps) → A 0)
    (input : ∀ j, Tracked Team Param Gadget exp (view 0 (flat j)).pack.layout)
    (q : F.Hist flat) (w : PowerSlot (Fin (k^steps) × Team) Param exp) :
    (Replay.publicFlat F.system (net (view := view)) (move F y hy pos save) steps le_rfl flat input q).words.site w =
      (normalizedHosts F save flat q).site ⟨w.1.1,(input w.1.1).words.site (w.1.2,w.2)⟩ := by
  let src := leaf (view := view)
  let wn : PowerSlot (Port k Team steps) Param exp := ((portEquiv k Team steps).symm w.1,w.2)
  let nested := Replay.flatInputs (fun z => (src z).layout) steps flat input
  have hn := replay_power_site F y hy pos save steps le_rfl (leavesEquiv k _ steps flat) nested q wn
  refine hn.trans (congrArg (normalizedAncestry F save steps le_rfl (leavesEquiv k _ steps flat) q).site ?_)
  apply (originalNames src steps flat).eq_symm_apply.mpr
  have hh := originalPowerSite_flat src steps flat input wn
  exact hh.trans (congrArg (fun z : Fin (k^steps) × Team =>
    (⟨z.1,(input z.1).words.site (z.2,w.2)⟩ : (parallelPacks fun j => src (flat j)).layout.Site))
    ((portEquiv k Team steps).apply_symm_apply w.1))

end Diagonal.CellEntries.DenseReplay

end BorderVNP
end Computability
end OAI
