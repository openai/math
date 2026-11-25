import OAI.Computability.BorderVNP.DiagonalStageSavedTags
import OAI.Computability.BorderVNP.DiagonalFlattenTagModels

/-! # All pointwise sparse observations on the selected normalized inner history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Site.Programs

open Crossing Diagonal.ExternalSew

/-- In a parallel disjoint union, retaining an original private predicate reads only
the matching child, even when different copies have equal public descriptions. -/
theorem carryPred_parallel {D k : ℕ} {P : Type} {bits : P → ℕ}
    {N M : Fin k → Network D P bits} (r : ∀ j, Retains (N j) (M j))
    (pred : ((j : Fin k) × (N j).Site) → (ℕ → Bool) → Prop) :
    @carryPred ((j : Fin k) × (N j).Site) ((j : Fin k) × (M j).Site) (Retains.parallel r).site pred =
      fun (v : (j : Fin k) × (M j).Site) b => @carryPred (N v.1).Site (M v.1).Site
        (r v.1).site (fun u => pred ⟨v.1,u⟩) v.2 b := by
  funext v b
  obtain ⟨j,v⟩ := v
  apply propext
  constructor
  · intro h u eq
    exact h ⟨j,u⟩ (congrArg (Sigma.mk j) eq)
  · rintro h ⟨i,u⟩ eq
    change (⟨i,(r i).site u⟩ : (a : Fin k) × (M a).Site) = ⟨j,v⟩ at eq
    obtain rfl : i = j := congrArg Sigma.fst eq
    exact h u (eq_of_heq (Sigma.mk.inj eq).2)

end Packing.Inherited.Site.Programs

namespace PackedHistoryCircuit.Normalized.Program

open Cover Crossing Shortening Adaptive Packing Packing.Inherited Epoch.Round
open Diagonal.CellEntries Diagonal.ExternalSew Site.Programs
open scoped Classical
attribute [local instance] portFintype

set_option maxHeartbeats 2000000
set_option maxRecDepth 6000

variable {D m k b exp : ℕ} [NeZero D] {K I P E Team Param Gadget : Type}
    [Field K] [Field E] [Fintype I] [Fintype P] [Fintype Team] [Fintype Param]
    {bits : P → ℕ} {A : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
    {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    {e : PaidIdentity K D m} (F : Program (B := B) e view) (store : F.SaveNames) (rows : F.SiteRows)
    (layout : F.SiteModelRows store rows) (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0) (pos : e.Entry → Gadget) (num : Gadget ↪ ℕ)

local notation3 "leaf₀" => (fun a => (view 0 a).pack)
local notation3 "net₀" => (fun n a => (view n a).pack.layout)
local notation3 "move₀" => DenseReplay.move (Team := Team) (Param := Param) (exp := exp) F y hy pos (namesStorage F store)

/-- Replaying any height of the real public histogram tree preserves the sparse
observation fiber for every locally assigned input and every original private choice. -/
theorem joined_replay_tagModels (n : ℕ) (hn : n ≤ b) (flat : Fin (k^n) → A 0)
    (initial : ∀ i, Site.Programs (view 0 (flat i)).pack.layout)
    (input : ∀ i, Tracked Team Param Gadget exp (view 0 (flat i)).pack.layout)
    (pred : ∀ i, (view 0 (flat i)).pack.layout.Site → (ℕ → Bool) → Prop)
    (models : ∀ i, TagModels (view 0 (flat i)).pack.layout (layout.edges 0 (flat i)) (rows.ports 0)
      (initial i) (input i).tags num (pred i))
    (q : (F.system.histories n hn (leavesEquiv k _ n flat)).Index) :
    let a := leavesEquiv k _ n flat
    let state := RowTrace.state F.system n hn a q
    let tracked := Replay.publicReplay F.system net₀ move₀ n hn a (Replay.flatInputs (net₀ 0) n flat input) q
    TagModels (view n state).pack.layout (layout.edges n state) (rows.ports n)
      (F.replayPrivatePrograms store rows (num ∘ pos) n hn a (nestedPrivatePrograms leaf₀ n flat initial) q)
      (@Tracked.tags _ _ _ _ _ _ (Replay.batchFinite k Team n) _ _ _ tracked) num
      (carryPred (normalizedAncestry F (namesStorage F store) n hn a q).site
        (fun v => let u := originalNames leaf₀ n flat v; pred u.1 u.2)) := by
  induction n with
  | zero =>
    intro a state tracked v
    apply (models 0 v).congrPred
    intro g
    exact (carryPred_old (Function.Embedding.refl _) (pred 0) v (extendWork g)).symm
  | succ n ih =>
    intro a state tracked
    let hj := Nat.lt_of_succ_le hn
    let index : Fin b := ⟨n,hj⟩
    let sub (j : Fin k) (l : Fin (k^n)) := flat (copyIndex k n (j,l))
    let c (j : Fin k) := RowTrace.state F.system n hj.le (a j) (q.1 j)
    let childTags (j : Fin k) := Replay.publicReplay F.system net₀ move₀ n hj.le (a j)
      (Replay.flatInputs (net₀ 0) n (sub j) (fun l => input (copyIndex k n (j,l)))) (q.1 j)
    let bank := nestedPrivatePrograms leaf₀ (n+1) flat initial
    let old (j : Fin k) := F.replayPrivatePrograms store rows (num ∘ pos) n hj.le (a j)
      (subInitial (view := view) n a bank j) (q.1 j)
    let host (j : Fin k) := normalizedAncestry F (namesStorage F store) n hj.le (a j) (q.1 j)
    let choices (v : (parallelLeaves leaf₀ (n+1) a).layout.Site) :=
      let u := originalNames leaf₀ (n+1) flat v
      pred u.1 u.2
    let tests (j : Fin k) := carryPred (host j).site (fun u => choices ⟨j,u⟩)
    have each (j : Fin k) : TagModels (view n (c j)).pack.layout (layout.edges n (c j)) (rows.ports n)
        (old j) (@Tracked.tags _ _ _ _ _ _ (Replay.batchFinite k Team n) _ _ _ (childTags j)) num (tests j) := by
      dsimp only [old]
      rw [subInitial_nested]
      exact ih hj.le (sub j) (fun l => initial (copyIndex k n (j,l))) (fun l => input (copyIndex k n (j,l)))
        (fun l => pred (copyIndex k n (j,l))) (fun l => models (copyIndex k n (j,l))) (q.1 j)
    have step := F.savePrivatePrograms_tagModels store rows layout y hy pos num index c q.2 childTags old tests each
    have lifted : (fun v : (raw (fun j => view n (c j))).layout.Site => tests v.1 v.2) =
        carryPred (Retains.parallel host).site choices := (carryPred_parallel host choices).symm
    let nextHost := ((normalizedStage e (F.stage index c) q.2).trans
      (Retains.store (namesStorage F store index c q.2))).site
    have composed := (congrArg (carryPred nextHost) lifted).trans
      (carryPred_trans (Retains.parallel host).site nextHost choices)
    intro v
    exact (step v).congrPred fun g => Iff.of_eq (congrFun (congrFun composed v) (extendWork g))

/-- All normalized inner updates, followed by the actual flattening of copy and port
rows, preserve the prescribed work at every original site and the pre-specialization
scalar counts of each realized sparse report. -/
theorem flatPrivatePrograms_tagModels (flat : Fin (k^b) → A 0)
    (initial : ∀ i, Site.Programs (view 0 (flat i)).pack.layout)
    (input : ∀ i, Tracked Team Param Gadget exp (view 0 (flat i)).pack.layout)
    (pred : ∀ i, (view 0 (flat i)).pack.layout.Site → (ℕ → Bool) → Prop)
    (models : ∀ i, TagModels (view 0 (flat i)).pack.layout (layout.edges 0 (flat i)) (rows.ports 0)
      (initial i) (input i).tags num (pred i)) (q : F.Hist flat) :
    let state := RowTrace.state F.system b le_rfl (leavesEquiv k _ b flat) q
    let tracked := Replay.publicFlat F.system net₀ move₀ b le_rfl flat input q
    TagModels (flattenPack b (F.terminal flat q).pack).layout (layout.edges b state) (Flat.portRows b (rows.ports b))
      (F.flatPrivatePrograms store rows (num ∘ pos) flat initial q) tracked.tags num
      (carryPred (normalizedHosts F (namesStorage F store) flat q).site (fun v => pred v.1 v.2)) := by
  intro state tracked
  let a := leavesEquiv k _ b flat
  let prior := F.replayPrivatePrograms store rows (num ∘ pos) b le_rfl a
    (nestedPrivatePrograms leaf₀ b flat initial) q
  let tags := Replay.publicReplay F.system net₀ move₀ b le_rfl a (Replay.flatInputs (net₀ 0) b flat input) q
  let p : Pack D (Port k P b) (width bits k b) (Entry Param Gadget) :=
    ⟨(view b state).pack.layout,@Tracked.tags _ _ _ _ _ _ (Replay.batchFinite k Team b) _ _ _ tags⟩
  let choices := fun v : (parallelPacks fun i => leaf₀ (flat i)).layout.Site => pred v.1 v.2
  have model := F.joined_replay_tagModels store rows layout y hy pos num b le_rfl flat initial input pred models q
  have h := TagModels.flatten b p (layout.edges b state) (rows.ports b) prior num
    (carryPred (normalizedAncestry F (namesStorage F store) b le_rfl a q).site
      (choices ∘ originalNames leaf₀ b flat)) model
  have eq := carryPred_normalizedHosts F (namesStorage F store) flat q choices
  intro v
  exact (h v).congrPred fun g => Iff.of_eq (congrFun (congrFun eq v) (extendWork g))

end PackedHistoryCircuit.Normalized.Program

end BorderVNP
end Computability
end OAI
