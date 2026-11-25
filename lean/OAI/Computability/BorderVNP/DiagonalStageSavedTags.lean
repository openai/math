import OAI.Computability.BorderVNP.DiagonalStageTagModels
import OAI.Computability.BorderVNP.PackedHistoryPrivateReplayModels
import OAI.Computability.BorderVNP.DiagonalSpecializedFlatReplay

/-! # The pointwise tagged fibers after a normalized stage's actual dense save -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Cover Crossing Shortening Adaptive PublicParallel Packing Packing.Inherited Epoch.Round
open Diagonal.CellEntries Diagonal.ExternalSew Site.Programs
open scoped Classical
attribute [local instance] portFintype

set_option maxHeartbeats 1600000
set_option maxRecDepth 5000

/-- Sort the true result cables and transport both the original work predicate and
the tag table to the physical stored state. -/
theorem carryPrivatePrograms_tagModels {D d ne nf np : ℕ} {K Q I Param Gadget : Type}
    [Fintype I] {fin fin' : Fintype Q} {bits : Q → ℕ}
    (p saved : PlacedPack D Q bits K I d) (edge : p.pack.layout.Edge ↪ Fin ne)
    (port : Q ↪ Fin np) (stored : saved = p.dense edge)
    (old : @Site.Programs D Q fin bits p.pack.layout)
    (tags : p.pack.layout.Tables (Entry Param Gadget)) (num : Gadget ↪ ℕ)
    (pred : p.pack.layout.Site → (ℕ → Bool) → Prop)
    (model : @TagModels D ne np Q fin bits Param Gadget p.pack.layout edge port old tags num pred)
    (dest : saved.pack.layout.Edge ↪ Fin nf) (cap : nf = ne)
    (names : HEq dest (CutCircuit.denseRows p.pack.layout edge)) :
    let storage := privateStorage p saved edge stored
    @TagModels D nf np Q fin' bits Param Gadget saved.pack.layout dest port
      (carryPrivatePrograms p saved edge stored (fin' := fin') old) (storage.tables tags) num
      (carryPred (Retains.store storage).site pred) := by
  subst saved
  subst nf
  have enum : fin' = fin := Subsingleton.elim _ _
  subst fin'
  obtain rfl := eq_of_heq names
  let _ := fin
  intro storage v
  let host := (Retains.store storage).site
  have agrees : carryPred host pred v = pred v := by
    funext g
    exact propext (carryPred_old host pred v g)
  rw [agrees]
  exact Site.Lineage.TagModel.dense (⟨p.pack.layout,tags⟩ : Pack D Q bits (Entry Param Gadget)) edge port v
    (old v) _ num (model v)

namespace Program

variable {D m k b exp : ℕ} [NeZero D] {K I P E Team Param Gadget : Type}
    [Field K] [Field E] [Fintype I] [Fintype P] [Fintype Team] [Fintype Param]
    {bits : P → ℕ} {A : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
    {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    {e : PaidIdentity K D m} (F : Program (B := B) e view) (store : F.SaveNames) (rows : F.SiteRows)
    (layout : F.SiteModelRows store rows) (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0) (pos : e.Entry → Gadget) (num : Gadget ↪ ℕ)

/-- Child tags indexed by the same enumeration of original teams as the public replay. -/
abbrev ReplayInput (n : ℕ) (x : A n) := by
  letI : Fintype (Port k Team n) := Replay.batchFinite k Team n
  exact Tracked (Port k Team n) Param Gadget exp (view n x).pack.layout

/-- The public and private normalized updates use the same result histogram, row
injections and second sort. This includes the original work predicate at every retained host. -/
theorem savePrivatePrograms_tagModels (i : Fin b) (c : Fin k → A i.val) (q : (F.stage i c).Index e)
    (input : ∀ j, ReplayInput (k := k) (Team := Team) (Param := Param) (Gadget := Gadget) (exp := exp) (view := view) i.val (c j))
    (old : ∀ j, Site.Programs (view i.val (c j)).pack.layout)
    (pred : ∀ j, (view i.val (c j)).pack.layout.Site → (ℕ → Bool) → Prop)
    (models : ∀ j, TagModels (view i.val (c j)).pack.layout (layout.edges i.val (c j)) (rows.ports i.val)
      (old j) (@Tracked.tags _ _ _ _ _ _ (Replay.batchFinite k Team i.val) _ _ _ (input j)) num (pred j)) :
    let st := F.stage i c
    let state := F.advance i c q
    let save := namesStorage F store
    TagModels (view (i.val+1) state).pack.layout (layout.edges (i.val+1) state) (rows.ports (i.val+1))
      (F.savePrivatePrograms store rows (num ∘ pos) i c q old)
      (@Tracked.tags _ _ _ _ _ _ (Replay.batchFinite k Team (i.val+1)) _ _ _
        (DenseReplay.move F y hy pos save i.val i.isLt c input q)) num
      (carryPred ((normalizedStage e st q).trans (Retains.store (save i c q))).site (fun v => pred v.1 v.2)) := by
  intro st state save
  let _ : Fintype (Port k Team i.val) := Replay.batchFinite k Team i.val
  let edge := store.number i c q
  let outPort := rows.ports (i.val+1)
  let fresh := st.privatePrograms e q old (rows.sites i c q) edge outPort (rows.seeds i) (num ∘ pos)
  let atStage := DenseReplay.stageOutput st input e y hy pos q
  let test := carryPred (normalizedStage e st q).site (fun v => pred v.1 v.2)
  have ports {nf : ℕ} (dest : (Fin k × Port k P i.val) ↪ Fin nf)
      (cap : nf = k*rows.nPort i.val)
      (ids : ∀ u, (dest u).val = (Parallel.portRows k (rows.ports i.val) u).val) :
      TagModels (st.result e q).pack.layout edge dest
        (st.privatePrograms e q old (rows.sites i c q) edge dest (rows.seeds i) (num ∘ pos)) atStage.tags num test := by
    subst nf
    obtain rfl : dest = Parallel.portRows k (rows.ports i.val) := DFunLike.ext _ _ fun u => Fin.ext (ids u)
    exact DenseReplay.stage_tagModels st input e y hy pos num q old (rows.sites i c q) edge
      (rows.ports i.val) (rows.seeds i) (fun j => layout.edges i.val (c j)) (layout.inputCap i c)
      (layout.inputRows i c) pred models
  have h := ports outPort (layout.portCap i) (layout.portRows i)
  have saved := carryPrivatePrograms_tagModels (fin' := portFintype (k := k) (P := P) (b := i.val+1)) (st.result e q) (view (i.val+1) state) edge outPort
    (store.stored i c q) fresh atStage.tags num test h (layout.edges _ state) (layout.savedCap i c q)
    (layout.savedRows i c q)
  dsimp only [test] at saved
  rw [carryPred_trans] at saved
  exact saved

end Program
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
