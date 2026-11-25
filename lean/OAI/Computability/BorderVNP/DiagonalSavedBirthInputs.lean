import OAI.Computability.BorderVNP.DiagonalNativeBirthInputs

/-! # The original input word after the real second cable sort -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Cover Crossing Shortening Adaptive PublicParallel Packing Packing.Inherited Epoch.Round
open Diagonal.CellEntries Diagonal.ExternalSew Site.Programs Site.Lineage
open scoped Classical
attribute [local instance] portFintype
set_option maxHeartbeats 2000000
set_option maxRecDepth 6000

/-- Equality of actual complete input lanes after the public state has sorted
its cables and carried the inherited bank to the saved state. -/
theorem carryPrivatePrograms_birthInput {D d ne nf np : ℕ} {K Q I : Type} [Fintype I]
    {fin fin' : Fintype Q} {bits : Q → ℕ} (p saved : PlacedPack D Q bits K I d)
    (edge : p.pack.layout.Edge ↪ Fin ne) (port : Q ↪ Fin np) (stored : saved = p.dense edge)
    (old : @Site.Programs D Q fin bits p.pack.layout) (dest : saved.pack.layout.Edge ↪ Fin nf)
    (cap : nf = ne) (names : HEq dest (CutCircuit.denseRows p.pack.layout edge))
    (v : p.pack.layout.Site) (x : PowerInput saved.pack.layout) :
    let storage := privateStorage p saved edge stored
    let next := carryPrivatePrograms p saved edge stored (fin' := fin') old
    @birthInput D nf np Q fin' bits saved.pack.layout dest port (storage.site v) (next (storage.site v)) x =
      @birthInput D ne np Q fin bits p.pack.layout edge port v (old v) (storage.powerInput x) := by
  subst saved
  subst nf
  have enum : fin' = fin := Subsingleton.elim _ _
  subst fin'
  obtain rfl := eq_of_heq names
  let _ := fin
  exact birthInput_dense p.pack.layout edge port v (old v) x

namespace Program

variable {D m k b : ℕ} [NeZero D] {K I P : Type} [Field K] [Fintype I] [Fintype P]
    {bits : P → ℕ} {A : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
    {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    {e : PaidIdentity K D m} (F : Program (B := B) e view) (store : F.SaveNames) (rows : F.SiteRows)
    (layout : F.SiteModelRows store rows) (number : e.Entry → ℕ)

/-- The actual old host's immutable birth input agrees before and after a whole
normalized stage, on the physically reassembled cable/hook/port words. -/
theorem savePrivatePrograms_birthInput (i : Fin b) (c : Fin k → A i.val) (q : (F.stage i c).Index e)
    (old : ∀ j, Site.Programs (view i.val (c j)).pack.layout)
    (v : (raw (fun j => view i.val (c j))).layout.Site)
    (x : PowerInput (view (i.val+1) (F.advance i c q)).pack.layout) :
    let s := F.stage i c
    let state := F.advance i c q
    let save := namesStorage F store
    let host := ((normalizedStage e s q).trans (Retains.store (save i c q))).site v
    birthInput (view (i.val+1) state).pack.layout (layout.edges (i.val+1) state) (rows.ports (i.val+1))
      host (F.savePrivatePrograms store rows number i c q old host) x =
    birthInput (view i.val (c v.1)).pack.layout (layout.edges i.val (c v.1)) (rows.ports i.val) v.2 (old v.1 v.2)
      (DenseReplay.childPowerInput s e q v ((save i c q).powerInput x)) := by
  intro s state save host
  let edge := store.number i c q
  let outPort := rows.ports (i.val+1)
  let fresh := s.privatePrograms e q old (rows.sites i c q) edge outPort (rows.seeds i) number
  let oldInput := (save i c q).powerInput x
  have ports {nf : ℕ} (dest : (Fin k × Port k P i.val) ↪ Fin nf)
      (cap : nf = k*rows.nPort i.val)
      (ids : ∀ u, (dest u).val = (Parallel.portRows k (rows.ports i.val) u).val) :
      birthInput (s.result e q).pack.layout edge dest (.inl v)
          (s.privatePrograms e q old (rows.sites i c q) edge dest (rows.seeds i) number (.inl v)) oldInput =
      birthInput (view i.val (c v.1)).pack.layout (layout.edges i.val (c v.1)) (rows.ports i.val) v.2 (old v.1 v.2)
        (DenseReplay.childPowerInput s e q v oldInput) := by
    subst nf
    obtain rfl : dest = Parallel.portRows k (rows.ports i.val) := DFunLike.ext _ _ fun u => Fin.ext (ids u)
    exact DenseReplay.stage_birthInput s e q old (rows.sites i c q) edge (rows.ports i.val) (rows.seeds i) number
      (fun j => layout.edges i.val (c j)) (layout.inputCap i c) (layout.inputRows i c) v oldInput
  have saved := carryPrivatePrograms_birthInput (fin' := portFintype (k := k) (P := P) (b := i.val+1))
    (s.result e q) (view (i.val+1) state) edge outPort (store.stored i c q) fresh (layout.edges _ state)
    (layout.savedCap i c q) (layout.savedRows i c q) (.inl v) x
  exact saved.trans (ports outPort (layout.portCap i) (layout.portRows i))

end Program
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
