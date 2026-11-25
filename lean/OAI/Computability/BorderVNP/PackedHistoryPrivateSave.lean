import OAI.Computability.BorderVNP.PackedHistoryPrivateModels

/-! # Exact fields on the public saved lineage arrays

Each site's old guesses and signed observations persist in the actual saved
program. The local field model follows the very same row and port injections
as the normalized epoch, including the equality transport at its stored state.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Site.Programs

open Crossing Shortening Packing Inherited

variable {D ne nf np : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} {K : Type*} [Field K]
    (p : Pack D P bits K) (edge : p.layout.Edge ↪ Fin ne) (port : P ↪ Fin np)
    (s : Site.Programs p.layout) (values : ℕ → K)

/-- The lineage program and field model survive stable saving of the actual occupied rows. -/
theorem FieldModels.densePack (model : FieldModels p edge port s values) :
    let saved := DirectoryCircuit.densePack p edge
    FieldModels saved (CutCircuit.denseRows p.layout edge) port
      (fun v => (s v).castWidth (dense_incoming p.layout edge v).symm) values := by
  intro saved v
  exact ⟨(model v).1,Site.Models.densePack p edge port v (s v).program (s v).size _ (model v).2⟩

end Packing.Inherited.Site.Programs

namespace PackedHistoryCircuit.Normalized

open Crossing Shortening Shortening.Adaptive Shortening.PublicParallel Cover Epoch Epoch.Round Packing Packing.Inherited
open scoped Classical
attribute [local instance] portFintype

section CurrentStage

variable {D m k d d' E np ns ne nf : ℕ} [NeZero D] {K P I B : Type} [Field K]
    [Fintype P] [Fintype I] [Fintype B] {bits : P → ℕ} {child : Fin k → PlacedPack D P bits K I d}
    (s : Stage m B d' child) (e : PaidIdentity K D m) (q : s.Index e)
    (old : ∀ j, Site.Programs (child j).pack.layout)
    (rows : ∀ j, (child j).pack.layout.Edge ↪ Fin E) (port : P ↪ Fin np)
    (hcap : s.rowCount = k*E) (hslot : ∀ z, (s.slot z).val = (parallelName rows z).val)
    (site : (s.result e q).pack.layout.Site ↪ Fin ns) (edge : (s.result e q).pack.layout.Edge ↪ Fin ne)
    (seed : ((I → Deck (d'+1)) × B) → ℕ) (number : e.Entry → ℕ)
    (values : ℕ → K) (paid : ∀ i, values (number i) = e.entry i)
    (models : ∀ i, Site.Programs.FieldModels (child i).pack (rows i) port (old i) values)

include hcap hslot paid models in
/-- The stage field model is valid for any exterior rectangle having exactly
the row ordinals assigned by parallel copy-and-port embedding. -/
theorem Stage.privatePrograms_ports (dest : Fin k × P ↪ Fin nf)
    (hc : nf = k*np) (hd : ∀ u, (dest u).val = (Parallel.portRows k port u).val) :
    Site.Programs.FieldModels (s.result e q).pack edge dest (s.privatePrograms e q old site edge dest seed number) values := by
  subst nf
  obtain rfl : dest = Parallel.portRows k port := DFunLike.ext _ _ fun u => Fin.ext (hd u)
  exact s.privatePrograms_models e q old rows port hcap hslot site edge seed number values paid models

end CurrentStage

/-- Stable saving carries every local model through the exact physical pack
equality, including a change of finite enumeration at the nested port level. -/
theorem carryPrivatePrograms_models {D d ne nf np : ℕ} {K Q I : Type} [Field K] [Fintype I]
    {fin fin' : Fintype Q} {bits : Q → ℕ} (p saved : PlacedPack D Q bits K I d)
    (edge : p.pack.layout.Edge ↪ Fin ne) (port : Q ↪ Fin np) (stored : saved = p.dense edge)
    (old : @Site.Programs D Q fin bits p.pack.layout) (values : ℕ → K)
    (model : @Site.Programs.FieldModels D ne np K _ Q fin bits p.pack edge port old values)
    (dest : saved.pack.layout.Edge ↪ Fin nf) (cap : nf = ne) (names : HEq dest (CutCircuit.denseRows p.pack.layout edge)) :
    @Site.Programs.FieldModels D nf np K _ Q fin' bits saved.pack dest port
      (carryPrivatePrograms p saved edge stored (fin' := fin') old) values := by
  subst saved
  subst nf
  obtain rfl : fin' = fin := Subsingleton.elim _ _
  obtain rfl := eq_of_heq names
  exact Site.Programs.FieldModels.densePack p.pack edge port old values model

namespace Program

variable {D m k E nf : ℕ} [NeZero D] {K I P : Type} [Field K] [Fintype I] [Fintype P] {bits : P → ℕ}
    {rounds : ℕ} {A : ℕ → Type*} {Bin : Fin rounds → Type} [∀ i, Fintype (Bin i)]
    {depth : ℕ → ℕ} {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    {e : PaidIdentity K D m} (F : Program (B := Bin) e view) (store : F.SaveNames) (directory : F.SiteRows)
    (number : e.Entry → ℕ) (i : Fin rounds) (c : Fin k → A i.val) (q : (F.stage i c).Index e)
    (old : ∀ j, Site.Programs (view i.val (c j)).pack.layout)
    (rows : ∀ j, (view i.val (c j)).pack.layout.Edge ↪ Fin E)
    (hcap : (F.stage i c).rowCount = k*E) (hslot : ∀ z, ((F.stage i c).slot z).val = (parallelName rows z).val)
    (dest : (view (i.val+1) (F.advance i c q)).pack.layout.Edge ↪ Fin nf)
    (savedCap : nf = store.capacity i c q)
    (savedRows : HEq dest (CutCircuit.denseRows ((F.stage i c).result e q).pack.layout (store.number i c q)))
    (portCap : directory.nPort (i.val+1) = k*directory.nPort i.val)
    (portRows : ∀ u, (directory.ports (i.val+1) u).val = (Parallel.portRows k (directory.ports i.val) u).val)
    (values : ℕ → K) (paid : ∀ a, values (number a) = e.entry a)
    (models : ∀ j, Site.Programs.FieldModels (view i.val (c j)).pack (rows j) (directory.ports i.val) (old j) values)

include hcap hslot savedCap savedRows portCap portRows paid models in
/-- Exact local models for the very programs returned by the actual receipt's dense
save, at the public row names consumed by the next stage. -/
theorem savePrivatePrograms_models :
    Site.Programs.FieldModels (view (i.val+1) (F.advance i c q)).pack dest (directory.ports (i.val+1))
      (F.savePrivatePrograms store directory number i c q old) values := by
  let st := F.stage i c
  let edge := store.number i c q
  let newPort := directory.ports (i.val+1)
  let fresh := st.privatePrograms e q old (directory.sites i c q) edge newPort (directory.seeds i) number
  have hm := st.privatePrograms_ports e q old rows (directory.ports i.val) hcap hslot (directory.sites i c q)
    edge (directory.seeds i) number values paid models newPort portCap portRows
  exact carryPrivatePrograms_models (st.result e q) (view (i.val+1) (F.advance i c q)) edge newPort
    (store.stored i c q) fresh values hm dest savedCap savedRows

end Program
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
