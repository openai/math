import OAI.Computability.BorderVNP.DiagonalTrackedPowerRead
import OAI.Computability.BorderVNP.DiagonalStageSavedTags
import OAI.Computability.BorderVNP.DiagonalFlattenTagModels

/-! # The physical birth input at a retained site

The private program consumes incidence words in its actual sorted order.
A site that survives parallel composition, a cable sort and a selected crossing
reads the same original input lanes as the inverse transport of its local table.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Site.Lineage

open Crossing Shortening DirectoryCircuit Diagonal.CellEntries Site.Programs
open scoped Classical

variable {D ne np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
  (N : Network D P bits) (edges : N.Edge ↪ Fin ne) (ports : P ↪ Fin np) (v : N.Site)
  (s : Lineage (Inherited.incoming N v))

/-- The exact word delivered to the immutable birth site, extended by zero
beyond its true input extent so that transport never depends on a width cast. -/
noncomputable def birthInput (x : PowerInput N) : ℕ → Bool :=
  extendWork (s.retention.readInput (inputWords N edges ports v (fun i => x.edges i.val) (fun p => x.ports p.val) ∘ Fin.cast s.size))

/-- Sorting physical cables reuses the old birth checker on the same input vector. -/
theorem birthInput_dense (x : PowerInput (Names.denseLayout N edges)) :
    birthInput (Names.denseLayout N edges) (CutCircuit.denseRows N edges) ports v
      (s.castWidth (dense_incoming N edges v).symm) x =
    birthInput N edges ports v s ((Storage.dense N edges).powerInput x) := by
  apply congrArg (fun a => extendWork (s.retention.readInput a))
  funext j
  exact dense_inputWords N edges ports v (fun u => x.edges u.val) (fun u => x.ports u.val) (Fin.cast s.size j)

/-- The selected child's raw edge and port words retain their ordinals
inside the disjoint union. -/
theorem birthInput_parallel {k : ℕ} (child : Fin k → Network D P bits) (rows : ∀ i, (child i).Edge ↪ Fin ne)
    (i : Fin k) (a : (child i).Site) (p : Lineage (Inherited.incoming (child i) a))
    (x : PowerInput (Network.parallel child)) :
    birthInput (Network.parallel child) (PublicParallel.parallelName rows) (Parallel.portRows k ports) ⟨i,a⟩
      (p.castWidth (Parallel.incoming_eq child i a).symm) x =
    birthInput (child i) (rows i) ports a p ⟨fun c => x.edges ⟨i,c⟩,fun b => x.ports (i,b)⟩ := by
  apply congrArg (fun z => extendWork (p.retention.readInput z))
  funext j
  exact parallel_inputWords child rows ports i a (fun u => x.edges u.val) (fun u => x.ports u.val) (Fin.cast p.size j)

/-- Renumbering through equal numerical rows preserves every physical birth lane. -/
theorem birthInput_numbered {ne' : ℕ} (edges' : N.Edge ↪ Fin ne') (cap : ne'=ne)
    (num : ∀ c, (edges' c).val = (edges c).val) (x : PowerInput N) :
    birthInput N edges' ports v s x = birthInput N edges ports v s x := by
  subst ne'
  obtain rfl : edges' = edges := DFunLike.ext _ _ fun c => Fin.ext (num c)
  rfl

section Layer

open Shortening.CombiningStep
open private extendWires from OAI.Computability.BorderVNP.PackedInheritedRoundValue
variable {m next : ℕ} [NeZero D] {K : Type} [Field K]
    (e : PaidIdentity K D m) (p : Pack D P bits K) {A : Type} [Fintype A]
    (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A) (name : A → ℕ)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
    (b : p.layout.Site) (oldID : p.layout.Edge ↪ Fin ne)
    (nextID : (output e p bin perm positive first q).layout.Edge ↪ Fin next)
    (prior : Lineage (Inherited.incoming p.layout b))

/-- A physically retained checker reads each old cable band at the selected
successor hook and each external bit at its original port. -/
theorem birthInput_orderedLayer (x : PowerInput (output e p bin perm positive first q).layout) :
    birthInput (output e p bin perm positive first q).layout nextID ports (.inl b)
      (orderedLayer e p bin perm name positive first q b oldID nextID ports prior) x =
    birthInput p.layout oldID ports b prior
      ⟨extendWires p.layout b (oldWireWords e p bin perm positive first q x.edges b),x.ports⟩ := by
  let z := oldWireWords e p bin perm positive first q x.edges b
  have hz : (fun c : Incident p.layout b => extendWires p.layout b z c.val) = z := by
    funext c j
    exact dite_eq_left c.property
  have lanes := layerRead_inputs e p bin perm positive first q b oldID nextID ports x.edges x.ports
  let staged := successorInput e p bin perm positive first q b nextID ports x.edges x.ports
  let sourceLane := layerRead e p bin perm positive first q b oldID nextID ports
  change extendWork (prior.retention.readInput ((staged ∘ sourceLane) ∘ Fin.cast prior.size)) =
    extendWork (prior.retention.readInput ((inputWords p.layout oldID ports b
      (fun c => extendWires p.layout b z c.val) (oldPortWords p x.ports b)) ∘ Fin.cast prior.size))
  rw [hz]
  exact congrArg (fun a => extendWork (prior.retention.readInput (a ∘ Fin.cast prior.size))) lanes

end Layer

end Packing.Inherited.Site.Lineage

namespace Diagonal.CellEntries.DenseReplay

open Cover Crossing Shortening Adaptive PublicParallel Packing Packing.Inherited PackedHistoryCircuit.Normalized
open Diagonal.ExternalSew Site.Programs Site.Lineage
open private extendWires from OAI.Computability.BorderVNP.PackedInheritedRoundValue
open scoped Classical
set_option maxHeartbeats 1800000

variable {D m k d next : ℕ} [NeZero D] {P I K B : Type} [Fintype P] [Fintype I] [Fintype B]
    [Field K] {bits : P → ℕ} {child : Fin k → PlacedPack D P bits K I d}
    (s : Stage m B next child) (e : PaidIdentity K D m) (q : s.Index e) (old : ∀ j, Site.Programs (child j).pack.layout)
    {ns ne np cap : ℕ} (siteID : (s.result e q).pack.layout.Site ↪ Fin ns)
    (edgeID : (s.result e q).pack.layout.Edge ↪ Fin ne) (port : P ↪ Fin np)
    (seed : ((I → Deck (next+1)) × B) → ℕ) (position : e.Entry → ℕ) (rows : ∀ j, (child j).pack.layout.Edge ↪ Fin cap)
    (hcap : s.rowCount=k*cap) (hslot : ∀ z, (s.slot z).val = (parallelName rows z).val)

include hcap hslot in
/-- On the chosen actual histogram, the bank's retained input agrees with
the endpoint and band words reconstructed by the selected mathematical site. -/
theorem stage_birthInput (v : (raw child).layout.Site) (x : PowerInput (s.result e q).pack.layout) :
    let progs := s.privatePrograms e q old siteID edgeID (Parallel.portRows k port) seed position
    birthInput (s.result e q).pack.layout edgeID (Parallel.portRows k port) (.inl v) (progs (.inl v)) x =
      birthInput (child v.1).pack.layout (rows v.1) port v.2 (old v.1 v.2) (childPowerInput s e q v x) := by
  intro progs
  let p := old v.1 v.2
  let ports := Parallel.portRows k port
  let before := CutCircuit.denseRows (raw child).layout s.slot
  let parallel := p.castWidth (Parallel.incoming_eq (fun j => (child j).pack.layout) v.1 v.2).symm
  let atInput := p.castWidth (s.input_incoming v.1 v.2).symm
  let y := cutPowerInput s e q v x
  have h := birthInput_orderedLayer ports e s.input s.label s.perm seed s.orient (0,false) q v before edgeID atInput x
  let rawInput := (Storage.dense (raw child).layout s.slot).powerInput y
  exact h.trans ((birthInput_dense (raw child).layout s.slot ports v parallel y).trans
    ((birthInput_numbered (raw child).layout (parallelName rows) ports v parallel s.slot hcap hslot rawInput).trans
      (birthInput_parallel port (fun j => (child j).pack.layout) rows v.1 v.2 p rawInput)))

end Diagonal.CellEntries.DenseReplay

end BorderVNP
end Computability
end OAI
