import OAI.Computability.BorderVNP.PackedFrozenNativePort
import OAI.Computability.BorderVNP.PackedSeedBirthTagModels
import OAI.Computability.BorderVNP.DiagonalEnrichedSewnTagModels
import OAI.Computability.BorderVNP.PackedSelectedPrivateFieldRows
import OAI.Computability.BorderVNP.DiagonalEnrichedTape

/-! # The signed private program on the same frozen grid as the public compiler -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.DeckGrid Packing.PhysicalEpochs Diagonal Diagonal.CellEntries
open Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP
open VPVNP.ParseGrammar EnrichedOuter TeamScales BorderVNP.Cube.Physical.NativeAssignments
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 3200000
set_option maxRecDepth 7200
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {K E Gadget : Type} [Field K] [Field E] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {R r pins link k d a regs rw ec width s copies T w : ℕ}
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs rw ec width ≤ k+1)
local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount (Fintype.card (Cube D)) d
local notation "G₀" => tapeTemplate p fit pins
variable {order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D (Fintype.card (Cube D)) d order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : PairedParameters k s ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth (tapeTemplate p fit pins)) ↪ Fin np)
    (table : (seedBundle (tapeTemplate p fit pins) (Fintype.card (Cube D)) d order position copies).Tables K)
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} {deep : S.floor+1+S.drop*T ≤ d+1}
    (C : Compiled (fun _ : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) =>
      copies*GridHosts.inputBlockWidth r (k+1) (Fintype.card (Cube D)) d) deep budget cap w)
    (words : Boundary.Pins S (d+1) (boundary S (d+1)) w 0 → Bool)
    (good : Boundary.Good budget 0 (Boundary.seedState S (tapeTemplate p fit pins) d order position copies table words))
    (seeds : ∀ h, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) h) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (count : (fan S)^T*copies = R+1)
    (y : e.Entry → E) (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget) (num : Gadget ↪ ℕ)
local notation "goodState" => Boundary.Good (S := S) (start := d+1) (P := Fin tiles)
  (bits := fun _ => copies*GridHosts.inputBlockWidth r (k+1) axes d)
  (shape := boundary S (d+1)) (w := w) budget
local notation "leaf" => (Subtype.mk (Boundary.seedState S G₀ d order position copies table words) good : Admissible goodState 0)
local notation "baseProg" => Boundary.wiredSeedStatePrograms S W position code sites edges ports copies table words
local notation "source" => EnrichedTape.base (Gadget := Gadget) p fit W position leaf rfl
local notation "key" => Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d))
local notation "M" => C.machine
local notation "rows" => C.privateSiteRows key seeds
local notation "oldPorts" => privatePorts S key
local notation "G₁" => SewnTape.wiring p fit free pins
variable (hp : (fieldSewParams (SewnTape.wiring p fit free pins) (Fintype.card (Cube D)) d).Valid)
    (q : (packHistory (Subtype.mk (Boundary.seedState S (tapeTemplate p fit pins) d order position copies table words) good)
      C.machine.epoch T).Index)
local notation3 (prettyPrint := false) "lastState" => ((packHistory (Pack := Admissible goodState) (K := fan S) leaf (M).epoch T).term q).val
local notation3 (prettyPrint := false) "net" => EnrichedTape.network p fit position free count M leaf rfl q
local notation3 (prettyPrint := false) "host" => ((Equiv.sigmaEquivProd (Fin ((fan S)^T)) (Fin axes → Deck (d+2))).symm.toEmbedding.trans
  (enrichedOuterHosts M leaf q).site)
local notation3 (prettyPrint := false) "lastProgs" => C.machine.terminalPrivatePrograms rows (num ∘ pos) leaf baseProg q
local notation3 (prettyPrint := false) "programs" => enrichedSewnPrograms G₁ axes d order position count M leaf rfl (Flat.portRows T (oldPorts T))
  hp q lastProgs
local notation3 (prettyPrint := false) "slabs" => fun j : Fin ((fan S)^T) × (Fin axes → Deck (d+2)) => W.seedSlab position code sites edges ports j.2
local notation3 (prettyPrint := false) "hidden" => W.bottomChoicesEquiv position edges slabs (fun _ => rfl)

/-- Every original verifier's private work range is present at its physical
host, with exactly the copy multiplicity and stride used to extract it. -/
theorem frozenSigned_birthWidth (j : Fin ((fan S)^T) × (Fin axes → Deck (d+2))) :
    (programs (host j)).birth.work = copies*(slabs j).stride := by
  exact congrArg Site.work (C.machine.terminalPrivatePrograms_birth rows (num ∘ pos) leaf baseProg q j.1 j.2)

/-- The private programs produced from this frozen public initializer model
the exact signed tag at every sewn site and every local input. The predicate
on the retained work bank is the tuple of original verifier choices decoded
from its own physical copy slots. -/
theorem frozenSigned_tagModels (z : BottomChoices slabs (fun _ => copies)) :
    Site.Programs.TagModels net (FieldExport.mergedEdges (fieldSewParams G₁ axes d) hp (lastState).rows.edge)
      finProdFinEquiv.toEmbedding programs
      (@Tracked.tags _ _ _ (Port (fan S) (Fin copies × Unit) T) (PairedParameters k s) Gadget
        (Replay.batchFinite (fan S) (Fin copies × Unit) T) inferInstance _ _ (EnrichedTape.tags p fit W position free count M leaf rfl y hy pos hp.block q (hidden z)))
      num (Site.Programs.carryPred host (birthPredicate slabs (fun _ => copies) z)) := by
  let cond := fun (h : Fin copies → W.Hidden position) c => W.seedBirthPredicate position code sites edges ports c h
  have seed (h : Fin copies → W.Hidden position) :
      Site.Programs.TagModels (leaf).val.pack.layout (leaf).val.rows.edge (oldPorts 0) baseProg (source h).tags num (cond h) := by
    let original := (Equiv.refl (Fin tiles)).toEmbedding
    have model := Boundary.wiredSeedStatePrograms_tagModels S W position code sites edges ports copies num h table words
    let outer := portFintype (k := fan S) (P := Fin tiles) (b := 0)
    exact @Site.Programs.TagModels.renumber _ _ _ _ outer _ _ _ (leaf).val.pack.layout
      (leaf).val.rows.edge original baseProg (source h).tags num (cond h) _ _ model _ (oldPorts 0) rfl
      (seedPortCount (D := D) d).symm (fun _ => rfl) (fun _ => rfl)
  have model := terminalSewnTagModels G₁ axes d order position count M leaf rfl hp q y hy pos source rows oldPorts
    (C.privateFieldRows key seeds) num baseProg cond seed (hidden z)
  intro v
  apply (model v).congrPred
  intro g
  constructor
  · intro h j hj
    exact (Boundary.seedBirthPredicate_bottomChoices W position code sites edges ports copies z j.1 j.2 _).mp
      (h ⟨j.1,j.2⟩ hj)
  · intro h j hj
    exact (Boundary.seedBirthPredicate_bottomChoices W position code sites edges ports copies z j.1 j.2 _).mpr
      (h (j.1,j.2) hj)

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
