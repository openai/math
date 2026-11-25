import OAI.Computability.BorderVNP.DiagonalCompiledSeedPathUse
import OAI.Computability.BorderVNP.DiagonalFrozenSignedModels
import OAI.Computability.BorderVNP.DiagonalCheckedBirthWindow
import OAI.Computability.BorderVNP.PackedSeedCoreChoices
import OAI.Computability.BorderVNP.PackedSeedUseBankPrefix

/-! # The source record of each original verifier on a genuine routed core -/

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


open BorderVNP.Cube.Physical BorderVNP.Cube GridHosts CellAddresses BottomReports DiagonalTallyCellReports CellSparse
open Packing.Inherited.Site.Programs

local notation3 (prettyPrint := false) "edge₁" => FieldExport.mergedEdges (fieldSewParams G₁ axes d) hp (lastState).rows.edge
local notation "port₁" => finProdFinEquiv.toEmbedding
local notation "chan₀" => Shortening.PublicCapacity.Rows.edge (groupedGridRows G₀ axes d order position copies)
local notation "group₀" => Equiv.toEmbedding (Equiv.refl (Fin (GridHosts.tileCount (Fintype.card (Cube D)) d)))
local notation3 (prettyPrint := false) "birthWidth₀" => frozenSigned_birthWidth p fit W position code sites edges ports table
  C words good seeds free count pos num hp q
local notation3 (prettyPrint := false) "model₀" => frozenSigned_tagModels p fit W position code sites edges ports table
  C words good seeds free count y hy pos num hp q
local notation3 (prettyPrint := false) "tags₀" => fun c =>
  @Tracked.tags _ _ _ (Port (fan S) (Fin copies × Unit) T) _ _
    (Replay.batchFinite (fan S) (Fin copies × Unit) T) inferInstance _ _
    (EnrichedTape.tags p fit W position free count M leaf rfl y hy pos hp.block q (hidden c))
local notation3 (prettyPrint := false) "size" => placedSize net programs

/-- A routed core and the physically ordered returning reports yield the actual
source record for every original seed. It suffices to read each bundle's true
offset, actual pre-call bank size and augmented guard on its receiving cell. -/
theorem frozenSigned_reportSource {countCells numSites cn cd blocks cb ch ck cs nrows : ℕ} {Team : Type}
    (cell : (net).Site → Fin countCells) (siteID : (net).Site ↪ Fin numSites)
    (owners : (Packet cn cd blocks → Selector cn ck ch) → Fin cd → Team)
    (slot : LiveBit net cell ↪ Physical.Slot cn cd blocks (ch*cb))
    (bank : Ports (fun _ : FreeBlock R tiles => GridHosts.inputBlockWidth r (k+1) axes d))
    (routed : Routed (b:=cb) (s:=cs) owners) (raw : (c : Fin countCells) → Fin (externalBase net cell c size) → Bool)
    (origin : Fin nrows ≃ Fin ((fan S)^T) × (Fin axes → Deck (d+2))) (boxSlot offset : Fin nrows → ℕ)
    {l : ReportLayout} (out : Fin countCells → ReportCell l) (D₀ : Fin countCells → CellSparse.Directory) :
    let supply := pathSupply net cell edge₁ port₁ owners slot bank
    let home := fun j => cell (host (origin j))
    let pre := fun c => CellAddresses.bank net cell c size (privateWires net cell size c (raw c))
      (privateStaging net cell size c (raw c)) (supply routed c)
    let physical := fun j => lookup (pre (home j) ++ (out (home j)).bits)
    let originalRow := fun j => W.seedUseBundle position code sites edges ports chan₀ group₀ (origin j).2
      (boxSlot j) (offset j) copies (lookup (pre (home j)))
    let bundle := fun j => W.seedCoreBundle position code sites edges ports (origin j).2 (boxSlot j) (offset j) copies
    let z := extractBottom net cell siteID size owners slabs (fun _ => copies)
      (fun _ j => retainedLocation net programs host slabs (fun _ => copies) birthWidth₀ j) routed raw
    let a := rawPath net cell edge₁ programs owners routed raw
    CorePassed net cell siteID edge₁ port₁ programs host slabs (fun _ => copies) birthWidth₀ owners slot bank num tags₀ model₀ routed raw →
    (∀ c,(out c).bundles=(BundleDirectory.sourceRows home c.val).map originalRow) →
    (∀ c,(pre c).length=(out c).privateWires+(out c).supplied) →
    (∀ j,offset j=siteBase net cell (home j) siteID size ⟨host (origin j),rfl⟩) →
    (∀ c, ∃ os,(appendRows (D₀ c) (supplements ((pre c).length+l.gadgets*l.countWidth)
      ((BundleDirectory.sourceRows home c.val).map bundle))).guardedObservations (lookup (pre c++(out c).bits))=some os) →
    ∀ j,C.sourceRecordAt p fit W position code sites edges ports table words good seeds (num ∘ pos) free count
      hp q (hidden z) slot a bank origin boxSlot offset physical l j (host (origin j)) := by
  intro supply home pre physical originalRow bundle z a core grouped extent base accepted j
  let row := fun j : Fin nrows => W.seedUseBundle position code sites edges ports chan₀ group₀ (origin j).2
      (boxSlot j) (offset j) copies (physical j)
  let v := host (origin j)
  let c := home j
  let fine := W.seedSlab position code sites edges ports (origin j).2
  have sizes (i : Fin nrows) : (row i).useCount=(bundle i).useBits :=
    W.seedUseBundle_count position code sites edges ports chan₀ group₀ (origin i).2
      (boxSlot i) (offset i) copies (physical i)
  have sameRows : row=originalRow := by
    funext t
    let vt := host (origin t)
    let ct := cell vt
    let L := programs vt
    have width : copies*(W.seedSlab position code sites edges ports (origin t).2).stride ≤ size vt :=
      (Eq.mp (congrArg (fun n => n ≤ size vt) (birthWidth₀ (origin t)))
        (L.retention.work_le.trans (Nat.le_add_right _ _)))
    have site := siteBase_fits net cell ct siteID size ⟨vt,rfl⟩
    have cap : externalBase net cell ct size ≤ (pre ct).length := by
      simp only [pre,CellAddresses.bank,List.length_append,List.length_ofFn,externalBase]
      omega
    apply W.seedUseBundle_append
    rw [base t]
    exact (Nat.add_le_add_left width _).trans (site.trans cap)
  have typedRows : (out c).bundles=(BundleDirectory.sourceRows home c.val).map row := by
    rw [sameRows]
    exact grouped c
  obtain ⟨os,returned⟩ := accepted c
  have result := CorePassed.groupedSeedReport net cell siteID edge₁ port₁ programs host slabs
    (fun _ => copies) birthWidth₀ owners slot bank num tags₀ model₀ routed raw core origin j (D₀ c) bundle row (out c)
    sizes typedRows (extent c) ⟨base j,rfl,rfl,rfl⟩ os returned
  let input := inputWords net edge₁ port₁ v (pathEdges slot a v) (fun f => bank f.val) ∘ Fin.cast (programs v).size
  let work := rawBirth net cell siteID programs raw v
  let original := Inherited.bits work ((programs v).retention.readInput input)
  have sameBirth : (programs v).birth=(baseProg (origin j).2).birth :=
    (M).terminalPrivatePrograms_birth rows (num ∘ pos) leaf baseProg q (origin j).1 (origin j).2
  have actual : (programs v).birth=W.seedBorn position code sites edges ports chan₀ group₀ (origin j).2 copies := sameBirth
  have guesses (i : Fin copies) : ((guessedWords (W.routedFine position) (GridPlacement.cell position W.route)
      (origin j).2 edges).symm (hidden z (origin j).1 i (origin j).2)) = z (origin j) i := by
    rw [W.bottomChoicesEquiv_read position edges slabs (fun _ => rfl),Equiv.symm_apply_apply]
    rfl
  have chosen : (fun i => (guessedWords (W.routedFine position) (GridPlacement.cell position W.route)
      (origin j).2 edges).symm (hidden z (origin j).1 i (origin j).2)) = z (origin j) := funext guesses
  refine ⟨work,?_⟩
  let x := atPathHost net slot a bank v
  have sameInput : (inputWords net edge₁ port₁ v (fun u => x.edges u.val) (fun u => x.ports u.val)
      ∘ Fin.cast (programs v).size) = input := by
    have wires : (fun u : Incident net v => x.edges u.val) = pathEdges slot a v := funext (atPathHost_edges net slot a bank v)
    rw [wires]
    rfl
  change Nonempty (W.CheckedBirthData position code sites edges ports chan₀ group₀ (origin j).2
    (physical j) (boxSlot j) (offset j) (hidden z (origin j).1) l
    (Inherited.bits work ((programs v).retention.readInput _)))
  rw [sameInput]
  unfold WiredWitness.CheckedBirthData
  rw [chosen,←actual]
  let family (atBase : ℕ) := Nonempty (WiredWitness.SeedBirthReceipt copies atBase fine
    (programs v).birth (bundle j).factors (row j) (physical j) (z (origin j)) l original)
  exact (congrArg family (base j)).mpr result

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
