import OAI.Computability.BorderVNP.DiagonalSelectedTermCountBounds
import OAI.Computability.BorderVNP.DiagonalPinnedPacketRow

/-! # Physical and original tallies on the selected signed decoder -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.DeckGrid Packing.PhysicalEpochs Diagonal Diagonal.CellEntries
open Diagonal.ExternalSew TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open EnrichedOuter TeamScales BorderVNP.Cube.Physical.NativeAssignments BorderVNP.Cube
open Branch ResidueBox ResidueIndex ResiduePins
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 7000
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {K F : Type} [Field K] [Field F] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {R r pin link k d a regs rw ec width s copies T header work : ℕ}
    (plan : SeedPlan S (k+1) r d T copies header work) (cube : FixedCube F) (φ : F →+* K)
    (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) {qchar : ℕ}
    {common : CommonField e (φ ∘ cube.table) qchar k s ord} (chart : AdvisedBranch common)
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs rw ec width ≤ k+1)
local notation3 (prettyPrint := false) "pins" => (pairedTableParameters (k+1) s+2)*pin
local notation3 (prettyPrint := false) "scalarIDs" => e.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width
local notation3 (prettyPrint := false) "code" => (ParseTable.numberedLabelEquiv ord k s).toEmbedding.trans Fin.valEmbedding
local notation3 (prettyPrint := false) "num" => (Fintype.equivFin (scalarIDs)).toEmbedding.trans Fin.valEmbedding
local notation3 (prettyPrint := false) "axes" => Fintype.card (Cube D)
local notation3 (prettyPrint := false) "tiles" => GridHosts.tileCount axes d
local notation3 (prettyPrint := false) "G₀" => tapeTemplate p fit pins
variable {order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate p fit ((pairedTableParameters (k+1) s+2)*pin)) (Fin.last k) D (Fintype.card (Cube D)) d order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth (tapeTemplate p fit ((pairedTableParameters (k+1) s+2)*pin))) ↪ Fin np)
    (table : (seedBundle (tapeTemplate p fit ((pairedTableParameters (k+1) s+2)*pin)) (Fintype.card (Cube D)) d order position copies).Tables K)
local notation3 (prettyPrint := false) "M" => plan.compiled.machine
local notation3 (prettyPrint := false) "mass" => initialMass (D:=D) (k+1) r d copies header
local notation3 (prettyPrint := false) "goodState" => Boundary.Good (S := S) (start := d+1) (P := Fin tiles)
  (bits := fun _ => copies*GridHosts.inputBlockWidth r (k+1) axes d)
  (shape := boundary S (d+1)) (w := 60*logWidth r (k+1)) (boundaryBudget S mass)
variable (words : Boundary.Pins S (d+1) (boundary S (d+1)) (60*logWidth r (k+1)) 0 → Bool)
    (good : Boundary.Good (boundaryBudget S (initialMass (D:=D) (k+1) r d copies header)) 0 (Boundary.seedState S (tapeTemplate p fit ((pairedTableParameters (k+1) s+2)*pin)) d order position copies table words))
    (seeds : ∀ h, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) h) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (count : (fan S)^T*copies = R+1)
local notation3 (prettyPrint := false) "leaf" => (Subtype.mk (Boundary.seedState S G₀ d order position copies table words) good : Admissible goodState 0)
local notation3 (prettyPrint := false) "G₁" => SewnTape.wiring p fit free pins
local notation3 (prettyPrint := false) "Y" => chart.gadgets ∘ Sum.inl
local notation3 (prettyPrint := false) "Hist" => (packHistory (Pack := Admissible goodState) (K := fan S) leaf (M).epoch T).Index
variable (hp : (fieldSewParams (SewnTape.wiring p fit free ((pairedTableParameters (k+1) s+2)*pin)) (Fintype.card (Cube D)) d).Valid)
    (α ξ : ℝ) (calibrated : plan.SignedLabelRows count link (cube.pred+1) α ξ)
    (lit : (UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a) = literal α (k+1))
    (hd : 0 < BorderVNP.Cube.alphabet α (k+1)) {cells : ℕ}
    (number : (Cube D → Deck (depth S (d+1) T+1)) ≃ Fin cells) (gap : ℕ)

attribute [local instance] selectedBatchFinite
attribute [local irreducible] UniversalMachine.programPrefix Nat.clog TeamTapeInput.digits TeamTapeInput.parameters VPVNP.BurstRAM.wordBits

local notation3 (prettyPrint := false) "packets" => plan.signedPackets count G₀ order position W code sites edges ports table
  words good cube α ξ calibrated lit hd hp number gap
local notation3 (prettyPrint := false) "banks" => canonicalBank (G := G₁) hp.block (GridHosts.gridRoom G₁ Fintype.card_pos)
local notation3 (prettyPrint := false) "tags" => EnrichedTape.tags (Gadget := scalarIDs) p fit W position free count M leaf rfl
  Y chart.preserves_paid Sum.inl hp.block
local notation3 (prettyPrint := false) "dir" => signedCoreDirectory plan p fit W position code sites edges ports table words
  good seeds free count Sum.inl num hp
local notation3 (prettyPrint := false) "rawWidth" => Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool
local notation3 (prettyPrint := false) "put" => (Sum.inr : TableEntry cube.pred cube.b cube.h cube.copies cube.width → scalarIDs)

local notation3 (prettyPrint := false) "Term" => selectedSignedTerms plan cube φ ord chart p fit W position sites edges ports table
  words good free count hp α ξ calibrated lit hd number gap

local notation3 (prettyPrint := false) "decode" => selectedSignedDecode plan cube φ ord chart p fit W position sites edges ports table
  words good seeds free count hp α ξ calibrated lit hd number gap


open Packing.CellAddresses Packing.BottomReports Packing.RoutingOutputs.NativeDemands

local notation3 (prettyPrint := false) "seedCall(" f ")" => f
  (D:=D) (m:=m) (K:=K) (Gadget:=scalarIDs) (e:=e) (S:=S) (R:=R) (r:=r) («pins»:=pins)
  (link:=link) (k:=k) (d:=d) (a:=a) (regs:=regs) (rw:=rw) (ec:=ec) (width:=width) (s:=s)
  (copies:=copies) (T:=T) (header:=header) (work:=work) (order:=order) (ns:=ns) (ne:=ne) (np:=np)
  (F:=F) (cells:=cells)
local notation3 (prettyPrint := false) "thisDir(" h ")" => seedCall(signedCoreDirectory) plan p fit W position code sites edges ports table words
  good seeds free count Sum.inl num hp h cube α ξ calibrated lit hd number gap
local notation3 (prettyPrint := false) "chosen" => signedDecodedPath plan cube φ ord chart p fit W position sites edges ports table
  words good seeds free count hp α ξ calibrated lit hd number gap
local notation3 (prettyPrint := false) "counts" => signedTermCounts plan cube φ ord chart p fit W position sites edges ports table
  words good free count hp α ξ calibrated lit hd number gap

include chart in
/-- The row read by the selected private calls, indexed by the chart's
actual grammar-parameter and scalar directories. -/
noncomputable def signedRecoveredCounts (q : Hist) (raw : rawWidth) (v : (thisDir(q)).Route cube.width × (thisDir(q)).Bank) :
    Fin (R+1) → Fin (pairedTableParameters (k+1) s + Fintype.card (scalarIDs)) → ℕ :=
  seedCall(signedRawPacketRow) plan p fit W position code sites edges ports table words good seeds free count
    (chart.gadgets ∘ Sum.inl) chart.preserves_paid Sum.inl num hp q cube α ξ calibrated lit hd number gap
    ord (Fintype.equivFin (scalarIDs)) put (banks raw) v

local notation3 (prettyPrint := false) "readCounts(" h ")" => signedRecoveredCounts plan cube φ ord chart p fit W position sites edges ports table
  words good seeds free count hp α ξ calibrated lit hd number gap h

include chart in
/-- Each real reported row is the original row of this exact guarded
choice under the canonical substituted input. -/
theorem signedDecodedTerm_sameCounts (q : Hist) (raw : rawWidth)
    (v : {a : (thisDir(q)).Route cube.width × (thisDir(q)).Bank // (thisDir(q)).Guard (banks raw) a}) :
    readCounts(q) raw v.val = counts raw (chosen raw q v) :=
  seedCall(signedPinnedPaths_nativeRow) plan p fit W position code sites edges ports table words good seeds free count
    (chart.gadgets ∘ Sum.inl) chart.preserves_paid Sum.inl num hp q cube α ξ calibrated lit hd number gap ord (Fintype.equivFin (scalarIDs))
    put banks raw v

/-- Every original term at this public history is recovered, including
inside the numeric rows supplied to the return verifier. -/
theorem signedOriginalTerm_sameCounts (q : Hist) (raw : rawWidth) (z : Term raw q) :
    readCounts(q) raw ((decode raw q).symm z).val = counts raw ⟨q,z⟩ := by
  refine (plan.signedDecodedTerm_sameCounts cube φ ord chart p fit W position sites edges ports table words good seeds
    free count hp α ξ calibrated lit hd number gap q raw ((decode raw q).symm z)).trans ?_
  exact congrArg (fun t => counts raw ⟨q,t⟩) ((decode raw q).apply_symm_apply z)

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator CellMacro.Generator TeamContraction.JointHeader TeamContraction.ProcessorSlots
open BorderVNP.Epoch.Round

variable {extra phase deg Q scaleA scaleB scaleJ : ℕ} (scales : EpochScales S (cube.pred+1) extra)
    (b : JointSchedule.{0} scales (phase+1) deg Q scaleA scaleB scaleJ)
    (room : ReaderTallyInputsAt cube b (k+1)) (batchEq : r=stretch b.ρ (k+1)) (stateEq : s=stretch b.σ (k+1))
    (teamsEq : R=b.physical.teamsPred (k+1)) (alpha : α=scales.α) (fraction : ξ=(scales.τ:ℝ)/5)
    (fields : RecordData (Boundary.seedState S (tapeTemplate p fit ((pairedTableParameters (k+1) s+2)*pin))
      d order position copies table words).pack.layout) {startCap : ℕ}
    (cover : (CoverScale.sites (Cube D) (d+1):ℝ) ≤ r*((k+1:ℕ):ℝ)^(9/10:ℝ))
    (small : 1+startCap ≤ TeamScales.width (k+1) (1/2:ℝ))
    (bound : PhysicalEpochs.SiteCap (Boundary.seedState S (tapeTemplate p fit ((pairedTableParameters (k+1) s+2)*pin))
      d order position copies table words).route fields true startCap) (time : T≤epochs scales.τ (k+1))

include room batchEq stateEq teamsEq alpha fraction fields cover small bound time in
/-- The true emitted row and the sum emitted by all teams fit the actual
machine word on every canonical selected route. -/
theorem signedRecoveredCounts_word (q : Hist) (raw : rawWidth)
    (v : {a : (thisDir(q)).Route cube.width × (thisDir(q)).Bank // (thisDir(q)).Guard (banks raw) a}) :
    (∀ t c, readCounts(q) raw v.val t c < 2^b.physical.word (k+1)) ∧
      (∀ c, (∑ t,readCounts(q) raw v.val t c) < 2^b.physical.word (k+1)) := by
  have checked := plan.signedTermCounts_word cube φ ord chart p fit W position sites edges ports table words good
    free count hp α ξ calibrated lit hd number gap scales b room batchEq stateEq teamsEq alpha fraction fields cover
    small bound time raw (chosen raw q v)
  have same := plan.signedDecodedTerm_sameCounts cube φ ord chart p fit W position sites edges ports table words good seeds
    free count hp α ξ calibrated lit hd number gap q raw v
  have wordEq := (b.sizes (Nat.succ_pos k)).2.2.2.1.trans (b.sizes (Nat.succ_pos k)).2.2.1.symm
  rw [same, ← wordEq]
  exact checked

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
