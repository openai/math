import OAI.Computability.BorderVNP.DiagonalNativeSeedPathUse
import OAI.Computability.BorderVNP.DiagonalNativeSeedBirthSuffix
import OAI.Computability.BorderVNP.DiagonalPassingSeedSource

/-! # Chronological operand values of the compiled, exterior-sewn verifier

A passing original site's recorded operand is evaluated on its own cube-path
endpoint. Its authentic birth-bank interval supplies the ordered incidence lanes
at the original grouped grid, including the same row-major leaf and copy.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover Shortening Shortening.Adaptive BorderVNP.Epoch BorderVNP.Epoch.Round
open Packing Packing.Inherited Packing.DeckGrid Diagonal Diagonal.ExternalSew Diagonal.CellEntries
open TeamContraction GridHosts ParseBatch ParseBatchVerifier Prewire VPVNP Site.Lineage
open Diagonal.ExternalSew.RowTrace EnrichedOuter EnrichedOuter.Boundary BorderVNP.Cube BorderVNP.Cube.Physical
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option synthInstance.maxSize 4000
set_option maxHeartbeats 2600000
set_option maxRecDepth 7000

variable {D m : ℕ} [NeZero D] {K E Gadget : Type} [Field K] [Field E] {e : PaidIdentity K D m}
    {S : SiteSchedule e} {R r pins link k d a regs rw ec width s copies T w : ℕ}
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs rw ec width ≤ k+1)
local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => tileCount (Fintype.card (Cube D)) d
local notation "G₀" => tapeTemplate p fit pins
variable {order : Fin (tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D (Fintype.card (Cube D)) d order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : PairedParameters k s ↪ ℕ) {ns ne np : ℕ}
    (siteID : (W.routedFine position).Site ↪ Fin ns) (edgeID : (W.routedFine position).Edge ↪ Fin ne)
    (portID : (Fin r × Fin (publicWidth (tapeTemplate p fit pins))) ↪ Fin np)
    (table : (seedBundle (tapeTemplate p fit pins) (Fintype.card (Cube D)) d order position copies).Tables K)
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} {deep : S.floor+1+S.drop*T ≤ d+1}
    (C : Compiled (fun _ : Fin (tileCount (Fintype.card (Cube D)) d) => copies*inputBlockWidth r (k+1) (Fintype.card (Cube D)) d) deep budget cap w)
    (words : Pins S (d+1) (boundary S (d+1)) w 0 → Bool)
    (good : Good budget 0 (seedState S (tapeTemplate p fit pins) d order position copies table words))
    (seeds : ∀ h, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) h) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (number : e.Entry → ℕ)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (count : (fan S)^T*copies = R+1)
    (y : e.Entry → E) (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0) (pos : e.Entry → Gadget)
local notation3 (prettyPrint := false) "ok₀" => EnrichedOuter.Boundary.Good (S := S) (start := d+1) (P := Fin tiles)
  (bits := fun _ => copies*inputBlockWidth r (k+1) axes d) (shape := boundary S (d+1)) (w := w) budget
local notation "leaf₀" => seedMember (G := G₀) (order := order) (copies := copies) (budget := budget) S position table words good
local notation "group₀" => Equiv.toEmbedding (Equiv.refl (Fin (tileCount (Fintype.card (Cube D)) d)))
local notation "chan₀" => Shortening.PublicCapacity.Rows.edge (groupedGridRows G₀ axes d order position copies)
local notation "grid₀" => seedBundle G₀ axes d order position copies
local notation "prog₀" => wiredSeedStatePrograms S W position code siteID edgeID portID copies table words
local notation "key₀" => Equiv.toEmbedding (finCongr (seedPortCount (D := D) d))
local notation "dir₀" => C.privateSiteRows key₀ seeds
local notation "port₀" => privatePorts S key₀
local notation "G₁" => SewnTape.wiring p fit free pins
local notation "src₀" => EnrichedTape.base (Gadget := Gadget) p fit W position leaf₀ rfl
variable (hp : (fieldSewParams (SewnTape.wiring p fit free pins) (Fintype.card (Cube D)) d).Valid)
    (q : (packHistory (Subtype.mk (seedState S (tapeTemplate p fit pins) d order position copies table words) good) C.machine.epoch T).Index) (z : Fin ((fan S)^T) → Fin copies → W.Hidden position)
local notation3 (prettyPrint := false) "state₀" => ((packHistory (Pack := Admissible ok₀) (K := fan S) leaf₀ C.machine.epoch T).term q).val
local notation "last₀" => C.machine.terminalPrivatePrograms dir₀ number leaf₀ prog₀ q
local notation "net₀" => EnrichedTape.network p fit position free count C.machine leaf₀ rfl q
local notation "prog₁" => enrichedSewnPrograms G₁ axes d order position count C.machine leaf₀ rfl
  (Flat.portRows T (port₀ T)) hp q last₀
/-- Use the row-major nested team enumeration of the terminal tagged replay. -/
noncomputable local instance compiledSeedPowerTeams {j : ℕ} : Fintype (Port (fan S) (Fin copies × Unit) j) :=
  Replay.batchFinite (fan S) (Fin copies × Unit) j

local notation "terminal₀" => EnrichedOuterReplay.terminal C.machine y hy pos leaf₀ src₀ q z
local notation3 (prettyPrint := false) "edges₁" => FieldExport.mergedEdges (fieldSewParams G₁ axes d) hp (state₀).rows.edge
local notation "ports₁" => finProdFinEquiv.toEmbedding

variable {cn cd blocks cb ch ck cs : ℕ} {Cell : Type} [DecidableEq Cell] {cell : (EnrichedTape.network p fit position free count C.machine (seedMember (G := tapeTemplate p fit pins) (order := order) (copies := copies) (budget := budget) S position table words good) rfl q).Site → Cell}
    (slot : LiveBit (EnrichedTape.network p fit position free count C.machine (seedMember (G := tapeTemplate p fit pins) (order := order) (copies := copies) (budget := budget) S position table words good) rfl q) cell ↪ BorderVNP.Cube.Physical.Slot cn cd blocks (ch*cb))
    (path : Physical.Path (EnrichedTape.network p fit position free count C.machine (seedMember (G := tapeTemplate p fit pins) (order := order) (copies := copies) (budget := budget) S position table words good) rfl q) cell cn cd blocks cb ch ck cs)
    (bank : Ports (fun _ : FreeBlock R (tileCount (Fintype.card (Cube D)) d) => inputBlockWidth r (k+1) (Fintype.card (Cube D)) d))

open EnrichedTape DiagonalTallyCellReports Site.Programs
attribute [local instance] WiredWitness.reportDeckEq

variable {N : ℕ} (origin : Fin N ≃ Fin ((fan S)^T) × (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (boxSlot offset : Fin N → ℕ) (physical : Fin N → ℕ → Bool)
    {cellsN : ℕ} (owner : Fin N → Fin cellsN) (team : Fin cellsN → ℕ) (current : ℕ)
    {l : ReportLayout} (reports : List (ReportCell l)) (cells : Fin reports.length ≃ {c : Fin cellsN // team c = current})
local notation "start₀" => W.retainedReportStart position origin
local notation "bundle₀" => W.retainedBundle (copies := copies) position origin code siteID edgeID portID chan₀ group₀ boxSlot offset physical
variable (grouped : ∀ i : Fin reports.length, reports[i].bundles = (BundleDirectory.sourceRows owner (cells i).val.val).map
  (W.retainedBundle (copies := copies) position origin code siteID edgeID portID
    (groupedGridRows (tapeTemplate p fit pins) (Fintype.card (Cube D)) d order position copies).edge
    (Equiv.refl (Fin (tileCount (Fintype.card (Cube D)) d))).toEmbedding boxSlot offset physical))
local notation3 (prettyPrint := false) "source₀" => W.reportUseEquiv position origin code siteID edgeID portID start₀ bundle₀ (fun _ => rfl)
  owner team current reports cells grouped (fun _ => rfl)
local notation "tag₀" => tags p fit W position free count C.machine leaf₀ rfl y hy pos hp.block q z

private theorem cast_power_owner {D exp : ℕ} {P Team Param Gadget : Type}
    [Fintype Team] [Fintype Param] {pb : P → ℕ} {N M : Network D P pb} (he : N=M)
    (t : Tracked Team Param Gadget exp N) (w0 : PowerSlot Team Param exp) :
    (t.castLayout he).words.site w0 = Eq.mp (congrArg Network.Site he) (t.words.site w0) := by
  subst M
  rfl

/-- The private receipt at a particular live vertex, in the native
directory's original sparse edge and grouped-port numbering. -/
def Compiled.sourceRecordAt (l : ReportLayout) (j : Fin N) (v : (net₀).Site) : Prop :=
  let pr := prog₁ v
  let x := atPathHost net₀ slot path bank v
  let seen := inputWords net₀ edges₁ ports₁ v (fun u => x.edges u.val) (fun u => x.ports u.val) ∘ Fin.cast pr.size
  ∃ work : Fin pr.birth.work → Bool, Nonempty (W.CheckedBirthData position code siteID edgeID portID chan₀ group₀
    (origin j).2 (physical j) (boxSlot j) (offset j) (z (origin j).1) l (bits work (pr.retention.readInput seen)))

local notation3 (prettyPrint := false) "record₀" => C.sourceRecordAt p fit W position code siteID edgeID portID table
  words good seeds number free count hp q z slot path bank origin boxSlot offset physical

/-- The chronological source carries real guard and report observations on the
original checker work followed by the input restored at its actual compiled host. -/
def Compiled.PassingSeedAt (l : ReportLayout) (j : Fin N) (h : Fin (bundle₀ j).positions.length) (i : Fin copies) : Prop :=
  let mark := W.sidecarEquiv position code siteID edgeID portID (origin j).2 (start₀ j) h
  let w0 := reportPathSlot (fan S) T (origin j).1 i mark.val
  let v := (terminal₀).words.site w0
  record₀ l j v

/-- A single observed original vertex suffices for every one of its marked
copies. The selected history preserves the mark's original owner. -/
theorem Compiled.passingSeedAt_of_source (j : Fin N) (atHost : record₀ l j ((enrichedOuterHosts C.machine leaf₀ q).site ⟨(origin j).1,(origin j).2⟩))
    (h : Fin (bundle₀ j).positions.length) (i : Fin copies) :
    C.PassingSeedAt p fit W position code siteID edgeID portID table words good seeds number free count
      y hy pos hp q z slot path bank origin boxSlot offset physical l j h i := by
  let mark := W.sidecarEquiv position code siteID edgeID portID (origin j).2 (start₀ j) h
  let w0 := reportPathSlot (fan S) T (origin j).1 i mark.val
  let idx := portEquiv (fan S) (Fin copies × Unit) T
  have hi : idx w0.1 = ((origin j).1,i,()) := idx.apply_symm_apply _
  let seed : Tracked Unit (PairedParameters k s) Gadget (Nat.clog 2 (r*(2*k+1)+1)) (W.seedGrid position) :=
    ⟨W.seedTags position (z (origin j).1 i),W.seedWords position (z (origin j).1 i)⟩
  have hc : (src₀ (z (idx w0.1).1)).words.site ((idx w0.1).2,w0.2) = (origin j).2 := by
    rw [hi]
    exact (cast_power_owner (W.seedGrid_eq position) seed ((),mark.val)).trans mark.property
  have dest := EnrichedOuterReplay.terminal_power_site y hy pos C.machine leaf₀ src₀ q z w0
  change (terminal₀).words.site w0 = (enrichedOuterHosts C.machine leaf₀ q).site
    ⟨(idx w0.1).1,(src₀ (z (idx w0.1).1)).words.site ((idx w0.1).2,w0.2)⟩ at dest
  rw [hc,hi] at dest
  exact (congrArg (record₀ l j) dest).mpr atHost

private theorem read_same_address {actual expected : ℕ → Bool} {a b : ℕ} (same : a=b) (j : ℕ)
    (read : actual (b+j)=expected (b+j)) : actual (a+j)=expected (a+j) := same.symm ▸ read

/-- The observed physical birth record at this current copy supplies all the
original incidence lanes on precisely the selected cube endpoint. -/
theorem Compiled.wiredSeed_sourceObserved (j : Fin N) (h : Fin (bundle₀ j).positions.length) (i : Fin copies)
    (passing : C.PassingSeedAt p fit W position code siteID edgeID portID table words good seeds number free count
      y hy pos hp q z slot path bank origin boxSlot offset physical l j h i) :
    ∃ source : W.PassingSeedSource position code siteID edgeID portID chan₀ group₀ (origin j).2
      (physical j) (boxSlot j) (offset j) (z (origin j).1) l,
      SourceBirthSuffix p fit W position free count C.machine leaf₀ rfl y hy pos hp.block q z slot path bank
        origin code siteID edgeID portID chan₀ group₀ boxSlot offset physical j h i source := by
  let tile := (origin j).2
  let mark := W.sidecarEquiv position code siteID edgeID portID tile (start₀ j) h
  let w0 := reportPathSlot (fan S) T (origin j).1 i mark.val
  let idx := portEquiv (fan S) (Fin copies × Unit) T
  have hi : idx w0.1 = ((origin j).1,i,()) := idx.apply_symm_apply _
  let seed : Tracked Unit (PairedParameters k s) Gadget (Nat.clog 2 (r*(2*k+1)+1)) (W.seedGrid position) :=
    ⟨W.seedTags position (z (origin j).1 i),W.seedWords position (z (origin j).1 i)⟩
  have hc : (src₀ (z (idx w0.1).1)).words.site ((idx w0.1).2,w0.2) = tile := by
    rw [hi]
    exact (cast_power_owner (W.seedGrid_eq position) seed ((),mark.val)).trans mark.property
  obtain ⟨work,⟨data⟩⟩ := passing
  refine ⟨data.passingSource,?_⟩
  have shape := C.wiredSeed_path_birthShape p fit W position code siteID edgeID portID table words good seeds number free
    count y hy pos hp q z w0
  have hw := shape.1.trans (congrArg (fun c => copies*(W.seedSlab position code siteID edgeID portID c).stride) hc)
  have hi' := shape.2.trans (congrArg (incoming grid₀) hc)
  have actual := C.wiredSeed_path_birthSuffix p fit W position code siteID edgeID portID table words good seeds number free
    count y hy pos hp q z slot path bank w0 work data.passingSource.birthBank
    (fun f => read_same_address hw f.val (data.passingSource_input (Fin.cast hi' f)))
  change ∀ f : Fin (incoming grid₀ ((src₀ (z (idx w0.1).1)).words.site ((idx w0.1).2,w0.2))), _ at actual
  rw [hc] at actual
  exact actual

include grouped in
/-- On genuine passing original sites, the emitted numerical operand uses
the exact parameter, place, and power bit of the terminal compiled cube path.
The real birth checks and cell report windows supply all input-lane equalities. -/
theorem Compiled.wiredSeed_occurrencePair (passing : ∀ j h i, C.PassingSeedAt p fit W position code siteID edgeID portID
    table words good seeds number free count y hy pos hp q z slot path bank origin boxSlot offset physical l j h i)
    (u : UseOccurrence reports) :
    let a := source₀ u
    let w0 := reportPathSlot (fan S) T a.2.val.1 a.1 a.2.val.2
    occurrencePair reports u = (code a.2.val.2.1, if (tag₀).words.localUse (pathEdges slot path)
      (fun _ f => bank f.val) w0.1 w0.2.1 w0.2.2 then 2^a.2.val.2.2.val else 0) := by
  refine occurrencePair_pathUse p fit W position free count C.machine leaf₀ rfl y hy pos hp.block q z slot path bank origin code
    siteID edgeID portID chan₀ group₀ boxSlot offset physical owner team current reports cells grouped ?_ u
  intro j h i
  exact C.wiredSeed_sourceObserved p fit W position code siteID edgeID portID table words good seeds number
    free count y hy pos hp q z slot path bank origin boxSlot offset physical j h i (passing j h i)

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
