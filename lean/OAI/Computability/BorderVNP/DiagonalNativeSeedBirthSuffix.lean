import OAI.Computability.BorderVNP.DiagonalBottomSeedPhysicalBits
import OAI.Computability.BorderVNP.DiagonalSewnBirthInputs
import OAI.Computability.BorderVNP.DiagonalOuterBirthInputs
import OAI.Computability.BorderVNP.DiagonalSewnSeedPowerRead
import OAI.Computability.BorderVNP.PackedBankWiredSeedState
import OAI.Computability.BorderVNP.PackedSelectedPrivateFieldRows
import OAI.Computability.BorderVNP.PackedFrozenNativePort

/-! # The immutable seed-checker suffix on the actual sewn computation path

The same selected machine supplies every intermediate sparse row. At a chosen
tracked power occurrence, the input part of its immutable birth bank contains
precisely the original grouped grid words reconstructed from that path.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Site.Lineage

open Crossing Diagonal.CellEntries

/-- The stored birth input sees the occupied numerical port ordinals of
the native cover even when its capacity is stated as the original tile count. -/
theorem birthInput_portRows {D ne np nq : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (edge : N.Edge ↪ Fin ne) (old : P ↪ Fin np)
    (next : P ↪ Fin nq) (cap : nq=np) (same : ∀ i,(next i).val=(old i).val)
    (v : N.Site) (pr : Lineage (Inherited.incoming N v)) (a : PowerInput N) :
    birthInput N edge next v pr a=birthInput N edge old v pr a := by
  subst nq
  obtain rfl : next=old := DFunLike.ext _ _ fun z => Fin.ext (same z)
  rfl

end Packing.Inherited.Site.Lineage

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Crossing Cover Shortening Shortening.Adaptive BorderVNP.Epoch BorderVNP.Epoch.Round
open Packing Packing.Inherited Packing.DeckGrid Diagonal Diagonal.ExternalSew Diagonal.CellEntries
open TeamContraction GridHosts ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar Site.Lineage
open Diagonal.ExternalSew.RowTrace
open scoped Classical
attribute [local instance] portFintype
set_option maxHeartbeats 2000000
set_option maxRecDepth 5500

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
    {R r t pins link inner n g d copies w : ℕ} {Edge : Type} [Fintype Edge] {G : Wiring R r t pins link inner n Edge}
    {len : Fin n} {key : Fin g}
local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => tileCount (Fintype.card (Cube D)) d
variable {order : Fin (tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness G len D (Fintype.card (Cube D)) d order key)
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (siteID : (W.routedFine position).Site ↪ Fin ns) (edgeID : (W.routedFine position).Edge ↪ Fin ne)
    (portID : (Fin r × Fin (publicWidth G)) ↪ Fin np)
    (table : (seedBundle G (Fintype.card (Cube D)) d order position copies).Tables K)
    (words : Pins S (d+1) (SelectedSchedule.boundary S (d+1)) w 0 → Bool)
local notation "state₀" => seedState S G d order position copies table words
local notation "grid₀" => seedBundle G (Fintype.card (Cube D)) d order position copies
local notation "group₀" => Equiv.toEmbedding (Equiv.refl (Fin (tileCount (Fintype.card (Cube D)) d)))
local notation "chan₀" => Shortening.PublicCapacity.Rows.edge (groupedGridRows G (Fintype.card (Cube D)) d order position copies)
local notation "prog₀" => wiredSeedStatePrograms S W position code siteID edgeID portID copies table words

/-- Put the verified initialized grid state into the selected machine's state
type at level zero. -/
noncomputable abbrev seedMember {budget : ℕ → ℕ} (good : Good budget 0 (state₀)) :
    Admissible (Good (S := S) (start := d+1) (P := Fin tiles) (bits := fun _ => copies*inputBlockWidth r n axes d)
      (shape := SelectedSchedule.boundary S (d+1)) (w := w) budget) 0 :=
  ⟨state₀,good⟩

/-- At the selected seed the native birth input is the physical grouped-grid
incidence vector, including the true sparse cable numbering. -/
theorem wiredSeedState_birthInput (c : (grid₀).Site) (x : PowerInput grid₀) (j : Fin (incoming grid₀ c)) :
    birthInput (state₀).pack.layout (state₀).rows.edge group₀ c (prog₀ c) x j.val =
      inputWords grid₀ chan₀ group₀ c (fun u => x.edges u.val) (fun u => x.ports u.val) j := by
  let outer := portFintype (k := fan S) (P := Fin tiles) (b := 0)
  let old := wiredSeedPrograms W position code siteID edgeID portID copies
  have changed := birthInput_instance (Fin.fintype tiles) outer grid₀ chan₀ group₀ old c x
  have sparse := birthInput_numbered (state₀).pack.layout chan₀ group₀ c (prog₀ c)
    (state₀).rows.edge (congrArg Shortening.PublicCapacity.Shape.edges (gridShape_zero S d))
    (seedState_rows S G d order position copies table words).2 x
  exact (congrFun (sparse.trans changed) j.val).trans (dite_eq_left j.isLt)

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

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
noncomputable local instance seedPowerTeams {j : ℕ} : Fintype (Port (fan S) (Fin copies × Unit) j) :=
  Replay.batchFinite (fan S) (Fin copies × Unit) j

local notation "terminal₀" => EnrichedOuterReplay.terminal C.machine y hy pos leaf₀ src₀ q z
local notation3 (prettyPrint := false) "edges₁" => FieldExport.mergedEdges (fieldSewParams G₁ axes d) hp (state₀).rows.edge
local notation "ports₁" => finProdFinEquiv.toEmbedding

variable {cn cd blocks cb ch ck cs : ℕ} {Cell : Type} [DecidableEq Cell] {cell : (EnrichedTape.network p fit position free count C.machine (seedMember (G := tapeTemplate p fit pins) (order := order) (copies := copies) (budget := budget) S position table words good) rfl q).Site → Cell}
    (slot : LiveBit (EnrichedTape.network p fit position free count C.machine (seedMember (G := tapeTemplate p fit pins) (order := order) (copies := copies) (budget := budget) S position table words good) rfl q) cell ↪ BorderVNP.Cube.Physical.Slot cn cd blocks (ch*cb))
    (path : Physical.Path (EnrichedTape.network p fit position free count C.machine (seedMember (G := tapeTemplate p fit pins) (order := order) (copies := copies) (budget := budget) S position table words good) rfl q) cell cn cd blocks cb ch ck cs)
    (bank : Ports (fun _ : FreeBlock R (tileCount (Fintype.card (Cube D)) d) => inputBlockWidth r (k+1) (Fintype.card (Cube D)) d))
    (w0 : PowerSlot (Port (fan S) (Fin copies × Unit) T) (PairedParameters k s) (Nat.clog 2 (r*(2*k+1)+1)))

/-- The immutable work length and input extent at the attained tracked owner
are the full repeated work and incidence widths of its original grid tile. -/
theorem Compiled.wiredSeed_path_birthShape :
    let idx := portEquiv (fan S) (Fin copies × Unit) T w0.1
    let c := (src₀ (z idx.1)).words.site (idx.2,w0.2)
    let pr := prog₁ ((terminal₀).words.site w0)
    pr.birth.work = copies*(W.seedSlab position code siteID edgeID portID c).stride ∧
      pr.birth.incoming = incoming grid₀ c := by
  intro idx c pr
  have host := EnrichedOuterReplay.terminal_power_site y hy pos C.machine leaf₀ src₀ q z w0
  have saved : pr.birth = (prog₀ c).birth := (congrArg (fun u => (last₀ u).birth) host).trans
    (C.machine.terminalPrivatePrograms_birth dir₀ number leaf₀ prog₀ q idx.1 c)
  have hw : pr.birth.work = copies*(W.seedSlab position code siteID edgeID portID c).stride :=
    congrArg Site.work saved
  have hi : pr.birth.incoming = incoming grid₀ c := congrArg Site.incoming saved
  exact ⟨hw,hi⟩

/-- Every suffix lane of the authentic retained seed checker reads the original
grouped input of this selected power occurrence on the very same sewn path. -/
theorem Compiled.wiredSeed_path_birthSuffix :
    let idx := portEquiv (fan S) (Fin copies × Unit) T w0.1
    let c := (src₀ (z idx.1)).words.site (idx.2,w0.2)
    let v := (terminal₀).words.site w0
    let pr := prog₁ v
    let x := atPathHost net₀ slot path bank v
    let current := inputWords net₀ edges₁ ports₁ v (fun u => x.edges u.val) (fun u => x.ports u.val) ∘ Fin.cast pr.size
    let original := EnrichedTape.pathBundleInput p fit W position free count C.machine leaf₀ rfl y hy pos hp.block q z slot path bank w0
    ∀ (work : Fin pr.birth.work → Bool) (birthBank : ℕ → Bool),
      (∀ u : Fin pr.birth.incoming, birthBank (pr.birth.work+u.val) =
        bits work (pr.retention.readInput current) (pr.birth.work+u.val)) →
      ∀ j : Fin (incoming grid₀ c), birthBank (copies*(W.seedSlab position code siteID edgeID portID c).stride+j.val) =
      inputWords grid₀ chan₀ group₀ c (fun u => original.edges u.val) (fun u => original.ports u.val) j := by
  intro idx c v pr x current original work birthBank authentic j
  let terminalInput := enrichedPathPowerInput G₁ axes d order position count C.machine leaf₀ rfl hp.block q slot path bank v
  have first := enrichedSewn_path_birthInput G₁ axes d order position count C.machine leaf₀ rfl dir₀ number prog₀
    (port₀ T) hp q slot path bank v
  have later := C.machine.historyPrivatePrograms_birthInput y hy pos dir₀ port₀ (C.privateFieldRows key₀ seeds)
    number leaf₀ prog₀ src₀ T le_rfl z q w0 terminalInput
  have old := wiredSeedState_birthInput S W position code siteID edgeID portID table words c original j
  have numeric := birthInput_portRows (leaf₀).val.pack.layout (leaf₀).val.rows.edge group₀ key₀
    (seedPortCount (D := D) d).symm (fun _ => rfl) c (prog₀ c) original
  obtain ⟨hw,hi⟩ := C.wiredSeed_path_birthShape p fit W position code siteID edgeID portID table words good
    seeds number free count y hy pos hp q z w0
  have read := birthBank_input net₀ edges₁ ports₁ v pr x work (Fin.cast hi.symm j)
  rw [←hw]
  exact (authentic (Fin.cast hi.symm j)).trans (read.trans ((congrFun (first.trans (later.trans numeric)) j.val).trans old))

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
