import OAI.Computability.BorderVNP.DiagonalSignedSewnMarkedWords
import OAI.Computability.BorderVNP.DiagonalSignedSewnProgramLoad
import OAI.Computability.BorderVNP.PackedBankTerminalSiteCaps

/-! # Compiled signed cell loads and marked operand bounds on one concrete seed -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.DeckGrid Packing.PhysicalEpochs Diagonal Diagonal.ExternalSew
open TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open EnrichedOuter Boundary GridHosts
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2200000
set_option maxRecDepth 5500
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {R r t pins link inner n g d copies T w : ℕ} {Edge : Type} [Fintype Edge] {G : Wiring R r t pins link inner n Edge}
    {len : Fin n} {key : Fin g}
    {order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness G len D (Fintype.card (Cube D)) d order key)
    (pos : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine pos).Site ↪ Fin ns) (edges : (W.routedFine pos).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth G) ↪ Fin np)
    (table : (seedBundle G (Fintype.card (Cube D)) d order pos copies).Tables K)
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} {deep : S.floor+1+S.drop*T ≤ d+1}
    (C : Compiled (fun _ : Fin (tileCount (Fintype.card (Cube D)) d) =>
      copies*inputBlockWidth r n (Fintype.card (Cube D)) d) deep budget cap w)
    (words : Pins S (d+1) (boundary S (d+1)) w 0 → Bool)
    (good : Good budget 0 (seedState S G d order pos copies table words))
    (seeds : ∀ h, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) h) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    {nc : ℕ} (ids : Fin (tileCount (Fintype.card (Cube D)) d) ↪ Fin nc)
    (number : e.Entry → ℕ)
    (real : Wiring R r t pins link inner n Edge)
    (count : (fan S)^T*copies = R+1)
    (hp : (fieldSewParams real (Fintype.card (Cube D)) d).Valid)
local notation "axes" => Fintype.card (Cube D)
local notation "adm" => Good (S := S) (start := d+1) (P := Fin (tileCount axes d))
  (bits := fun _ => copies*inputBlockWidth r n axes d) (shape := boundary S (d+1)) (w := w) budget
local notation "leaf" => (Subtype.mk (seedState S G d order pos copies table words) good : Admissible adm 0)
local notation "src" => wiredSeedStatePrograms S W pos tag sites edges ports copies table words
local notation "dir" => C.privateSiteRows ids seeds
local notation "lastPorts" => Flat.portRows T (privatePorts S ids T)

variable (placed : (seedState S G d order pos copies table words).pack.layout =
      (wiredGrid real (Fintype.card (Cube D)) d order pos).groupedRepeat
        (fun _ : Fin (tileCount (Fintype.card (Cube D)) d) => inputBlockWidth r n (Fintype.card (Cube D)) d) order copies)

open InheritedBank

/-- Use the original verifier's own two site accounts. The same installed
program supplies both load bounds, and one global numeric limit bounds every
marked operand without charging an unoccupied private interval. -/
theorem signedSewn_sourceNumbers (hm : 0 < m) (dB : ℕ) (q : (packHistory
    (Subtype.mk (seedState S G d order pos copies table words) good) C.machine.epoch T).Index)
    {Cells : Type} (cellID : (Cube D → Deck (depth S (d+1) T+1)) ≃ Cells)
    (short : inputBlockWidth r n axes d ≤ link) :
    let degree := Fintype.card (Direction axes)
    let cap₀ := seedBoxCapacity n r axes d degree
    let mass := baseMass degree cap₀ (seedChannelWidth n r axes d) copies dB
    let L := S.publicProgramFactor^T*mass
    let coeff := (birthWordCoefficient e+8)*(BankCharges.bound e+1)*(S.populationFactor+2)
    let Z := max (max 2 (max copies cap₀)) (max (coeff*(L+1)) (max 1 (15*L)))
    let state := ((packHistory leaf C.machine.epoch T).term q).val
    let cell := fun v => cellID (reduceMove (depth S (d+1) T) (state.route.origin v))
    let N := enrichedSewnLayout real axes d order pos count C.machine leaf placed q
    let pr := enrichedSewnPrograms real axes d order pos count C.machine leaf placed lastPorts hp q
      (C.machine.terminalPrivatePrograms dir number leaf src q)
    (∀ c ex, localRecords N ex pr.fullFields.prior pr.fullFields.payload (fun v => cell v=c) ≤ 1042*L) ∧
      (∀ v, (pr v).program.ScalarBound Z) := by
  intro degree cap₀ mass L coeff Z state cell N pr
  have full := (wiredSeedStatePrograms_bounds S W pos tag sites edges ports copies table words dB).2.1
  have bank : SiteCap (leaf).val.route (src).bankFields true mass := by
    intro tile
    have cap' := bankRecords_le (leaf).val.pack.layout src (src).fullFields true
      (fun v => ⟨(src v).program.publicNodes_le_staticNodes,le_rfl⟩)
      (fun v => reduceMove (depth S (d+1) 0) ((leaf).val.route.origin v) = tile)
    exact (Nat.add_le_add_left cap' 1).trans (full tile)
  constructor
  · exact enrichedSewn_programTile real axes d order pos count C.machine leaf placed lastPorts hp q cellID
      dir number src mass full short
  · have sizes := enrichedSewn_address_capacity real axes d order pos count C.machine leaf placed lastPorts hp q
      dir number src cellID mass bank
    intro v tagWord inSet
    have num := signedSewn_markedWords W pos tag sites edges ports table C words good seeds ids number real count hp placed
      hm mass bank q v tagWord inSet
    have size : (pr v).program.size ≤ 15*L := sizes.2 v
    change tagWord.2 ≤ max (max (max 2 (max copies cap₀)) (coeff*(L+1))) (max 1 (pr v).program.size) at num
    change tagWord.2 ≤ max (max 2 (max copies cap₀)) (max (coeff*(L+1)) (max 1 (15*L)))
    omega

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
