import OAI.Computability.BorderVNP.DiagonalEnrichedReaderBounds
import OAI.Computability.BorderVNP.DiagonalExternalFreeCanonical
import OAI.Computability.BorderVNP.PackedFrozenSeedInputs

/-! # Reader widths on the selected frozen seed and its actual packet volume -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Branch Crossing Cover Shortening Shortening.Adaptive Packing PhysicalEpochs Packing.DeckGrid
open Diagonal Diagonal.CellEntries Diagonal.ExternalSew GridHosts TeamContraction TeamScales EnrichedOuter
open ParseBatch ParseBatchVerifier Prewire VPVNP BorderVNP.Epoch BorderVNP.Epoch.Round
open ResidueIndex ResidueBox
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1800000
set_option maxRecDepth 6500
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {K E K₀ Gadget : Type} [Field K] [Field E] [Field K₀]
    {e : PaidIdentity K D m} {S : SiteSchedule e}
    {R r k pins link a regs w ec width s copies T d header Q : ℕ} (plan : SeedPlan S (k+1) r d T copies header Q)
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs w ec width ≤ k+1)
local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => tileCount (Fintype.card (Cube D)) d
local notation "G₀" => tapeTemplate p fit pins
variable {order : Fin (tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D (Fintype.card (Cube D)) d order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : PairedParameters k s ↪ ℕ) {ns ne np : ℕ}
    (siteID : (W.routedFine position).Site ↪ Fin ns) (edgeID : (W.routedFine position).Edge ↪ Fin ne)
    (portID : Fin r × Fin (publicWidth (tapeTemplate p fit pins)) ↪ Fin np)
    (table : (seedBundle (tapeTemplate p fit pins) (Fintype.card (Cube D)) d order position copies).Tables K)
    {σ : Type} [Fintype σ] (x : σ → Bool)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (count : (fan S)^T*copies=R+1)
    (y : e.Entry → E) (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget) (hg : 0 < inputBlockWidth r (k+1) (Fintype.card (Cube D)) d)
local notation "G₁" => SewnTape.wiring p fit free pins
local notation "M" => plan.compiled.machine
local notation "leaf" => plan.frozenLeaf G₀ order position W code siteID edgeID portID table x
local notation "bank" => canonicalBank (G := G₁) hg (gridRoom G₁ (Fintype.card_pos : 0 < tiles))

variable (cube : FixedCube K₀) {extra E₀ deg Q₀ A B j cut : ℕ} (scales : EpochScales S (cube.pred+1) extra)
    (b : JointSchedule.{0} scales (E₀+1) deg Q₀ A B j)
    (length : LengthBudget b cut (k+1)) (room : ReaderTallyInputsAt cube b (k+1))
    (batch : r = stretch b.ρ (k+1)) (candidate : s = stretch b.σ (k+1)) (groups : R = b.physical.teamsPred (k+1))
    (depthEq : d+1 = CoverScale.initialDepth (Cube D) r (k+1)) (time : T = epochs scales.τ (k+1))
    (small : 1+initialMass (D := D) (k+1) r d copies header ≤ TeamScales.width (k+1) (1/2:ℝ))

/-- The row-major finite enumeration used in the assigned packet expansion. -/
noncomputable local instance readerTeamFinite {j : ℕ} : Fintype (Port (fan S) (Fin copies × Unit) j) :=
  Replay.batchFinite (fan S) (Fin copies × Unit) j

variable (packet : ∀ q, PacketPlacement (Port (fan S) (Fin copies × Unit) T)
      cube.pred (BorderVNP.Cube.alphabet scales.α (k+1)) cube.b cube.h cube.copies (EnrichedTape.network p fit position free count plan.compiled.machine
        (plan.frozenLeaf (tapeTemplate p fit pins) order position W code siteID edgeID portID table x) rfl q))
    (cubePos : BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width → Gadget)
local notation "volume" => ((R+1)*exterior ((scales.τ:ℝ)/5) r (k+1) : ℕ)
local notation "alphabet" => BorderVNP.Cube.alphabet scales.α (k+1)
local notation "Paths" => EnrichedTape.assignedPath p fit W position free count M leaf rfl y hy pos hg packet cubePos bank
local notation "terms" => EnrichedTape.assigned p fit W position free count M leaf rfl y hy pos hg packet cubePos bank

include length room batch candidate groups depthEq time small in
/-- Every original assigned path satisfies the four numerical reader tests, using the
actual initial program's expanded bank fields and the common exterior reservation.
The packet equality is the block count of the selected finite cube labeling. -/
theorem frozen_assigned_reader_bounds
    (packed : ∀ q, (packet q).blocks = BorderVNP.Cube.Physical.blocksFor volume (cube.h*cube.b) (alphabet^(cube.pred+1)))
    (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) (raw : Fin pins → Bool) (u : Paths raw) (degree : ℕ) :
    let z := terms ord raw u
    Fits (radius (batchDegree (R+1) (pairedTableParameters (k+1) s) r k) degree) (parameterShift z.exponents) ∧
    (∀ l, z.exponents l < 2^b.physical.tally (k+1)) ∧
    (∀ g, (∑ team, z.counts team g) < 2^b.physical.multBits (k+1)) ∧
    (∀ g, (∑ team, z.counts team g) < 2^b.physical.tally (k+1)) := by
  have cover : (CoverScale.sites (Cube D) (d+1):ℝ) ≤ r*((k+1:ℕ):ℝ)^(9/10:ℝ) := by
    rw [depthEq,batch]
    exact length.cover.2.2.2.1
  have expanded := plan.frozenLeaf_bankCap G₀ order position W code siteID edgeID portID table x
  exact EnrichedTape.assigned_reader_bounds (D := D) (m := m) (k := k) (s := s) (r := r) (R := R)
    («axes» := Fintype.card (Cube D)) (gridDepth := d) (start := d+1) (copies := copies) (T := T)
    (regs := regs) (rw := w) (ec := ec) (width := width) (a := a) (order := order) (pins := pins) (link := link)
    (Gadget := Gadget) (E := E) (K := K) (cs := cube.width) p fit W position free count M leaf rfl y hy pos hg packet cubePos bank
    cube scales b room batch candidate groups rfl rfl _ cover small expanded time.le ord raw u volume le_rfl (packed u.1) degree

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
