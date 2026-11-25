import OAI.Computability.BorderVNP.DiagonalEnrichedNativeRows
import OAI.Computability.BorderVNP.DiagonalEnrichedReaderBounds

/-! # Native tally and multiplicity widths for the actual enriched arithmetic term -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.EnrichedTape

open Crossing Shortening Adaptive Packing Packing.DeckGrid Cover TeamContraction ExternalSew GridHosts
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PublicCapacity VPVNP BorderVNP.Cube MvPolynomial
open scoped BigOperators Classical BorderVNP.Epoch.Cube

universe u v

variable {D m start T : ℕ} [NeZero D] {K E Gadget : Type} [Field K] [Field E] {e : PaidIdentity K D m}
    {S : Normalized.SiteSchedule e} {shape : ℕ → Shape} {Word : ℕ → Type} [∀ t, Fintype (Word t)]
    {V : ℕ → ℕ → Type} [∀ t j, Fintype (V t j)] {w : ℕ → ℕ → ℕ}
    {R r pins link k axes gridDepth a regs rw ec width s copies : ℕ}
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs rw ec width ≤ k+1)
    {order : Fin (tileCount axes gridDepth) ≃ (Fin axes → Deck (gridDepth+2))}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D axes gridDepth order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin axes → Deck (gridDepth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (free : Fin (R+1) → Fin r → Fin a → Bool)
    {deep : S.floor+1+S.drop*T ≤ start} (count : (EnrichedOuter.fan S)^T*copies = R+1)
    {good : ∀ j, EnrichedOuter.State S start (Fin (tileCount axes gridDepth))
      (fun _ => copies*inputBlockWidth r (k+1) axes gridDepth) shape Word j → Prop}
    (M : EnrichedOuter.Machine.{0,u} deep good V w) (bottom : EnrichedOuter.Admissible good 0)
    (installed : bottom.val.pack.layout = (wiredGrid (tapeTemplate p fit pins) axes gridDepth order position).groupedRepeat
      (fun _ : Fin (tileCount axes gridDepth) => inputBlockWidth r (k+1) axes gridDepth) order copies)
    (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget) (hg : 0 < inputBlockWidth r (k+1) axes gridDepth)

set_option synthInstance.maxSize 4000
set_option maxHeartbeats 850000

/-- Enumerate the true original batch numbers in the nested public history. -/
noncomputable local instance nativeBoundsBatchFinite {j : ℕ} : Fintype (Port (EnrichedOuter.fan S) (Fin copies × Unit) j) :=
  Replay.batchFinite (EnrichedOuter.fan S) (Fin copies × Unit) j

variable {cn cd cb ch cK cs : ℕ} {Pin : Type}
    (packet : ∀ q, PacketPlacement (Port (EnrichedOuter.fan S) (Fin copies × Unit) T)
      cn cd cb ch cK (network p fit position free count M bottom installed q))
    (cubePos : TableEntry cn cb ch cK cs → Gadget)
    (bank : Pin → Ports (fun _ : FreeBlock R (tileCount axes gridDepth) =>
      inputBlockWidth r (k+1) axes gridDepth))

open TeamScales Branch ResidueBox ResidueIndex BorderVNP.Cube.Physical Epoch.Round
attribute [local instance] portFintype


/-- The shared tally field can represent all current-owner rows and their
totals for this genuine assigned history. The dense multiplicity field at
each physical scalar ID stores the very same sum with its smaller width. -/
theorem native_reader_bounds {F₀ : Type*} [Field F₀] (cube : FixedCube F₀)
    {extra E₀ d Q A B j : ℕ} (scales : EpochScales S (cube.pred+1) extra)
    (b : JointSchedule.{v} scales (E₀+1) d Q A B j)
    (room : ReaderTallyInputsAt cube b (k+1))
    (batchEq : r = stretch b.ρ (k+1)) (candidateEq : s = stretch b.σ (k+1))
    (teamsEq : R = b.physical.teamsPred (k+1)) (cubeEq : cn = cube.pred)
    (alphabetEq : cd = BorderVNP.Cube.alphabet scales.α (k+1))
    (fields : Epoch.Round.RecordData bottom.val.pack.layout) {B₀ : ℕ}
    (cover : (CoverScale.sites (Epoch.Cube D) start : ℝ) ≤ r*((k+1:ℕ):ℝ)^(9/10:ℝ))
    (small : 1+B₀ ≤ TeamScales.width (k+1) (1/2:ℝ)) (seedCap : PhysicalEpochs.SiteCap bottom.val.route fields true B₀)
    (time : T ≤ epochs scales.τ (k+1))
    (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) (i : Pin)
    (u : assignedPath p fit W position free count M bottom installed y hy pos hg packet cubePos bank i)
    (occupied : ℝ) (occupied_le : occupied ≤ ((R+1)*exterior ((scales.τ:ℝ)/5) r (k+1):ℕ))
    (packed : (packet u.1).blocks = blocksFor occupied (cube.h*cube.b) (cd^(cn+1)))
    {U : ℕ} (scalar : Gadget ≃ Fin U) (degree : ℕ) :
    let t := assigned p fit W position free count M bottom installed y hy pos hg packet cubePos bank ord i u
    let rows := nativeRow p fit W position free count M bottom installed y hy pos hg packet cubePos bank ord scalar i u
    Fits (radius (batchDegree (R+1) (pairedTableParameters (k+1) s) r k) degree) (parameterShift t.exponents) ∧
      (∀ team j, rows team j < 2^b.physical.tally (k+1)) ∧
      (∀ j, (∑ team, rows team j) < 2^b.physical.tally (k+1)) ∧
      (∀ g : Fin U, (∑ team, rows team (Fin.natAdd (pairedTableParameters (k+1) s) g)) <
        2^b.physical.multBits (k+1)) := by
  intro t rows
  obtain ⟨fit₀,param,gmult,gcount⟩ := assigned_reader_bounds p fit W position free count M bottom installed y hy pos hg
    packet cubePos bank cube scales b room batchEq candidateEq teamsEq cubeEq alphabetEq fields cover small seedCap
    time ord i u occupied occupied_le packed degree
  let t' := t.numberScalars scalar
  have eq (j : Fin (pairedTableParameters (k+1) s + U)) :
      (∑ team, rows team j) = ∑ team, DiagonalTallyRAM.tallyRow t' team j :=
    sum_nativeRow p fit W position free count M bottom installed y hy pos hg packet cubePos bank ord scalar i u j
  have sumFits (j : Fin (pairedTableParameters (k+1) s + U)) :
      (∑ team, rows team j) < 2^b.physical.tally (k+1) := by
    refine Fin.addCases (fun p => ?_) (fun g => ?_) j
    · exact ((eq (Fin.castAdd U p)).trans (DiagonalTallyRAM.tallyRow_parameter t' p)).le.trans_lt (param p)
    · exact ((eq (Fin.natAdd (pairedTableParameters (k+1) s) g)).trans (DiagonalTallyRAM.tallyRow_gadget t' g)).le.trans_lt
        (gcount (scalar.symm g))
  refine ⟨fit₀,fun team j => ?_,sumFits,fun g => ?_⟩
  · exact (Finset.single_le_sum (fun j _ => Nat.zero_le (rows j _)) (Finset.mem_univ team)).trans_lt (sumFits j)
  · exact ((eq (Fin.natAdd (pairedTableParameters (k+1) s) g)).trans (DiagonalTallyRAM.tallyRow_gadget t' g)).le.trans_lt
      (gmult (scalar.symm g))

end Diagonal.CellEntries.EnrichedTape

end BorderVNP
end Computability
end OAI
