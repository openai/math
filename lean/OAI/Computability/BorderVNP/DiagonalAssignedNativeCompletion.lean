import OAI.Computability.BorderVNP.DiagonalEnrichedNativeRowBounds
import OAI.Computability.BorderVNP.DiagonalPositiveCoreReadback
import OAI.Computability.BorderVNP.DiagonalCanonicalFinishImage
import OAI.Computability.BorderVNP.DiagonalCompletedReader

/-! # Actual assigned rows in the signed native finish -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.EnrichedTape

open Crossing Shortening Adaptive Packing Packing.DeckGrid Cover TeamContraction ExternalSew GridHosts
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PublicCapacity VPVNP BorderVNP.Cube MvPolynomial
open scoped BigOperators Classical BorderVNP.Epoch.Cube

universe u

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
set_option maxHeartbeats 1600000
set_option maxRecDepth 12000

/-- Enumerate the true original batch numbers in the nested public history. -/
noncomputable local instance completionBatchFinite {j : ℕ} : Fintype (Port (EnrichedOuter.fan S) (Fin copies × Unit) j) :=
  Replay.batchFinite (EnrichedOuter.fan S) (Fin copies × Unit) j

variable {cn cd cb ch cK cs : ℕ} {Pin : Type}
    (packet : ∀ q, PacketPlacement (Port (EnrichedOuter.fan S) (Fin copies × Unit) T)
      cn cd cb ch cK (network p fit position free count M bottom installed q))
    (cubePos : TableEntry cn cb ch cK cs → Gadget)
    (bank : Pin → Ports (fun _ : FreeBlock R (tileCount axes gridDepth) =>
      inputBlockWidth r (k+1) axes gridDepth))

open TeamScales Branch ResidueBox ResidueIndex BorderVNP.Cube.Physical Epoch.Round
attribute [local instance] portFintype


open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator CompactMachine CellMacro.Generator
open TeamContraction.JointHeader DiagonalTallyCellReports

variable {F₀ : Type*} [Field F₀] (cube : FixedCube F₀)
    {extra E₀ d Q A B j : ℕ} (scales : EpochScales S (cube.pred+1) extra)
    (b : JointSchedule.{u} scales (E₀+1) d Q A B j)
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
    {U : ℕ} (scalar : Gadget ≃ Fin U)
    {reserve groups capacity : ℕ} {id : TableEntry cn cb ch cK cs → ℕ} {gen : Fragment IO}
    (X : UncheckedCandidate id gen (k+1) (b.physical.word (k+1)) (R+1) (parameterCount (2*(k+1)) k s+U)
      (b.physical.tally (k+1)))
    (header : PositiveFields reserve cn groups capacity (R+1) (parameterCount (2*(k+1)) k s+U)
      (b.physical.tally (k+1)))

local notation3 (prettyPrint := false) "sourceRows" => nativeRow p fit W position free count M bottom installed
  y hy pos hg packet cubePos bank ord scalar i u

variable
    (passing : ∀ t c, c ∈ X.assigned t → c.Passing (b.physical.word (k+1)) (k+1))
    (finish : ∀ raw t, let reports := canonicalReports X.assigned passing
      let S₀ := X.team reports raw t
      let a₀ := (X.candidate reports raw).1 t
      let mac := install gen (k+1) S₀.routines
      PositiveFields.FinishInput t (nativeRow p fit W position free count M bottom installed y hy pos hg packet cubePos bank ord scalar i u) (b.physical.tally (k+1)) S₀.pub mac
        (cellBank S₀.pub mac a₀.2.val.2.1 a₀.2.val.2.2) a₀.2.val.2.2 (header.withSubtotals raw).tallyWords)

include room batchEq candidateEq teamsEq cubeEq alphabetEq fields cover small seedCap time occupied_le packed passing finish

/-- Complete the physical report and subtotal tests on an actual term of (11.2).
The row at each team counts the occurrences it received on this term. Both the
row and its all-team sum fit the machine word on the selected schedule. -/
noncomputable def nativeCompletion :
    X.Completion header := by
  have bounds := native_reader_bounds p fit W position free count M bottom installed y hy pos hg packet cubePos bank cube
    scales b room batchEq candidateEq teamsEq cubeEq alphabetEq fields cover small seedCap time ord i u occupied occupied_le packed scalar 0
  have same : b.physical.tally (k+1) = b.physical.word (k+1) :=
    (b.sizes (Nat.succ_pos k)).2.2.2.1.trans (b.sizes (Nat.succ_pos k)).2.2.1.symm
  refine ⟨passing,sourceRows,finish,same.le,bounds.2.1,?_⟩
  exact same ▸ bounds.2.2.1

local notation3 (prettyPrint := false) "completedPath" => nativeCompletion p fit W position free count M bottom installed
  y hy pos hg packet cubePos bank cube scales b room batchEq candidateEq teamsEq cubeEq alphabetEq fields cover small
  seedCap time ord i u occupied occupied_le packed scalar X header passing finish

/-- The all-team input of the residue-reader ledger equals the selected
original term's column at every numbered parameter and scalar position. -/
theorem nativeCompletion_totals (c : Fin (parameterCount (2*(k+1)) k s+U)) :
    (∑ t,(completedPath).rows t c) =
      ∑ t,DiagonalTallyRAM.tallyRow ((assigned p fit W position free count M bottom installed
        y hy pos hg packet cubePos bank ord i u).numberScalars scalar) t c :=
  sum_nativeRow p fit W position free count M bottom installed y hy pos hg packet cubePos bank ord scalar i u c

open TeamContraction.ProcessorSlots

omit finish in
/-- Select each true native operand receipt once. The very same dependent
return completes the guarded source and certifies the low-memory protection
that the reader later needs. The selected rows are precisely those of the
original numbered history. -/
theorem exists_nativeProtectedCompletion
    (layout : Fin (R+1) → SignedTaskArena.Layout) (arena : Fin (R+1) → StartupArena)
    (physical : ∀ raw t, let rr := canonicalReports X.assigned passing
      let S₀ := X.team rr raw t
      let a₀ := (X.candidate rr raw).1 t
      let mac := install gen (k+1) S₀.routines
      ∃ receipt : PositiveFields.FinishInput t sourceRows (b.physical.tally (k+1)) S₀.pub mac
        (cellBank S₀.pub mac a₀.2.val.2.1 a₀.2.val.2.2) a₀.2.val.2.2 (header.withSubtotals raw).tallyWords,
      receipt.post=(layout t).after ∧ (∀ j<(layout t).after.start, j≠(S₀.pub 0).val+35 →
        receipt.selected j=a₀.2.val.2.2 j) ∧ (S₀.pub 0).val=(arena t).frame ∧ (arena t).next≤(layout t).cube.header.header) :
    ∃ H : X.Completion header, H.rows=sourceRows ∧
      (∀ raw t, H.Protected X raw t (layout t) (arena t)) ∧
      ∀ c, (∑ t,H.rows t c) = ∑ t,DiagonalTallyRAM.tallyRow ((assigned p fit W position free count M bottom installed
        y hy pos hg packet cubePos bank ord i u).numberScalars scalar) t c := by
  choose finish evidence using physical
  let H := nativeCompletion p fit W position free count M bottom installed y hy pos hg packet cubePos bank cube
    scales b room batchEq candidateEq teamsEq cubeEq alphabetEq fields cover small seedCap time ord i u
    occupied occupied_le packed scalar X header passing finish
  refine ⟨H,rfl,?_,?_⟩
  · intro raw t
    obtain ⟨base,kept,frame,place⟩ := evidence raw t
    exact ⟨base,kept,frame,place⟩
  · exact nativeCompletion_totals p fit W position free count M bottom installed y hy pos hg packet cubePos bank cube
      scales b room batchEq candidateEq teamsEq cubeEq alphabetEq fields cover small seedCap time ord i u occupied
      occupied_le packed scalar X header passing finish

variable (reports : NativeReports X.assigned) (raw : Fin ((R+1)*(parameterCount (2*(k+1)) k s+U)*b.physical.tally (k+1)) → Bool)

/-- Across all report guesses and all shared words the native checks recover
the current owner counts of this particular original assignment. -/
theorem nativeCompletion_fields :
    positivePass (X.team reports raw) (X.joined reports raw) (X.candidate reports raw) ↔
      reports = canonicalReports X.assigned passing ∧ raw = PositiveFields.canonicalSubtotals (b.physical.tally (k+1)) sourceRows :=
  (X.completed completedPath).pass_iff reports raw

/-- The actual chosen returning suffix on any passing proposal writes the
integer sum from the original numbered term at its physical output address. -/
theorem nativeCompletion_word (pass : positivePass (X.team reports raw) (X.joined reports raw) (X.candidate reports raw))
    (t : Fin (R+1)) (c : Fin (parameterCount (2*(k+1)) k s+U)) (j : ℕ) (hj : j<b.physical.word (k+1)) :
    let a := (X.candidate reports raw).1 t
    let out := ((X.team reports raw t).finish a (pass.2 t)).val.2.2
    out ((finish raw t).outputBase (header.withSubtotals raw)+(c.val*b.physical.word (k+1)+j)) =
      DiagonalResidueRAM.word (b.physical.word (k+1))
        (((∑ v, DiagonalTallyRAM.tallyRow (nativeTally p fit W position free count M bottom installed y hy pos hg
          packet cubePos bank ord scalar i u) v c).testBit j).toNat) := by
  have read := RoutingISA.Evaluator.UncheckedCandidate.Completion.finish_output X completedPath reports raw pass t c j hj
  exact read.trans (congrArg (fun z : ℕ => DiagonalResidueRAM.word (b.physical.word (k+1)) ((z.testBit j).toNat))
    (sum_nativeRow p fit W position free count M bottom installed y hy pos hg packet cubePos bank ord scalar i u c))

end Diagonal.CellEntries.EnrichedTape

end BorderVNP
end Computability
end OAI
