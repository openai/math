import OAI.Computability.BorderVNP.CubePhysicalNumberedPlacement
import OAI.Computability.BorderVNP.DiagonalNumberedEnrichedTape

/-! # True native subtotal columns of each fully assigned enriched history -/

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

/-- Enumerate the true original batch numbers in the nested public history. -/
noncomputable local instance nativeRowBatchFinite {j : ℕ} : Fintype (Port (EnrichedOuter.fan S) (Fin copies × Unit) j) :=
  Replay.batchFinite (EnrichedOuter.fan S) (Fin copies × Unit) j

variable {cn cd cb ch cK cs : ℕ} {Pin : Type}
    (packet : ∀ q, PacketPlacement (Port (EnrichedOuter.fan S) (Fin copies × Unit) T)
      cn cd cb ch cK (network p fit position free count M bottom installed q))
    (cubePos : TableEntry cn cb ch cK cs → Gadget)
    (bank : Pin → Ports (fun _ : FreeBlock R (tileCount axes gridDepth) =>
      inputBlockWidth r (k+1) axes gridDepth))


open BorderVNP.Cube.Physical ParseTable
set_option maxHeartbeats 2200000
set_option maxRecDepth 18000

variable {U : ℕ} (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) (scalar : Gadget ≃ Fin U) (i : Pin)
    (v : assignedPath p fit W position free count M bottom installed y hy pos hg packet cubePos bank i)

/-- Subtotals emitted by the current owner of each packed site and packet
vertex, with the grammar and dense scalar IDs used by the actual reader. -/
noncomputable def nativeRow :=
  Assigned.nativeRow (network p fit position free count M bottom installed) packet
    (tags p fit W position free count M bottom installed y hy pos hg) (fun i _ => bank i) cubePos ord
    (SewnTape.teamNumber (EnrichedOuter.fan S) T copies R count) scalar i v

/-- Original batch-indexed term, with its scalar columns numbered by the
same dense table directory the packet lookup uses. -/
noncomputable abbrev nativeTally :=
  (assigned p fit W position free count M bottom installed y hy pos hg packet cubePos bank ord i v).numberScalars scalar

/-- Exact identity on the original use bits and true lookup multiplicities. -/
theorem nativePathTally_eq :
    Assigned.nativePathTally (network p fit position free count M bottom installed) packet
      (tags p fit W position free count M bottom installed y hy pos hg) (fun i _ => bank i) cubePos ord
      (SewnTape.teamNumber (EnrichedOuter.fan S) T copies R count) scalar i v =
    nativeTally p fit W position free count M bottom installed y hy pos hg packet cubePos bank ord scalar i v :=
  Assigned.nativeTally_eq (network p fit position free count M bottom installed) packet
    (tags p fit W position free count M bottom installed y hy pos hg) (fun i _ => bank i) cubePos ord
    (SewnTape.teamNumber (EnrichedOuter.fan S) T copies R count) scalar i v

/-- Summing all current physical owners recovers the numbered columns of
the true fully assigned term (11.2). -/
theorem sum_nativeRow (j : Fin (Branch.pairedTableParameters (k+1) s + U)) :
    (∑ t, nativeRow p fit W position free count M bottom installed y hy pos hg packet cubePos bank ord scalar i v t j) =
    ∑ t, DiagonalTallyRAM.tallyRow
      (nativeTally p fit W position free count M bottom installed y hy pos hg packet cubePos bank ord scalar i v) t j :=
  Assigned.nativeRow_sum (network p fit position free count M bottom installed) packet
    (tags p fit W position free count M bottom installed y hy pos hg) (fun i _ => bank i) cubePos ord
    (SewnTape.teamNumber (EnrichedOuter.fan S) T copies R count) scalar i v j

/-- The present physical owners' contributions to an original grammar
parameter sum to that parameter's true formal exponent. -/
theorem sum_native_parameter (j : Fin (Branch.pairedTableParameters (k+1) s)) :
    (∑ t, nativeRow p fit W position free count M bottom installed y hy pos hg packet cubePos bank ord scalar i v t
      (Fin.castAdd U j)) =
    (assigned p fit W position free count M bottom installed y hy pos hg packet cubePos bank ord i v).exponents j :=
  (sum_nativeRow p fit W position free count M bottom installed y hy pos hg packet cubePos bank ord scalar i v
    (Fin.castAdd U j)).trans (DiagonalTallyRAM.tallyRow_parameter _ j)

/-- The scalar's total count includes every genuine use in a cell or a cube
packet, in the dense native position of the original scalar. -/
theorem sum_native_scalar (g : Gadget) :
    (∑ t, nativeRow p fit W position free count M bottom installed y hy pos hg packet cubePos bank ord scalar i v t
      (Fin.natAdd (Branch.pairedTableParameters (k+1) s) (scalar g))) =
    ∑ t, (assigned p fit W position free count M bottom installed y hy pos hg packet cubePos bank ord i v).counts t g := by
  refine (sum_nativeRow p fit W position free count M bottom installed y hy pos hg packet cubePos bank ord scalar i v _).trans
    ((DiagonalTallyRAM.tallyRow_gadget _ (scalar g)).trans ?_)
  simp only [nativeTally,Tally.numberScalars,Equiv.symm_apply_apply]

end Diagonal.CellEntries.EnrichedTape

end BorderVNP
end Computability
end OAI
