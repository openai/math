import OAI.Computability.BorderVNP.DiagonalPositiveHeaderSyntax
import OAI.Computability.BorderVNP.CubePhysicalAlignedClaims
import OAI.Computability.BorderVNP.CubeTeamDeclarationReturn

/-! # Header fields forced by actual distributed declaration and subtotal scans -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.JointHeader.PositiveFields

open VPVNP.BurstRAM RoutingISA _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.Physical.Owned Cube.TeamRows DiagonalResidueRAM
open DiagonalTallyMaterialize (Operand)

variable {reserve axes groups cap teams dim tally w : ℕ}
local notation "Fields" => PositiveFields reserve axes groups cap teams dim tally

/-- Numerical contents of the proposed physical subtotal words, including guesses
that a subsequent tally check will reject. -/
def rawCounts (p : Fields) (u : Fin teams) (c : Fin dim) : ℕ :=
  (DiagonalTallyRAM.fieldWord tally p.tallyWords u c).val

/-- Every exact-width raw subtotal suffix is already the little-endian encoding
of its unverified numerical values. This allows geometry reconstruction to run
on an arbitrary parsed header before any claimed subtotal has been checked. -/
theorem tallyWords_rawCounts (p : Fields) : p.tallyWords = DiagonalTallyRAM.broadcast tally p.rawCounts := by
  have bound (u : Fin teams) (c : Fin dim) : p.rawCounts u c < 2^tally :=
    (DiagonalTallyRAM.fieldWord tally p.tallyWords u c).isLt
  have eq (u : Fin teams) (c : Fin dim) : DiagonalTallyRAM.fieldWord tally p.tallyWords u c = word tally (p.rawCounts u c) :=
    Fin.ext (word_val _ _ (bound u c)).symm
  apply (DiagonalTallyRAM.unique_broadcast p.rawCounts le_rfl bound).unique
  · exact ⟨p.tallyWords_length,p.tallyWords_width,eq⟩
  · exact ⟨field_count p.rawCounts tally,field_width p.rawCounts tally,DiagonalTallyRAM.fieldWord_broadcast _ bound⟩

/-- No extra bit follows the last subtotal digit in the parsed positive branch. -/
theorem bits_eq_emitted (p : Fields) :
    p.bits = Cube.RouteRecords.emittedHeader p.profile p.cube tally p.rawCounts 0 := by
  simp only [bits,Cube.RouteRecords.emittedHeader,padded,evaluation,JointHeader.spelling,
    List.replicate_zero,List.append_nil,List.append_assoc,← tallyWords_rawCounts,tallyWords_flatten]

/-- Native signed allocator and subtotal returns at every team force all of the
original received words, including every transmitted digit of every local count. -/
theorem tally_of_returns (p : Fields) (rows : Fin teams → Fin dim → ℕ)
    (fit : tally ≤ w) (bounded : ∀ i c, rows i c < 2^tally) (arenas : Fin teams → DiagonalTallyRAM.Arena)
    (pub : Fin teams → Arg → Word w) (mac : Fin teams → TeamOpcode.Macros w 8) (state : Fin teams → Bank w)
    (mem : Fin teams → Memory w) (os : Fin teams → List Operand) (ptr : Fin teams → ℕ)
    (dimensions : ∀ i, (arenas i).dim = dim) (team : ∀ i, (arenas i).team = i.val)
    (source : ∀ i, DiagonalTallyRAM.AlignedAllocationInput (arenas i) (pub i) (mem i) (os i) p.tallyWords (ptr i))
    (actual : ∀ i (c : Fin dim), (arenas i).localRow (os i) c.val = rows i c)
    (returns : ∀ i, ∃ es t mt, Runs (pub i) (mac i) DiagonalTallyRAM.alignedAllocateAndEvaluate (state i) (mem i) es t mt) :
    List.ofFn p.subtotals = (DiagonalTallyRAM.broadcast tally rows).flatten := by
  rw [← tallyWords_flatten]
  exact congrArg List.flatten (DiagonalTallyRAM.broadcast_of_aligned_runs rows p.tallyWords p.tallyWords_length
    p.tallyWords_width fit bounded arenas pub mac state mem os ptr dimensions team source actual returns)

variable {blocks b h K s : ℕ}
local notation "cubeCap" => declarationCap axes groups blocks b h s

/-- The native row checks and the returned public least-coordinate scan force
every raw cube declaration bit, including when a code word has surplus range. -/
theorem cube_of_returns (p : PositiveFields reserve axes groups cubeCap teams dim tally)
    (select : Packet axes groups blocks → Selector axes K h) (axis : Fin (axes+1))
    (coord : readCode (axes+1) p.cube.1 = axis.val) (owner : Fin groups → Fin teams)
    (pub : Fin teams → Arg → Word w) (mac : Fin teams → TeamOpcode.Macros w 8)
    (checks : CheckedScans owner pub mac (axis,fun row j => readCode _ (p.cube.2 row j)) select b s)
    (labels : groups^(axes+1) ≤ 2^w) (packets : packetTrials axes groups blocks*(h*s) < 2^w)
    (capacity : cubeCap < 2^w) {arg : Arg → Word w} {routines : TeamOpcode.Macros w 8}
    {r : Bank w} {m : Memory w} {es t mt}
    (minimum : Runs arg routines CubeLengths.publicMinimum r m es t mt) (fit : CubeLengths.Fits w (readings arg) (readings m))
    (shape : (CubeLengths.layout (readings arg) (readings m)).entries = groups*groups*(axes+1))
    (directions : (CubeLengths.layout (readings arg) (readings m)).coordinates = axes+1)
    (index : (CubeLengths.layout (readings arg) (readings m)).chosen = axis.val)
    (table : CubeLengths.StoredRows (readings m) (CubeLengths.layout (readings arg) (readings m)).claimed
      (fun row j => readCode _ (p.cube.2 row j))) : p.cube = Cube.Physical.broadcast b s select :=
  (passesBroadcast_iff b s select p.cube).mp ⟨axis,coord,
    (checks.passes labels packets capacity minimum fit shape directions index table).1⟩

/-- Fixed reconstructed source history, selector tuple and actual subtotal rows
determine the entire physical header. -/
theorem emitted_of_checked {I : Type*} {valid : (Fin reserve → Bool) → Prop} (encode : I ≃ {x // valid x})
    (p : PositiveFields reserve axes groups cubeCap teams dim tally) (history : I) (accept : valid p.profile)
    (source : encode.symm ⟨p.profile,accept⟩ = history) (select : Packet axes groups blocks → Selector axes K h)
    (rows : Fin teams → Fin dim → ℕ) (cube : p.cube = Cube.Physical.broadcast b s select)
    (bank : List.ofFn p.subtotals = (DiagonalTallyRAM.broadcast tally rows).flatten) :
    p.bits = Cube.RouteRecords.emittedHeader (encode history).val (Cube.Physical.broadcast b s select) tally rows 0 := by
  have profile := congrArg Subtype.val ((encode.symm_apply_eq).mp source).symm
  simp only [bits,Cube.RouteRecords.emittedHeader,padded,evaluation,JointHeader.spelling,
    List.replicate_zero,List.append_nil,List.append_assoc,profile,cube,bank]

end TeamContraction.JointHeader.PositiveFields

end BorderVNP
end Computability
end OAI
