import OAI.Computability.VPVNP.PrimedInputRAMRows
import OAI.Computability.VPVNP.PrimedInputRAMCopy

/-!
# Two-pass assembly of the inputs to the primed coefficient counter

The first pass branches at every internal bit's designated physical cell.
The second pass reads one fixed header or scratch address when needed,
then writes the resulting bit to a separate rectangular input array. The
proof identifies the result, at every parse leaf, with the full primed
coefficient-machine input. No validator is called on any shared bit string.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM

open BurstRAM

/-- Number of input cells in one rectangular pass, with n bits per site in each of two groups
of 2^r sites. -/
abbrev positions (n r : ℕ) := (2 * 2^r) * n

/-- The two rectangular arrays are placed after the auxiliary headers.
The three supplied cut lengths have addresses 0, 1, 2. The histogram
may occupy reserved addresses beyond the bit arrays before `scratchBase`. -/
structure Layout (L : Lengths) (n r H w : ℕ) where
  /-- Universal-machine program whose literal prefix is embedded in every assembled processor
  input. -/
  program : UniversalMachine.Program
  fits : ProcessorInput.Fits program n r H w
  middleFits : L.middleCut ≤ 2^r
  /-- Beginning of the first-pass choice rectangle in external memory. -/
  scratchBase : ℕ
  headersFit : Header.count L ≤ scratchBase
  addressesFit : scratchBase + positions n r + positions n r ≤ 2^w

variable {L : Lengths} {n r H w : ℕ}

namespace Layout

variable (Q : Layout L n r H w)

/-- The loop counters range over row-major cells of the `2R` full tapes. -/
def coordinates :
    (Site r × RowField Q.program n r H w) ≃ Fin (positions n r) :=
  (finProdFinEquiv.prodCongr (rowIndex Q.program Q.fits)).trans finProdFinEquiv

/-- Whether this rectangular position is the designated location that chooses a shared internal
bit. -/
def owns (i : Fin (positions n r)) : Bool := cellOwner L (Q.coordinates.symm i)

/-- Exact equivalence between internal summation indices and branch cells
of the actual flattened first-pass loop. -/
def internalOwner : Internal L r H w ≃ {i : Fin (positions n r) // Q.owns i = true} :=
  (ownerEquiv _ _ Q.middleFits).trans (Q.coordinates.subtypeEquiv (by
    intro c; simp [owns]))

/-- Injective word address of a first-pass scratch cell, obtained by offsetting its rectangular
index from the scratch base. -/
def bitAddress : Fin (positions n r) ↪ Word w :=
  scratchAddress Q.scratchBase (by have := Q.addressesFit; omega)

/-- Injective word address in the second-pass output rectangle immediately following first-pass
scratch. -/
def outputAddress : Fin (positions n r) ↪ Word w :=
  scratchAddress (Q.scratchBase + positions n r) Q.addressesFit

/-- Word address of the specified header field below the scratch rectangle. -/
def readHeader (j : Header L) : Word w :=
  ⟨j.address.val, j.address.isLt.trans_le (Q.headersFit.trans (by have := Q.addressesFit; omega))⟩

/-- Inverse of the chosen-address map for the branch stream. -/
def assignment (bits : Internal L r H w → Bool) : Assignment Q.owns :=
  bits ∘ Q.internalOwner.symm

/-- All admissible branch streams, including those encoding inconsistent
primed messages, are enumerated exactly once. -/
def streamEquiv (bitWord : Bool → Word w) (initial : Memory w) :
    {bs : List Bool // (firstPass Q.owns Q.bitAddress bitWord bs initial).isSome = true} ≃
      (Internal L r H w → Bool) :=
  (admissibleEquiv Q.owns Q.bitAddress bitWord initial).trans
    (Q.internalOwner.symm.arrowCongr (Equiv.refl _))

private def reference (i : Fin (positions n r)) : Ref L r H w :=
  cellRef L (UniversalMachine.programPrefix Q.program).get (Q.coordinates.symm i)

/-- Resolve a literal, header reference or shared internal bit to the immediate word or RAM
address used by the copy pass. -/
def refSource (bitWord : Bool → Word w) : Ref L r H w → CopySource w
  | .literal b => .literal (bitWord b)
  | .header j => .fetch (Q.readHeader j)
  | .shared b => .fetch (Q.bitAddress (Q.internalOwner b).val)

/-- Source of the second-pass copy for this rectangular input position. -/
def source (bitWord : Bool → Word w) (i : Fin (positions n r)) : CopySource w :=
  Q.refSource bitWord (Q.reference i)

private theorem separated (bitWord : Bool → Word w) :
    CopySeparated Q.outputAddress (Q.source bitWord) := by
  intro i j a h
  unfold source at h
  cases hr : Q.reference i with
  | literal b => simp [hr, refSource] at h
  | header k =>
    simp [hr, refSource] at h
    subst a
    intro he
    have hh := congrArg Fin.val he
    change k.address.val = Q.scratchBase + positions n r + j.val at hh
    have := k.address.isLt
    have := Q.headersFit
    omega
  | shared b =>
    simp [hr, refSource] at h
    subst a
    intro he
    have hh := congrArg Fin.val he
    change Q.scratchBase + (Q.internalOwner b).val.val = Q.scratchBase + positions n r + j.val at hh
    have := (Q.internalOwner b).val.isLt
    omega

/-- Store the chosen bits and perform all deterministic copies. -/
def assemble (bitWord : Bool → Word w) (bs : List Bool) (initial : Memory w) : Option (Memory w) :=
  (firstPass Q.owns Q.bitAddress bitWord bs initial).map
    (secondPass Q.outputAddress (Q.source bitWord))

/-- Final RAM after storing the given internal bit assignment at its owners and copying every
processor-input cell. -/
def assembled (bitWord : Bool → Word w) (bits : Internal L r H w → Bool)
    (initial : Memory w) : Memory w :=
  secondPass Q.outputAddress (Q.source bitWord)
    (store Q.bitAddress (bitWord ∘ bitAt (Q.assignment bits)) (owners Q.owns) initial)

theorem assemble_branches (bitWord : Bool → Word w) (bits : Internal L r H w → Bool)
    (initial : Memory w) :
    Q.assemble bitWord (branches (Q.assignment bits)) initial = some (Q.assembled bitWord bits initial) := by
  simp only [assemble, firstPass_branches, Option.map_some, assembled]

private theorem read_ref (bitWord : Bool → Word w) (bits : Internal L r H w → Bool)
    (hdr : Header L → Bool) (initial : Memory w)
    (hi : ∀ j, initial j.address.val = bitWord (hdr j)) (ref : Ref L r H w) :
    CopySource.get (store Q.bitAddress (bitWord ∘ bitAt (Q.assignment bits)) (owners Q.owns) initial)
      (Q.refSource bitWord ref) = bitWord (ref.value hdr bits) := by
  cases ref with
  | literal b => rfl
  | header j =>
    change store _ _ _ initial j.address.val = bitWord (hdr j)
    rw [bitAddress, store_header _ _ _ _ initial (j.address.isLt.trans_le Q.headersFit), hi]
  | shared b =>
    have hb := (Q.internalOwner b).property
    change store _ _ _ initial (Q.bitAddress (Q.internalOwner b).val).val = bitWord (bits b)
    rw [store_at _ _ _ _ ((mem_owners _ _).mpr hb)]
    simp [bitAt, hb, assignment]

/-- After the two passes, the grammar parser can fetch the selected leaf bit
in a single word read. This holds for every internal assignment. -/
theorem assembled_input (bitWord : Bool → Word w) (bits : Internal L r H w → Bool)
    (hdr : Header L → Bool) (initial : Memory w)
    (hi : ∀ j, initial j.address.val = bitWord (hdr j)) (u : Site r) (j : Fin n) :
    Q.assembled bitWord bits initial (Q.outputAddress (finProdFinEquiv (finProdFinEquiv u,j))).val =
      bitWord (input Q.program Q.fits hdr bits u j) := by
  obtain ⟨f,rfl⟩ := (rowIndex Q.program Q.fits).surjective j
  change Q.assembled bitWord bits initial (Q.outputAddress (Q.coordinates (u,f))).val = _
  rw [assembled, secondPass_at _ _ _ (Q.separated bitWord), source, read_ref _ _ _ _ _ hi,
    reference, Equiv.symm_apply_apply, input_at]

/-- Number of calls plus probes of the two passes. The first pass makes at
most one write per cell. The second makes at most one read and one write. -/
theorem twoPass_cost (bitWord : Bool → Word w) (bits : Internal L r H w → Bool)
    (next₁ next₂ : Fin (positions n r) → Word w) (initial : Memory w) :
    let cells := List.finRange (positions n r)
    let f := bitAt (Q.assignment bits)
    let m := store Q.bitAddress (bitWord ∘ f) (owners Q.owns) initial
    RAMBuckets.cost Report.probes (reports Q.owns Q.bitAddress next₁ bitWord f cells) +
      RAMBuckets.cost Report.probes (copyReports Q.outputAddress (Q.source bitWord) next₂ cells m) ≤
      5 * positions n r := by
  dsimp only
  rw [reports_cost, List.length_finRange]
  have h1 := owners_length_le Q.owns
  have h2 := copyReports_cost_le Q.outputAddress (Q.source bitWord) next₂ (List.finRange _)
    (store Q.bitAddress (bitWord ∘ bitAt (Q.assignment bits)) (owners Q.owns) initial)
  rw [List.length_finRange] at h2
  change (List.filter Q.owns (List.finRange (positions n r))).length ≤ _ at h1
  omega

end Layout
end PrimedInputRAM

end VPVNP
end Computability
end OAI
