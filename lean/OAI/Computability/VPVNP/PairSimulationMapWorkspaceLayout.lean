import OAI.Computability.VPVNP.PairSimulationMapWorkspace

/-!
# Consecutive scratch regions for a native map call

The live histogram and operand fields may be at different addresses from one
call to the next. Above their exclusive ends the caller reserves space for
the port directory, the fixed argument descriptor, the selector ordinals, and
the output labels. The two copy arrays have the same capacity.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapWorkspace

open MotifSelector MotifGrid MotifBlocks MotifConversion MapLookup MapPortAgreement
open CursorBounds Filter

variable {D E : Type} [Fintype D] [Fintype E]

/-- Reserve the two possible ends of each supply edge before the argument descriptor. -/
def descriptorBase (E : Type) [Fintype E] (directory : ℕ) : ℕ :=
  directory + 2 * Fintype.card E

/-- The selector ordinals start immediately after the fixed descriptor. -/
def ordinalBase (D E : Type) [Fintype D] [Fintype E] (directory : ℕ) : ℕ :=
  descriptorBase E directory + Fintype.card (MapCallSetup.Arg D E)

/-- The label array follows the reserved selector-ordinal array. -/
def scratchRegions (fieldBase : LabelField D E → ℕ) (directory hist copies : ℕ) :
    Regions D E where
  base := fieldBase
  directory := directory
  source := ordinalBase D E directory
  target := ordinalBase D E directory + copies
  hist := hist

/-- Exclusive end of the label array, including its unused reserved capacity. -/
def scratchEnd (D E : Type) [Fintype D] [Fintype E] (directory copies : ℕ) : ℕ :=
  ordinalBase D E directory + copies + copies

variable {J K : Type} [Fintype J] [DecidableEq J] [Field K]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  {B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H'}
  {z : B.grid.demands} {j : J} {p r k w n u t copies hist directory limit : ℕ}
  (P : MapEntry.Program B z j p r k) (demand : D → ℕ) (v : E → ℕ)
  (fieldBase : LabelField D E → ℕ)

/-- The descriptor has a distinct address for each argument, strictly before
the first scratch ordinal. -/
theorem descriptorWord_lt (D E : Type) [Fintype D] [Fintype E] (directory : ℕ)
    (a : Fin (Fintype.card (MapCallSetup.Arg D E))) :
    descriptorBase E directory + a.val < ordinalBase D E directory :=
  Nat.add_lt_add_left a.isLt _

/-- All writable map arrays are separated for any supplied operand bases whose
ends and the live histogram precede the directory. -/
theorem scratchRegions_ordered
    (fields : ∀ f, fieldBase f + rawWidth demand v B.selectorBits u f ≤ directory)
    (histEnd : hist + t ≤ directory) (hc : u ≤ copies)
    (room : scratchEnd D E directory copies ≤ limit) :
    Ordered P demand v (scratchRegions fieldBase directory hist copies) u t limit := by
  have hports := ports_length_le G j P.edgeOrder
  dsimp only [scratchEnd, ordinalBase, descriptorBase] at room
  constructor <;> dsimp only [scratchRegions, ordinalBase, descriptorBase]
  · exact fields
  · omega
  · omega
  · omega
  · omega
  · exact Or.inr histEnd

variable (d : MotifEntry.DemandBits src dst demand j)
    (x : Half G (fun e ↦ Fin (v e + u * B.selectorBits) → Bool) j)

/-- The natural layout supplies the workspace of the actual native map program,
including all selector-dependent reads on unsuccessful choices. -/
noncomputable def scratchWorkspace (C : Capacity B w n limit) (hu : u ≤ n)
    (fields : ∀ f, fieldBase f + rawWidth demand v B.selectorBits u f ≤ directory)
    (histEnd : hist + t ≤ directory) (hc : u ≤ copies)
    (room : scratchEnd D E directory copies ≤ limit) :
    MapEntry.Program.Workspace P demand v d x t w :=
  workspace P (scratchRegions fieldBase directory hist copies) d x C hu
    (scratchRegions_ordered P demand v fieldBase fields histEnd hc room)

/-- Above field and histogram starts at most `n ^ 5`, leave room for a payload
of at most `n` bits and every selector suffix of at most `n` copies. -/
def liveDirectory (selectorBits counters n : ℕ) : ℕ :=
  n ^ 5 + n + n * selectorBits + counters

omit [DecidableEq J] in
theorem eventually_scratchCapacity
    (B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H')
    (b t : ℕ) (hb : 1 ≤ b) :
    ∀ᶠ n : ℕ in atTop, Capacity B (wordBits b n) n
      (scratchEnd D E (liveDirectory B.selectorBits t n) n) := by
  apply eventually_capacity (B := B) b hb
  unfold scratchEnd ordinalBase descriptorBase liveDirectory
  have tags := PolynomiallyBounded.id.mul (PolynomiallyBounded.const B.selectorBits)
  have directory := (((PolynomiallyBounded.id.pow 5).add PolynomiallyBounded.id).add tags).add
    (PolynomiallyBounded.const t)
  have descriptors := directory.add (PolynomiallyBounded.const (2 * Fintype.card E))
  have ordinals := descriptors.add (PolynomiallyBounded.const (Fintype.card (MapCallSetup.Arg D E)))
  exact (ordinals.add PolynomiallyBounded.id).add PolynomiallyBounded.id

/-- The same capacity, fixed before the branch, constructs workspaces for all
map inputs of these numerical sizes. No equality of the proposed total widths
with the selected payload is required. -/
noncomputable def liveWorkspace
    (C : Capacity B w n (scratchEnd D E (liveDirectory B.selectorBits t n) n))
    (hu : u ≤ n) (hbase : ∀ f, fieldBase f ≤ n ^ 5) (hhist : hist ≤ n ^ 5)
    (hd : ∀ e, demand e ≤ n) (hv : ∀ e, v e ≤ n) :
    MapEntry.Program.Workspace P demand v d x t w := by
  apply scratchWorkspace P demand v fieldBase d x C hu (copies := n)
    (directory := liveDirectory B.selectorBits t n) (hist := hist)
  · intro f
    rcases f with ⟨b, e⟩ | ⟨b, e⟩
    · have := hbase (.inl (b, e))
      have := hd e
      simp only [rawWidth, liveDirectory]
      omega
    · have := hbase (.inr (b, e))
      have := hv e
      have := Nat.mul_le_mul_right B.selectorBits hu
      simp only [rawWidth, liveDirectory]
      omega
  · unfold liveDirectory
    omega
  · exact hu
  · rfl

end PairSimulation.MapWorkspace

end VPVNP
end Computability
end OAI
