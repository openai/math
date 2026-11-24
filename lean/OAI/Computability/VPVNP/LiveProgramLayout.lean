import OAI.Computability.VPVNP.LiveHeaderExpressions
import OAI.Computability.VPVNP.PrimedStackRAMLayout
import OAI.Computability.VPVNP.RAMParameters

/-!
# Public geometry and disjoint working regions of the live program

The group header occupies addresses below `2^d`. The external tag, the
header parser's own workspace and the remaining arrays start above it. The
shadow of the auxiliary RAM has room for every virtual site. Unused shadow
addresses have zero default and need no initialization.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram
open PublicExpr

/-- Fixed choices for a circuit exponent and a fixed expander and evaluator. -/
structure Constants where
  /-- Circuit-size exponent used in the grammar state bound `n^(circuitExponent + 5)`. -/
  circuitExponent : ℕ
  /-- Exponent giving the height parameter of the paired chain as a power of the input length. -/
  chainPower : ℕ
  /-- Exponent giving the capacity of the live header’s advice field as a power of the input
  length. -/
  advicePower : ℕ
  /-- Exponent giving the cut-width parameter of the live header as a power of the input
  length. -/
  deltaPower : ℕ
  /-- Exponent giving the radius of the bounded tape windows in an evaluator configuration. -/
  radiusPower : ℕ
  /-- Exponent reserving space for the packed literal prefix in the live memory layout. -/
  prefixPower : ℕ
  /-- Number of motif labels appended to the grammar production labels. -/
  motifLabels : ℕ

namespace Constants

/-- Public expression for the number of grammar states at length n, namely n raised to the
circuit exponent plus five. -/
def states (c : Constants) := PublicExpr.n.natPow (c.circuitExponent + 5)

/-- Number of terminal and ordered binary production labels. Terminals contribute two per
position and state, and each degree split contributes one per ordered triple of states. -/
def grammarLabels (c : Constants) : PublicExpr :=
  let states := c.states
  let pairs := .divConst (.mul .n (.sub .n 1)) 2
  states * .n * 2 + ((pairs*states)*states)*states

/-- Total number of counters for grammar productions and motif labels together. -/
def labels (c : Constants) := c.grammarLabels + .lit c.motifLabels
/-- Public chain height `n^chainPower`, one more than the header’s chain parameter h. -/
def height (c : Constants) := PublicExpr.n.natPow c.chainPower
/-- Number of exponent bits per label, twice the public chain height. -/
def Z (c : Constants) := 2 * c.height
/-- Radius of each evaluator tape window at the current input length. -/
def radius (c : Constants) := PublicExpr.n.natPow c.radiusPower
/-- Words per evaluator configuration, comprising one state word and two tape windows of twice
the radius plus one cell each. -/
def configWords (c : Constants) := 1 + (2*c.radius+1) + (2*c.radius+1)
/-- Reserved capacity for storing the program prefix at the current input length. -/
def prefixCapacity (c : Constants) := PublicExpr.n.natPow c.prefixPower

/-- Header parameters for chain height minus one, cut width, advice capacity, total exponent
bits, and the two-tape configuration’s bit length. -/
def lengths (c : Constants) : Lengths := ⟨.sub c.height 1, PublicExpr.n.natPow c.deltaPower,
  PublicExpr.n.natPow c.advicePower, c.labels*c.Z, c.configWords * .w⟩

/-- Concrete triangular production index used in the auxiliary preorder parser. -/
theorem grammarLabels_eq (c : Constants) (g : Geometry) :
    c.grammarLabels.eval g = PrimedStackRAM.labelCount g.n g.n (g.n^(c.circuitExponent+5)) := by
  simp [grammarLabels, states, PublicExpr.eval, PrimedStackRAM.labelCount, Nat.choose_two_right]

end Constants

namespace Layout

/-- Address of the external dispatch tag, immediately above the range of the d-bit site
addresses. -/
def stageTag : PublicExpr := .pow2 .d
/-- Start of the live header parser’s workspace, one word after the stage tag. -/
def header := stageTag + 1
/-- Start of the auxiliary descriptor table at the end of the live header workspace. -/
def descriptor (c : Constants) := HeaderLayout.limit c.lengths header
/-- Start of the label-counter array after the seven three-word auxiliary descriptors. -/
def counter (c : Constants) := descriptor c + 21
/-- Start of the saved evaluator configuration immediately after the label counters. -/
def oldState (c : Constants) := counter c + c.labels
/-- Start of the next evaluator configuration after the saved configuration’s word array. -/
def newState (c : Constants) := oldState c + c.configWords
/-- Start of temporary storage for evaluator transitions after both configuration arrays. -/
def transitionScratch (c : Constants) := newState c + c.configWords
/-- Start of the advice frames after the five transition scratch words. -/
def adviceFrames (c : Constants) := transitionScratch c + 5
/-- Start of the packed literal-prefix area after the twenty-four advice-frame words. -/
def packedPrefix (c : Constants) := adviceFrames c + 24
/-- Reserve the full prefix capacity in addresses. Packing uses at most one
word per bit, including when the active prefix is shorter than its capacity. -/
def orderMap (c : Constants) := packedPrefix c + c.prefixCapacity
/-- Start of the virtual RAM shadow after the order map, which reserves one entry per label. -/
def shadow (c : Constants) := orderMap c + c.labels

/-- Virtual bucket exponent obtained by rounding the ceiling binary logarithm of n up to the
next multiple of four and dividing by four. -/
def virtualBucketBits : PublicExpr := .divConst (.add (.clog2 .n) 3) 4
/-- Virtual site address width obtained by subtracting the virtual bucket exponent from the
ceiling binary logarithm of the total virtual capacity. -/
def virtualSiteBits : PublicExpr := .sub (.clog2 (stageTag * .n * (.clog2 .n))) virtualBucketBits
/-- Start of the pair table’s workspace after reserving one shadow word per virtual site. -/
def pairWorkspace (c : Constants) := shadow c + .pow2 virtualSiteBits

theorem virtualSiteBits_eq (g : Geometry) (hn : 1 ≤ g.n) :
    virtualSiteBits.eval g = BurstRAM.virtualSiteExponent g.d g.n := by
  have he := Compression.bucketExponent_ratio_eq (a := 1) (b := 4) (by decide) hn
  have h := BurstRAM.roundedUp_eq 1 4 g.n
  simp only [pow_one] at he
  rw [BurstRAM.virtualSiteExponent, h, he]
  change Nat.clog 2 (2^g.d * g.n * Nat.clog 2 g.n) - (Nat.clog 2 g.n + 3)/4 = _
  rw [show Nat.clog 2 g.n + 4 - 1 = Nat.clog 2 g.n + 3 by omega]

end Layout
end LiveProgram

end VPVNP
end Computability
end OAI
