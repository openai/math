import OAI.Computability.VPVNP.LiveHeaderPhysical
import OAI.Computability.VPVNP.LiveHeaderPhases
import OAI.Computability.VPVNP.LiveHeaderMode
import OAI.Computability.VPVNP.PolynomialBounds

/-!
# Public schedule and scratch addresses for live header recovery

A group's number and its incoming and outgoing cuts stay in external memory.
The stage order, allocated buffer sizes and per-stage limits are public. Each
bounded field scan consults the private descriptor before probing a site.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderSchedule

open LiveHeaderWidths LiveHeaderDescriptors

/-- The four field sizes selected before the simulation exponent is chosen.
The chain has height `h+1`. The exponent array has `e=tZ` individual bits. -/
structure Sizes where
  /-- The height parameter of the live chain, whose two halves each contain two to this power
  groups. -/
  h : ℕ
  /-- The cut block width used to bound exterior and padding scans. -/
  delta : ℕ
  /-- The number of distributed advice bits copied into the live header workspace. -/
  advice : ℕ
  /-- The number of bits allocated to each exponent payload. -/
  e : ℕ
  /-- The serialized bit length allocated to each evaluator configuration. -/
  config : ℕ

/-- The stages of header recovery, from copying index and advice through metadata, primed
indices, and per-field descriptor and scan calls. -/
inductive Stage where
  | index | advice | width (s : Slot) | flag (f : Flag) | firstTail | mode
  | primedInit | primedDigits | descriptor (side : Side) (f : Field) | scan (side : Side) (f : Field)

/-- Descriptors and their consumers always alternate. The two descriptor
words can therefore be reused for all eight fields. -/
def stages : List Stage :=
  [.index,.advice,.width .liveLeft,.width .liveRight,.width .primedLeft,.width .primedMiddle,
   .width .primedRight,.flag .first,.flag .middle,.flag .firstHalf,.flag .last,.firstTail,
   .mode,.primedInit,.primedDigits] ++
  [Side.left,.right].flatMap fun side => [Field.exterior,.exponents,.config,.padding].flatMap
    fun f => [.descriptor side f,.scan side f]

theorem stage_count : stages.length = 31 := rfl

/-- The public number of positions available for scanning the specified incident field. -/
def Sizes.capacity (s : Sizes) : Field → ℕ
  | .exterior | .padding => (s.h+1)*s.delta
  | .exponents => s.e
  | .config => s.config

/-- A finite bound on each stage's number of microcalls. A bounded scan
uses one last, zero-probe call at its public limit to hand off. -/
def calls (s : Sizes) : Stage → ℕ
  | .index => s.h+2+1
  | .advice => s.advice+1
  | .primedDigits => s.h+1+1
  | .scan _ f => s.capacity f+1
  | _ => 1

/-- Per-stage local probes per active call, before the linking tag reads. -/
def probes : Stage → ℕ
  | .index => 6
  | .advice => 2
  | .firstTail => 4
  | .mode => 5
  | .primedDigits => 5
  | .descriptor .. => 6
  | .scan _ .padding => 3
  | .scan .. => 4
  | _ => 3

theorem probe_limit (i : Stage) : probes i ≤ 6 := by
  cases i <;> try (dsimp only [probes]; omega)
  rename_i f
  cases f <;> dsimp only [probes] <;> omega

/-- Allocating both sides and each public bound costs only polynomially many
calls. No multiplicative factor of the number of sites occurs. -/
def callBound (s : Sizes) : ℕ :=
  31 + (s.h+2) + s.advice + (s.h+1) + 4*((s.h+1)*s.delta) + 2*s.e + 2*s.config

theorem sum_calls (s : Sizes) : (stages.map (calls s)).sum = callBound s := by
  simp only [stages, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, calls, Sizes.capacity, callBound]
  omega

/-- The nested native stage dispatcher adds one tag probe per call and at
most one tag write at handoff. Including the enclosing dispatcher and the
call itself gives a bound of eleven cost units per call. -/
def costBound (s : Sizes) := 11 * callBound s

theorem polynomial_cost {S : ℕ → Sizes}
    (hh : PolynomiallyBounded fun n => (S n).h) (hd : PolynomiallyBounded fun n => (S n).delta)
    (ha : PolynomiallyBounded fun n => (S n).advice) (he : PolynomiallyBounded fun n => (S n).e)
    (hc : PolynomiallyBounded fun n => (S n).config) :
    PolynomiallyBounded fun n => costBound (S n) := by
  open PolynomiallyBounded in
    exact (const 11).mul (((((((const 31).add (hh.add (const 2))).add ha).add (hh.add (const 1))).add
      ((const 4).mul ((hh.add (const 1)).mul hd))).add ((const 2).mul he)).add ((const 2).mul hc))

/-- Widths for the auxiliary header occupy three consecutive words. -/
def widthAddr (base : ℕ) : Slot → ℕ
  | .liveLeft => base+1 | .liveRight => base+2 | .primedLeft => base+3
  | .primedMiddle => base+4 | .primedRight => base+5

/-- Address of the selected first, midpoint, first-half, or last flag in header scratch. -/
def flagAddr (base : ℕ) : Flag → ℕ
  | .first => base+6 | .middle => base+7 | .firstHalf => base+8 | .last => base+9

/-- Address of the scratch flag identifying the first evaluator group. -/
def firstTailAddr (base : ℕ) := base+10
/-- Address holding the selected live-header mode tag. -/
def tagAddr (base : ℕ) := base+11
/-- Address of the scratch word giving the next incident field's source offset. -/
def offsetAddr (base : ℕ) := base+12
/-- Address of the scratch word giving the next incident field's occupied length. -/
def countAddr (base : ℕ) := base+13
/-- Address of the borrow bit carried through primed index construction. -/
def borrowAddr (base : ℕ) := base+14
/-- Start of the unpacked one-based group index in header scratch. -/
def indexBase (base : ℕ) := base+15
/-- The cell after the group-index digits recording the highest set-bit position. -/
def highAddr (s : Sizes) (base : ℕ) := indexBase base + (s.h+2)
/-- The cell recording the number of set bits in the group index. -/
def populationAddr (s : Sizes) (base : ℕ) := highAddr s base + 1
/-- The first cell of the unpacked left primed index, after the index summary. -/
def leftIndexBase (s : Sizes) (base : ℕ) := populationAddr s base + 1
/-- The first cell of the unpacked right primed index, after the left index. -/
def rightIndexBase (s : Sizes) (base : ℕ) := leftIndexBase s base + (s.h+2)
/-- The first advice cell after both primed index arrays. -/
def adviceBase (s : Sizes) (base : ℕ) := rightIndexBase s base + (s.h+2)
/-- The base of the reserved exterior payload interval on the selected incident side. -/
def exteriorBase (s : Sizes) (base : ℕ) : Side → ℕ
  | .left => adviceBase s base + s.advice
  | .right => adviceBase s base + s.advice + s.capacity .exterior

/-- The base of the selected side's exponent array after both exterior reservations. -/
def exponentBase (s : Sizes) (base : ℕ) : Side → ℕ
  | .left => exteriorBase s base .right + s.capacity .exterior
  | .right => exteriorBase s base .right + s.capacity .exterior + s.e

/-- The base of the selected side's evaluator configuration array after the exponent arrays. -/
def configBase (s : Sizes) (base : ℕ) : Side → ℕ
  | .left => exponentBase s base .right + s.e
  | .right => exponentBase s base .right + s.e + s.config

/-- First address available to another module. The tag used to dispatch
among the header stages is at `base`, separate from the emitted mode tag. -/
def limit (s : Sizes) (base : ℕ) := configBase s base .right + s.config

theorem limit_eq (s : Sizes) (base : ℕ) :
    limit s base = base + 17 + 3*(s.h+2) + s.advice + 2*((s.h+1)*s.delta) + 2*s.e + 2*s.config := by
  simp [limit,configBase,exponentBase,exteriorBase,adviceBase,rightIndexBase,leftIndexBase,populationAddr,highAddr,indexBase,Sizes.capacity]
  omega

/-- The destination address of a copied incident payload, with a dummy zero address for padding
checks. -/
def dest (s : Sizes) (base : ℕ) (side : Side) : Field → ℕ
  | .exterior => exteriorBase s base side
  | .exponents => exponentBase s base side
  | .config => configBase s base side
  | .padding => 0

end LiveHeaderSchedule

end VPVNP
end Computability
end OAI
