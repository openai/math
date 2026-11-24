import OAI.Computability.VPVNP.CursorRouteChecker
import OAI.Computability.VPVNP.CursorFieldOffsets

/-!
# Executing an initial cursor vertex

The checker receives four contiguous bit vectors, the two outgoing and the
two incoming fields of its own vertex. It executes the local route tests
and runs the private site validator only at cursor zero. Its accepted bit
strings are exactly the initial choices used in the monomial path sum.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CursorNetwork

open CursorRouting RAMLayout BurstRAM BurstRAM.PrivateRAM

variable {D H w p r k e : ℕ} [NeZero D]

/-- Four contiguous vectors of arc bits, addressed within one vertex. -/
abbrev Buffers (D H w : ℕ) := LocalPort → Fin (ramPayloadWidth D H w) → Bool

/-- Read one routing operand at its precomputed field offset. -/
def readBuffer (buf : Buffers D H w) (a : LocalAddress D H w) : Bool :=
  buf a.port (ramFieldOffset D H w ⟨a.system, a.bit⟩)

/-- Serialize the four independent half-wire vectors supplied at a vertex. -/
def halfBuffers (v : Position D) (z : (network D (ramFieldBits H w : RAMSystem D → ℕ)).Half v) :
    Buffers D H w
  | .outgoing side => ramPayloadEquiv D H w (out v z side)
  | .incoming side => ramPayloadEquiv D H w (inc v z side)

theorem readBuffer_halfBuffers (v : Position D)
    (z : (network D (ramFieldBits H w : RAMSystem D → ℕ)).Half v) :
    readBuffer (halfBuffers v z) = readHalf v z := by
  funext a
  rcases a with ⟨port,s,j⟩
  cases port <;> simp [readBuffer, halfBuffers, readHalf]

/-- Decode the validator input by addressing the selected arc at each
successor or sorting slot. -/
def incidentBuffer (v : Position D) (buf : Buffers D H w) : Fin (width D H w) → Bool :=
  decodeIncident v.2
    (fun s j ↦ readBuffer buf ⟨.outgoing ((systemMask s).val.testBit v.1.val), s, j⟩)
    (fun s j ↦ readBuffer buf
      ⟨.incoming ((systemMask s).val.testBit ((finRotate D).symm v.1).val), s, j⟩)

theorem incidentBuffer_halfBuffers (v : Position D)
    (z : (network D (ramFieldBits H w : RAMSystem D → ℕ)).Half v) :
    incidentBuffer v (halfBuffers v z) =
      decodeIncident v.2 (sent systemMask v z) (received systemMask v z) := by
  unfold incidentBuffer
  rw [readBuffer_halfBuffers]
  rfl

/-- Boolean acceptance on independently supplied half-wire indices. A valid
transit vertex consumes no private bits. -/
def initialAccept (M : Machine w p r k) (fuel : ℕ) (initial header : Word w)
    (hw : 2 ≤ w) (hc : 2 ^ D * 2 ^ e < 2 ^ w) (v : Position D)
    (buf : Buffers D (2 ^ e) w) (choices : List Bool) : Bool :=
  routeAccept (2 ^ e) w v (readBuffer buf) &&
    (if v.1 = 0 then
      (M.validateIncident fuel initial header hw hc v.2 (incidentBuffer v buf) choices).1.isSome
    else choices.isEmpty)

private def rejectEquiv {f : List Bool → Bool} (h : ∀ bs, f bs = false) :
    {bs // f bs = true} ≃ Empty where
  toFun b := False.elim (by have := b.prop; simp [h] at this)
  invFun := Empty.elim
  left_inv b := False.elim (by have := b.prop; simp [h] at this)
  right_inv e := e.elim

private def transitEquiv {f : List Bool → Bool} (h : ∀ bs, f bs = true ↔ bs = []) :
    {bs // f bs = true} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], (h []).mpr rfl⟩
  left_inv b := Subtype.ext ((h _).mp b.prop).symm
  right_inv _ := rfl

/-- Acceptance on the serialized local buffers preserves the original
private path itself. It gives the singleton empty string at a valid transit
vertex and no strings at vertices failing a route or clamp check. -/
noncomputable def initialAcceptEquiv (M : Machine w p r k) (fuel : ℕ) (initial : Word w)
    (header : ℕ → Word w) (hw : 2 ≤ w) (hc : 2 ^ D * 2 ^ e < 2 ^ w)
    (v : Position D) (z : (validatorNetwork D e w).Half v) :
    {bs // initialAccept M fuel initial (header v.2) hw hc v (halfBuffers v z) bs = true} ≃
      initialChoices M fuel initial header hw hc v z := by
  classical
  let passed := routeAccept (2 ^ e) w v (readBuffer (halfBuffers v z))
  have ok : passed = true ↔ Checks systemMask v z ∧
      (v.1 = 0 → ActiveSends v.2 (sent systemMask v z)) := by
    rw [show passed = routeAccept (2 ^ e) w v (readHalf v z) by
      simp [passed, readBuffer_halfBuffers]]
    exact routeAccept_readHalf v z
  unfold initialChoices
  split_ifs with hcheck hzero hactive
  · apply Equiv.subtypeEquivRight
    intro bs
    have hp := ok.mpr ⟨hcheck, fun _ ↦ hactive⟩
    unfold passed at hp
    simp only [initialAccept, hp, Bool.true_and, hzero, ↓reduceIte, incidentBuffer_halfBuffers]
  · apply rejectEquiv
    have hp : passed = false := Bool.eq_false_iff.mpr fun h ↦ hactive ((ok.mp h).2 hzero)
    intro bs
    unfold passed at hp
    simp only [initialAccept, hp, Bool.false_and]
  · apply transitEquiv
    have hp := ok.mpr ⟨hcheck, fun h ↦ (hzero h).elim⟩
    intro bs
    unfold passed at hp
    simp [initialAccept, hp, hzero]
  · apply rejectEquiv
    have hp : passed = false := Bool.eq_false_iff.mpr fun h ↦ hcheck (ok.mp h).1
    intro bs
    unfold passed at hp
    simp only [initialAccept, hp, Bool.false_and]

end CursorNetwork

end VPVNP
end Computability
end OAI
