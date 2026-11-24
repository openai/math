import OAI.Computability.VPVNP.MacaulayReadArms
import OAI.Computability.VPVNP.AffinePinCoefficient

/-! # Calling the affine pin routine on the decoded Macaulay row

The positive-divisibility branch takes its exponent buffer from the equation
scan. It copies the decoded pin index, reads the pin table, and returns the
field scalar directly on the matrix reader's result port.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.MacaulayRead.Arms.Pin

open RAMTape BurstRAM SliceArithmetic MacaulayRowDispatch
open RadicalCertificate.MonomialIndex

set_option synthInstance.maxSize 2500

variable {K : Type}

private abbrev binary : AffinePin.Query.Port := .inl .binary
private abbrev residual : AffinePin.Query.Port := .inl .exponents
private abbrev result : AffinePin.Query.Port := .inl .value

/-- Route the affine query's exponent input to the equation scan's packed residuals and its
scalar output to the reader result. The other query ports use the embedded payload. -/
def mount (inc : AffinePin.Query.Port ↪ K) (q : AffinePin.Query.Port) : Ports K :=
  if q = residual then slot false (.external .packed)
  else if q = result then .result else extra (.payload (inc q))

theorem mount_injective (inc : AffinePin.Query.Port ↪ K) : Function.Injective (mount inc) := by
  intro a b h
  by_cases ha : a = residual <;> by_cases hb : b = residual <;>
    by_cases ha' : a = result <;> by_cases hb' : b = result <;>
      simp_all [mount, slot, extra]

/-- Copy the decoded pin index to the affine query's binary input, then run the query on the
reader's ports. -/
def machine (inc : AffinePin.Query.Port ↪ K) : FiniteRoutine (Ports K) :=
  (SuccessorFields.prependCopy (route (.reg (outReg 1))) (mount inc binary) (extra .temp)).followedBy
    (AffinePin.Query.machine.onPorts (mount inc))

/-- The embedded payload ports contain the initial affine query frame for the given pin advice,
extension modulus and scalar word width. -/
def Preloaded {p e : ℕ} (inc : AffinePin.Query.Port ↪ K) (A : AffinePin.Stage.Advice)
    (c : Vector p e) (v : ℕ) (payload : Stacks K) : Prop :=
  ∀ q, payload (inc q) = AffinePin.Query.frame A c v {} q

/-- Install the initial affine query frame at the embedded payload ports of the given stack
bank. -/
noncomputable def preload {p e : ℕ} (inc : AffinePin.Query.Port ↪ K) (A : AffinePin.Stage.Advice)
    (c : Vector p e) (v : ℕ) (base : Stacks K) : Stacks K :=
  installStacks inc base (AffinePin.Query.frame A c v {})

theorem preload_correct {p e : ℕ} (inc : AffinePin.Query.Port ↪ K) (A : AffinePin.Stage.Advice)
    (c : Vector p e) (v : ℕ) (base : Stacks K) : Preloaded inc A c v (preload inc A c v base) :=
  installStacks_at inc.injective base _

private theorem unpack {p e w : ℕ} (inc : AffinePin.Query.Port ↪ K) (A : AffinePin.Stage.Advice)
    (c : Vector p e) (v : ℕ) (aux : Stacks K) (h : Preloaded inc A c v aux)
    (rs : Reg → Word w) (data : Bool → PairCall.Inputs) (packed flag constants : Bool → List Bool)
    (res : List Bool) (q : AffinePin.Query.Port) :
    frame rs res (storage w data packed flag constants aux) (mount inc q) =
      AffinePin.Query.frame A c v {exponents := packed false, value := res} q := by
  rcases q with q | q
  · cases q <;> first | rfl | exact h _
  · exact h _

private theorem set_result [DecidableEq K] {w : ℕ} (rs : Reg → Word w) (s : Stacks (Leaf K))
    (old new : List Bool) : Function.update (frame rs old s) .result new = frame rs new s := by
  funext z; cases z <;> rfl

private theorem set_residual [DecidableEq K] {w : ℕ} (rs : Reg → Word w) (res : List Bool)
    (data : Bool → PairCall.Inputs) (pack flag constants : Bool → List Bool) (aux : Stacks K) :
    Function.update (frame rs res (storage w data pack flag constants aux)) (slot false (.external .packed)) [] =
      frame rs res (storage w data (Function.update pack false []) flag constants aux) := by
  funext z
  cases z with
  | row | col | result => rfl
  | aux z =>
    rcases z with q | z
    · cases q <;> rfl
    rcases z with ⟨b,q⟩ | j
    · cases b <;> cases q with
      | external f => cases f <;> rfl
      | internal | scratch => rfl
    · cases j <;> rfl

/-- Tick bound for copying a width-`w` pin index and looking up its affine coefficient. -/
def cost (t e w v : ℕ) := 5*w+2 + AffinePin.Query.cost t e w v

/-- One positive-divisibility affine call. The row decoder's register,
the flag, the powered scan and the immutable advice survive the call. -/
theorem bounded [DecidableEq K] {p e t w v S : ℕ} [Fact p.Prime] [NeZero e] {c : Vector p e}
    (inc : AffinePin.Query.Port ↪ K) (hw : 0<w) (hv : SliceArithmetic.Word.workingWidth p ≤ v)
    (pins : Finset (Fin t)) (a : Fin t → Scalar c) (i : Fin t) (d : Fin t →₀ ℕ)
    (hd : ∀ j, d j < 2^w) (rs : Reg → BurstRAM.Word w) (hi : (rs (outReg 1)).val = i.val)
    (data : Bool → PairCall.Inputs) (pack flag constants : Bool → List Bool) (aux : Stacks K)
    (hpack : pack false = ExponentPack.packed w (List.ofFn (fun j => d j)))
    (hp : Preloaded inc (AffinePin.Query.advice w v pins a) c v aux)
    (hS : AffinePin.Query.space t e w v ≤ S)
    (room : ∀ z, ((frame rs [] (storage w data pack flag constants aux)) z).length + (5*w+2) ≤ S) :
    let ans : Scalar c := if i∈pins then (if d=0 then -a i else if d=Finsupp.single i 1 then 1 else 0) else 0
    ∃ steps ≤ cost t e w v, (machine inc).BoundedRun S steps (frame rs [] (storage w data pack flag constants aux))
      (frame rs (Engine.scalar v ans) (storage w data (Function.update pack false []) flag constants aux)) := by
  let A := AffinePin.Query.advice w v pins a
  let start := frame rs [] (storage w data pack flag constants aux)
  let digit := UniversalCountStack.digits w i.val
  let mid := Function.update start (mount inc binary) digit
  let ans : Scalar c := if i∈pins then (if d=0 then -a i else if d=Finsupp.single i 1 then 1 else 0) else 0
  let finish := frame rs (Engine.scalar v ans) (storage w data (Function.update pack false []) flag constants aux)
  have hwI : i.val < 2^w := hi ▸ (rs (outReg 1)).isLt
  have hr : start (route (.reg (outReg 1))) = digit := by
    rw [show start (route (.reg (outReg 1))) = wordBits (rs (outReg 1)) from frame_route ..]
    apply congrArg wordBits
    exact Fin.ext (hi.trans (Nat.mod_eq_of_lt hwI).symm)
  have hsrc : (route (.reg (outReg 1)) : Ports K) = .aux (.inl (.reg (outReg 1))) := by
    simp [route, inReg, outReg, Dispatch.Code.inReg, Dispatch.Code.outReg]
  have hbin : start (mount inc binary) = [] := hp binary
  have copy := SuccessorFields.prependCopy_runs (route (.reg (outReg 1))) (mount inc binary) (extra .temp)
    (by rw [hsrc]; intro h; cases h) (by rw [hsrc]; intro h; cases h) (by intro h; cases h) start rfl
  rw [hr, hbin, List.append_nil, UniversalCountStack.length_digits] at copy
  have hb : (SuccessorFields.prependCopy (route (.reg (outReg 1))) (mount inc binary) (extra .temp)).BoundedRun S (5*w+2) start mid := UniversalCountStack.spaceRun_of_steps copy room
  obtain ⟨n,hn,run⟩ := AffinePin.Query.bounded hw hv pins a i hwI d hd
  have call : (AffinePin.Query.machine.onPorts (mount inc)).BoundedRun S n mid finish := by
    apply (run.enlarge hS).framed (mount_injective inc) hb.final_cap
    · intro q
      by_cases h : q = binary
      · subst q; exact Function.update_self ..
      · rw [show mid (mount inc q) = start (mount inc q) from Function.update_of_ne (fun e => h (mount_injective inc e)) ..]
        rw [show start = frame rs [] (storage w data pack flag constants aux) from rfl,
          unpack inc A c v aux hp rs data pack flag constants [] q, hpack]
        rcases q with q | q
        · cases q <;> first | rfl | exact (h rfl).elim
        · rfl
    · intro q
      have hu := unpack inc A c v aux hp rs data (Function.update pack false []) flag constants (Engine.scalar v ans) q
      simpa only [Function.update_self] using hu
    · intro z hz
      have hh : finish = Function.update (Function.update start .result (Engine.scalar v ans))
          (slot false (.external .packed)) [] := by rw [set_result, set_residual]
      have hres : z ≠ slot false (.external .packed) := (hz residual).symm
      have hout : z ≠ .result := (hz result).symm
      rw [hh, Function.update_of_ne hres, Function.update_of_ne hout]
      exact (Function.update_of_ne (fun e => hz binary e.symm) ..).symm
  exact ⟨_, Nat.add_le_add_left hn _, hb.followedBy call⟩

/-- The same bus call returns the coefficient of the field polynomial used
in the Macaulay row, in the rank engine's power-basis representation. -/
theorem coefficient [DecidableEq K] {p e t w v S : ℕ} [Fact p.Prime] [NeZero e] {c : Vector p e}
    {F ι : Type*} [Field F] [Algebra (ZMod p) F] (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] F)
    (system : ι → MvPolynomial (Fin t) F) (inc : AffinePin.Query.Port ↪ K)
    (hw : 0<w) (hv : SliceArithmetic.Word.workingWidth p ≤ v)
    (pins : Finset (Fin t)) (a : Fin t → F) (i : Fin t) (d : Fin t →₀ ℕ) (hd : ∀ j, d j < 2^w)
    (rs : Reg → BurstRAM.Word w) (hi : (rs (outReg 1)).val = i.val)
    (data : Bool → PairCall.Inputs) (pack flag constants : Bool → List Bool) (aux : Stacks K)
    (hpack : pack false = ExponentPack.packed w (List.ofFn (fun j => d j)))
    (hp : Preloaded inc (AffinePin.Query.advice w v pins (fun j => AffinePin.Query.encode φ (a j))) c v aux)
    (hS : AffinePin.Query.space t e w v ≤ S)
    (room : ∀ z, ((frame rs [] (storage w data pack flag constants aux)) z).length + (5*w+2) ≤ S) :
    let ans := AffinePin.Query.encode φ ((SliceGeometry.pinnedEquations system pins a (.inr i)).coeff d)
    ∃ steps ≤ cost t e w v, (machine inc).BoundedRun S steps (frame rs [] (storage w data pack flag constants aux))
      (frame rs (Engine.scalar v ans) (storage w data (Function.update pack false []) flag constants aux)) := by
  dsimp only
  rw [← AffinePin.Query.encode_pin φ system pins a i d]
  exact bounded inc hw hv pins (fun j => AffinePin.Query.encode φ (a j)) i d hd rs hi data pack flag constants
    aux hpack hp hS room

end RankQuery.Stack.MacaulayRead.Arms.Pin

end VPVNP
end Computability
end OAI
