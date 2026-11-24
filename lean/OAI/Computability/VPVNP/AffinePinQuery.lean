import OAI.Computability.VPVNP.AffinePinStage
import OAI.Computability.VPVNP.AffinePinScalar
import OAI.Computability.VPVNP.RoutineSpace

/-!
# Fixed bit-stack program for affine pin coefficients

The immutable pin mask and table are independent of the row and queried
monomial. The program computes three offsets from the live row index,
classifies the packed exponent, selects the pin, and performs the scalar
operation in the advised power basis.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace AffinePin.Query

open RAMTape SliceArithmetic RankQuery.Stack RadicalCertificate.MonomialIndex
open UniversalCountStack (digits)

/-- The combined ports for classifying a queried monomial, reading its pin data, and computing
the field coefficient. -/
abbrev Port := Stage.Port ⊕ AddCall.Port

private def outputPorts : Output.Port → Port
  | .inl (.inr .acc) => .inl .value
  | .inl j => .inr j
  | .inr .active => .inl .active
  | .inr .constant => .inl .constant
  | .inr .unit => .inl .unit
  | .inr .right => .inl .high
  | .inr .tmp => .inl .tmp

/-- Select the coordinate’s mask bit and field value, classify the requested exponent, and
compute the coefficient of its affine pin equation. -/
def machine : FiniteRoutine Port :=
  (Stage.machine.onPorts Sum.inl).followedBy (Output.machine.onPorts outputPorts)

variable {p e t : ℕ} {c : Vector p e}

/-- The coordinate-ordered bit vector indicating which variables are pinned. -/
def mask (pins : Finset (Fin t)) : List Bool := List.ofFn (fun i => decide (i∈pins))

/-- Concatenate the pinned-value table in coordinate order, encoding every field element in
limbs of `v` bits. -/
def values (v : ℕ) (a : Fin t → Scalar c) : List Bool := Blocks.table fun j => Engine.scalar v (a j)

/-- The fixed exponent width, scalar width, pin mask, and packed field-value table used for
every monomial query of this slice. -/
def advice (w v : ℕ) (pins : Finset (Fin t)) (a : Fin t → Scalar c) : Stage.Advice :=
  ⟨w, e*v, mask pins, values v a⟩

/-- Combine the pin advice and current lookup state with a clean field-arithmetic bank
containing the packed extension modulus. -/
def frame (A : Stage.Advice) (c : Vector p e) (v : ℕ) (s : Stage.Work) : Stacks Port :=
  Sum.elim (Stage.frame A s) (AddCall.clean (MultiplyCall.external p e v (SliceArithmeticRound.packed v (List.ofFn c)) [] []))

theorem mask_length (pins : Finset (Fin t)) : (mask pins).length = t := List.length_ofFn

theorem values_length (v : ℕ) (a : Fin t → Scalar c) : (values v a).length = t*(e*v) :=
  Blocks.length _ _ (fun j => by simp [Engine.scalar])

theorem extra_length (v : ℕ) (pins : Finset (Fin t)) (a : Fin t → Scalar c) :
    (mask pins ++ values v a).length = t + t*(e*v) := by rw [List.length_append, mask_length, values_length]

private theorem mask_cell (pins : Finset (Fin t)) (i : Fin t) :
    ((mask pins).drop i.val).take 1 = [decide (i∈pins)] := by
  have hl : i.val < (mask pins).length := (mask_length pins).symm ▸ i.isLt
  rw [List.drop_eq_getElem_cons hl]
  simp [mask]

private theorem values_cell (v : ℕ) (a : Fin t → Scalar c) (i : Fin t) :
    ((values v a).drop (i.val*(e*v))).take (e*v) = Engine.scalar v (a i) :=
  Blocks.cell _ _ (fun _ => by simp [Engine.scalar]) i

/-- Uniform step bound over the `t` coordinate rows for decoding an index, scanning the
exponents, reading the pin table, and returning a scalar. -/
def cost (t e w v : ℕ) := Stage.cost w t w (e*v) (t*w) + Output.cost e v

private theorem cost_le {i t e w v : ℕ} (hi : i ≤ t) :
    Stage.cost w i w (e*v) (t*w) + Output.cost e v ≤ cost t e w v := by
  unfold cost Stage.cost Reader.cost EvaluatorDigitLookup.lookupTicks
  gcongr

variable [Fact p.Prime] [NeZero e]

/-- Return the canonical scalar for the indexed row and queried exponent.
All temporary stacks are clean at the return. -/
theorem machine_runs {w v : ℕ} (hw : 0<w) (hv : Word.workingWidth p ≤ v)
    (pins : Finset (Fin t)) (a : Fin t → Scalar c) (i : Fin t) (hi : i.val<2^w)
    (d : Fin t →₀ ℕ) (hd : ∀ j, d j < 2^w) :
    let A := advice w v pins a
    let entry : Stage.Work := {binary := digits w i.val, exponents := ExponentPack.packed w (List.ofFn (fun j => d j))}
    let ans : Scalar c := if i∈pins then (if d=0 then -a i else if d=Finsupp.single i 1 then 1 else 0) else 0
    ∃ steps ≤ cost t e w v, machine.Runs steps (frame A c v entry) (frame A c v {value := Engine.scalar v ans}) := by
  dsimp only
  let A := advice w v pins a
  let entry : Stage.Work := {binary := digits w i.val, exponents := ExponentPack.packed w (List.ofFn (fun j => d j))}
  let act := decide (i∈pins)
  let zero := decide (d=0)
  let unit := decide (d=Finsupp.single i 1)
  let got : Stage.Work := {active := [act], constant := [zero], unit := [unit], value := Engine.scalar v (a i)}
  let ans := Output.result (a i) act zero unit
  let final : Stage.Work := {value := Engine.scalar v ans}
  obtain ⟨pre,b,post,hp,hl,_,hz,hu⟩ := Blocks.split_packed w hw i d hd
  have hm : i.val+1 ≤ A.mask.length := (mask_length pins).symm ▸ i.isLt
  have hval : i.val*A.scalarWidth+A.scalarWidth ≤ A.values.length := by
    change i.val*(e*v)+e*v ≤ (values v a).length
    rw [values_length, ← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ i.isLt
  obtain ⟨k,hk,run⟩ := Stage.machine_runs A (digits w i.val) pre b post i.val
    (by rw [UniversalCountStack.value_digits, Nat.mod_eq_of_lt hi]) hl hm hval
  have len : (ExponentPack.packed w (List.ofFn (fun j => d j))).length = t*w := by
    rw [Blocks.exponent_table]; exact Blocks.length _ _ (fun _ => UniversalCountStack.length_digits ..)
  rw [← hp, len, UniversalCountStack.length_digits] at hk
  have mcell : (A.mask.drop i.val).take 1 = [act] := mask_cell pins i
  have vcell : (A.values.drop (i.val*A.scalarWidth)).take A.scalarWidth = Engine.scalar v (a i) := values_cell v a i
  simp only [← hp, mcell, vcell, hz, hu] at run
  have stage : (Stage.machine.onPorts (Sum.inl : Stage.Port → Port)).Runs k (frame A c v entry)
      (frame A c v got) := by
    apply FiniteRoutine.runs_onPorts_framed _ Sum.inl_injective run (fun _ => rfl) (fun _ => rfl)
    rintro (j | j) hj
    · exact (hj j rfl).elim
    · rfl
  obtain ⟨l,hh,out⟩ := Output.machine_runs hv (a i) act zero unit
  have write : (Output.machine.onPorts outputPorts).Runs l (frame A c v got) (frame A c v final) := by
    apply FiniteRoutine.runs_onPorts_framed _ (by decide) out
    · rintro ((j | j) | j) <;> first | cases j <;> rfl
    · rintro ((j | j) | j) <;> first | cases j <;> rfl
    · rintro (j | j) hj
      · cases j <;> first | rfl | exact (hj (.inl (.inr .acc)) rfl).elim | exact (hj (.inr .active) rfl).elim | exact (hj (.inr .constant) rfl).elim | exact (hj (.inr .unit) rfl).elim
      · rfl
  have heq : ans = if i∈pins then (if d=0 then -a i else if d=Finsupp.single i 1 then 1 else 0) else 0 := by
    by_cases h : i∈pins <;> by_cases z : d=0 <;> by_cases u : d=Finsupp.single i 1 <;>
      simp [ans, Output.result, act, zero, unit, h, z, u]
  refine ⟨k+l, (Nat.add_le_add hk hh).trans (cost_le i.isLt.le), ?_⟩
  rw [← heq]
  exact stage.followedBy write

end AffinePin.Query

end VPVNP
end Computability
end OAI
