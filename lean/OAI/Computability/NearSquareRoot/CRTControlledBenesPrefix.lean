import OAI.Computability.IntegerMultiplication.Curtain.Scanner

/-! # Reading the Boolean prefix in physical pin order

The P192 address markers list digits least significant first. The local program reverses
each marker and converts its binary digits to Booleans, retaining its full width.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic

/-- Read the outermost dimension first. On binary layouts this is the MSB-first address. -/
def pinBits : {s : Tape} → Pin s → List Bool
  | [], _ => []
  | _ :: _, (a,tail) => decide (a.val = 1) :: pinBits tail

@[simp] theorem pinBits_length {s : Tape} (a : Pin s) : (pinBits a).length = s.length := by
  induction s with
  | nil => rfl
  | cons d s ih => exact congrArg Nat.succ (ih (look a).2)

theorem pinBits_union (s t : Tape) (a : Pin s) (b : Pin t) :
    pinBits (Union s t (a,b)) = pinBits a ++ pinBits b := by
  induction s with
  | nil => rfl
  | cons d s ih => exact congrArg (decide ((look a).1.val = 1) :: ·) (ih (look a).2)

theorem pinBits_field {n : ℕ} (a : Block 2 n) : pinBits a = (most a).map Packed.title := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (decide ((look a).1.val = 1) :: pinBits (look a).2) =
      Packed.title (look a).1 :: (most (look a).2).map Packed.title
    rw [ih]
    have v (b : Fin 2) : decide (b.val = 1) = Packed.title b := by fin_cases b <;> decide
    rw [v]

@[simp] theorem field_replicate (p n : ℕ) : field p n = List.replicate n p := by
  induction n <;> simp_all [field, List.replicate_succ]

theorem fieldPrefixTrace {I : Type} {r : Regime I} (n : I → ℕ) (h : r.Has (tally ∘ n)) :
    Strip.Trace r (fun i => line 2 (n i)) (fun _ a => send (pinBits a)) := by
  have e : Easy (fun ds : Raw 2 => ds.reverse.map Packed.title) :=
    Easy.reverse.compose (Easy.finite Packed.title).mapping
  have z := Curtain.aims (fun i (a : Block 2 (n i)) => least a) (Curtain.issues n h) _ e.poly
  simpa only [pinBits_field, least, List.reverse_reverse] using z

/-- Stream every prefix from the single unary width descriptor at the P192 trace budget. -/
theorem prefixTrace {I : Type} {r : Regime I} (n : I → ℕ) (h : r.Has (tally ∘ n)) :
    Strip.Trace r (fun i => layout (List.replicate (n i) 2)) (fun _ a => send (pinBits a)) := by
  let traced (s : I → Tape) := Strip.Trace r (fun i => layout (s i)) (fun _ a => send (pinBits a))
  change traced (fun i => List.replicate (n i) 2)
  rw [← show (fun i => field 2 (n i)) = (fun i => List.replicate (n i) 2) from funext (fun i => field_replicate 2 (n i))]
  exact fieldPrefixTrace n h

/-- P192's track-to-block adoption reads a coordinate function in increasing wire order. -/
theorem pinBits_bolt {n : ℕ} (x : Fin n → Fin 2) :
    pinBits ((Earth.bolt n).cast x) = List.ofFn (fun i => Packed.title (x i)) := by
  rw [pinBits_field]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have h : i < n := by simpa using hj
    simp only [List.getElem_map, List.getElem_ofFn]
    exact congrArg Packed.title (congrFun (Earth.lightning x) ⟨i,h⟩)

/-- The same charged readout directly on a binary coordinate track. -/
theorem trackPrefixTrace {I : Type} {r : Regime I} (n : I → ℕ) (h : r.Has (tally ∘ n)) :
    Strip.Trace r (fun i => Earth.canon (n i)) (fun _ a => send (List.ofFn (fun j => Packed.title (a j)))) := by
  have q := (fieldPrefixTrace n h).via (fun i => Earth.bolt (n i))
  simpa only [Function.comp_def, pinBits_bolt] using q

end Benes

end NearSquareRoot
end Computability
end OAI
