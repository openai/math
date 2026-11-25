import OAI.Computability.NearSquareRoot.SynchronizedFixedWord
import OAI.Computability.NearSquareRoot.SynchronizedAxisProgram

/-! # Generation of the routed single-bit Walsh instruction stream

The generator expands each local instruction on its encoded unary fields and
replaces each internal-bit Walsh by a three-instruction routed call. The
resulting program includes both directions of each permutation and each
phase instruction needed for the adjoint transform.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.AxisWord

open IntegerMultiplication IntegerMultiplication.Code

private theorem adjoint_poly : Poly adj := by
  have hf : Poly flip := by
    unfold flip
    exact Easy.fst.poly.pair (Easy.snd.poly.fstCompose.pair (Easy.snd.poly.sndCompose.compose Iter.negate.poly))
  exact Easy.reverse.poly.compose (Poly.maps _ hf)

/-- Polynomial case analysis on a Boolean field of the input. -/
private theorem chooseBool {A B : Type} [Codec A] [Codec B] {b : A → Bool}
    {f g : A → B} (p : Poly b) (q : Poly f) (r : Poly g) :
    Poly (fun x => if b x then f x else g x) := by
  simpa only [Bool.cond_eq_ite] using p.choose q r

private theorem chooseTest {A B : Type} [Codec A] [Codec B] {p : A → Prop}
    [DecidablePred p] {f g : A → B} (test : Poly (fun x => decide (p x)))
    (q : Poly f) (r : Poly g) : Poly (fun x => if p x then f x else g x) := by
  simpa using chooseBool test q r

private theorem tag_test (tag : ℕ) : Poly (fun x : Inst => decide (x.1.length = tag)) := by
  have fstTag : Poly (fun x : Inst => x.1) := Easy.fst.poly
  have h := fstTag.pair (Code.Poly.const (tally tag))
  simpa only [tally_length] using h.compose (Iter.linked (X := Unit) (Y := Unit)).poly

private theorem instruction_poly (t : ℕ) : Poly (fun arg : Tally => inst t arg) := by unfold inst; fun_prop

private theorem cons_poly {A B : Type} [Codec A] [Codec B] {f : A → B} {g : A → List B}
    (hf : Poly f) (hg : Poly g) : Poly (fun x => f x :: g x) :=
  (hf.pair hg).compose Poly.cons

private theorem threeRounds_poly (t p : ℕ) : Poly (threeRounds t p) := by
  unfold threeRounds
  repeat apply cons_poly (instruction_poly _)
  exact Code.Poly.const []

private theorem oriented_poly {f : Inst → List Inst} (hf : Poly f) :
    Poly (fun i : Inst => if i.2.2 then adj (f i) else f i) :=
  chooseBool Easy.snd.poly.sndCompose (hf.compose adjoint_poly) hf

private theorem lowerInst_poly : Poly lowerInst := by
  unfold lowerInst
  apply chooseTest (tag_test 2)
  · exact oriented_poly (Easy.snd.poly.fstCompose.compose (threeRounds_poly 14 15))
  · apply chooseTest (tag_test 3)
    · exact oriented_poly (Easy.snd.poly.fstCompose.compose (threeRounds_poly 10 11))
    · exact cons_poly Poly.identity (Code.Poly.const [])

theorem loweredRestored_poly : Poly loweredRestored := by
  unfold loweredRestored lower
  simp_rw [List.flatMap_def]
  exact (restored_poly.compose (Poly.maps _ lowerInst_poly)).compose Easy.flatten.poly

private theorem route_template : Poly (fun i : Tally × Inst =>
    [inst 18 i.2.2.1, inst 10, inst 18 i.2.2.1]) := by
  have h : Poly (fun i : Tally × Inst => inst 18 i.2.2.1) :=
    Easy.snd.poly.sndCompose.fstCompose.compose (instruction_poly 18)
  exact cons_poly h (cons_poly (Code.Poly.const _) (cons_poly h (Code.Poly.const [])))

private theorem fixedInst_poly : Poly (fun p : Tally × Inst => fixedInst p.1 p.2) := by
  have argTest : Poly (fun p : Tally × Inst => decide (p.2.2.1.length < p.1.length)) :=
    (Easy.snd.poly.sndCompose.fstCompose.pair Easy.fst.poly).compose Iter.small_easy.poly
  unfold fixedInst
  apply chooseTest (p := fun (p : Tally × Inst) => p.2.1.length = 14) (Easy.snd.poly.compose (tag_test 14))
  · apply chooseTest argTest
    · exact chooseBool Easy.snd.poly.sndCompose.sndCompose (route_template.compose adjoint_poly) route_template
    · exact Code.Poly.const []
  · exact cons_poly Easy.snd.poly (Code.Poly.const [])

/-- Stack program generating the exact final singleton-bit layout from the unary exponent. -/
theorem fixedWord_poly : Poly fixedWord := by
  unfold fixedWord
  simp_rw [List.flatMap_def]
  exact ((Poly.identity.pair loweredRestored_poly).compose
    (Poly.push ([] : Tally) (inst 0) fixedInst_poly)).compose Easy.flatten.poly

private theorem unary_size : Dom id (fun k : ℕ => size (tally k)) :=
  ⟨1, 2, fun k => by simp [size_tally]⟩

theorem fixedWord_task :
    Task.BT id (fun k : ℕ => send (tally k)) (fun k => send (fixedWord (tally k))) :=
  fixedWord_poly.on unary_size

/-- A fixed deterministic multitape machine produces the spelling of the entire
routed short-transform program within polynomially many actual steps and cells. -/
theorem fixedWord_machine :
    PolyTreeMachine id (fun k : ℕ => send (tally k)) (fun k => send (fixedWord (tally k))) :=
  polyTreeMachine_of_BT fixedWord_task unary_size

private theorem flatMap_length_le {A B : Type*} (f : A → List B) (c : ℕ)
    (hf : ∀ x, (f x).length ≤ c) (l : List A) : (l.flatMap f).length ≤ c * l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ]
    have := hf x
    omega

theorem loweredRestored_length_le (k : Tally) :
    (loweredRestored k).length ≤ 6 * (1032 * k.length + 1549) := by
  rw [← restored_length]
  apply flatMap_length_le
  intro x
  unfold lowerInst
  split_ifs <;> simp [threeRounds, adj]

theorem fixedWord_length_le (k : Tally) :
    (fixedWord k).length ≤ 18 * (1032 * k.length + 1549) := by
  have h : (fixedWord k).length ≤ 3 * (loweredRestored k).length := by
    apply flatMap_length_le
    intro x
    unfold fixedInst
    split_ifs <;> simp [adj]
  exact h.trans (by have := loweredRestored_length_le k; omega)

end ShortFourier.AxisWord

end NearSquareRoot
end Computability
end OAI
