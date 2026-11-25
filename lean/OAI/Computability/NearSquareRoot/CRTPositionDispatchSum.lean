import OAI.Computability.NearSquareRoot.CRTPositionNativeOp
import OAI.Computability.NearSquareRoot.CRTControlledSizes
import OAI.Computability.IntegerMultiplication.Strip.Steps
import OAI.Computability.IntegerMultiplication.Staff.Nat

/-! # Uniform branching on a finite position program opcode -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Adic IntegerMultiplication.Staff
open IntegerMultiplication.Strip IntegerMultiplication.Loom IntegerMultiplication.Packed

def OpFamily {T : Type} [Codec T] (ρ : ℝ) (wrap : T → Op) : Prop :=
  ∀ {X : Type} {R : Regime X} {l : X → ℕ} (k : X → ℕ) (q : X → T)
    (_ : Realizes R k) (_ : R.Has q) (_ : ∀ x, WellFormed (k x) (guardWidth (k x)) (wrap (q x)))
    {U : X → Type} (u : (x : X) → Series (U x)) (_ : ∀ x, (u x).count ≤ l x)
    (f : (x:X) → Block 2 (k x) → U x → Bead),
    let flat x := line 2 (k x)
    Breeze (Spindle.modes k (τ:=ρ)) R (fun x => (flat x).count) l
      (together R.header (cloth flat u f))
      (cloth flat u (fun x a => f x (nativeOp (k x) (guardWidth (k x)) (wrap (q x)) a)))

private def unpack {A B : Type} [Codec A] [Codec B] : A ⊕ B → Bool × Tree
  | .inl a => (false,send a)
  | .inr b => (true,send b)

/-- Decode the binary constructor from the actual header. On each fiber the same
second subtree is the selected operand, with the codec expected by that branch. -/
theorem opFamily_sum {A B : Type} [Codec A] [Codec B] {ρ : ℝ} (wrap : A ⊕ B → Op)
    (left : OpFamily ρ (wrap ∘ Sum.inl)) (right : OpFamily ρ (wrap ∘ Sum.inr)) :
    OpFamily ρ wrap := by
  intro X R l k q hk hq valid U u hu f
  let flat x := line 2 (k x)
  let L := {y : X × A // q y.1 = .inl y.2}
  let H := {y : X × B // q y.1 = .inr y.2}
  let lo (y:L) := y.val.1
  let hi (y:H) := y.val.1
  let src (y:L) := y.val.2
  let dst (y:H) := y.val.2
  let tag x := (unpack (q x)).1
  have encode (t : A ⊕ B) : send (unpack t) = send t := by cases t <;> rfl
  have both : R.Has (fun x => unpack (q x)) := by
    unfold Regime.Has
    simpa only [Function.comp_def,encode] using (show R.Small (send ∘ q) from hq)
  have read := both.ez Easy.fst
  have station := terminal (p:=2) (by decide) k hk
  have live := cloth_size flat u station f hu
  have select := Drive.small station.1 live read
  apply classify_b tag select hi lo
    (fun x => by
      cases e : q x with
      | inl a => exact ⟨fun _ => ⟨⟨(x,a),e⟩,rfl⟩,by simp [tag,e,unpack]⟩
      | inr b => exact ⟨by simp [tag,e,unpack],fun _ => ⟨⟨(x,b),e⟩,rfl⟩⟩)
  · have eq (y : L) : q (lo y) = Sum.inl (src y) := y.property
    have given : (R.pull lo).Has (fun y => q (lo y)) := Task.BT.map hq lo
    simp only [eq] at given
    have operand : (R.pull lo).Has (fun y => (false,src y)) := given
    have run := left (R:=R.pull lo) (k ∘ lo) src (Task.BT.map (show R.Has (tally ∘ k) from hk) lo)
      (operand.ez Easy.snd) (fun y => by simpa only [eq,Function.comp_apply] using valid (lo y))
      (fun y => u (lo y)) (fun y => hu (lo y)) (fun y => f (lo y))
    convert run using 1 <;> try rfl
    funext y
    simp only [Function.comp_apply,cloth,stackRun,eq]
  · have eq (y : H) : q (hi y) = Sum.inr (dst y) := y.property
    have given : (R.pull hi).Has (fun y => q (hi y)) := Task.BT.map hq hi
    simp only [eq] at given
    have operand : (R.pull hi).Has (fun y => (true,dst y)) := given
    have run := right (R:=R.pull hi) (k ∘ hi) dst (Task.BT.map (show R.Has (tally ∘ k) from hk) hi)
      (operand.ez Easy.snd) (fun y => by simpa only [eq,Function.comp_apply] using valid (hi y))
      (fun y => u (hi y)) (fun y => hu (hi y)) (fun y => f (hi y))
    convert run using 1 <;> try rfl
    funext y
    simp only [Function.comp_apply,cloth,stackRun,eq]

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
