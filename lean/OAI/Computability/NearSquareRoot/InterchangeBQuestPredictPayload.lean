import OAI.Computability.NearSquareRoot.InterchangePredictRun
import OAI.Computability.NearSquareRoot.InterchangeBQuestTemplate
import OAI.Computability.NearSquareRoot.InterchangeBQuestAddress
import OAI.Computability.NearSquareRoot.InterchangeCompiledPivot
import OAI.Computability.NearSquareRoot.InterchangePayloadStage
import OAI.Computability.NearSquareRoot.InterchangeSpectralFibre

/-!
# Bounded execution of a packed predictor

The fixed address frame supplies the programs for every route. The
local scan and all parked input and output banks are charged against
the parent mass. Each child retains its packed alphabet and outer tapes.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace Interchange.RepairSchedule

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Loom InterchangeAddress InterchangePayloadBank StageRoute StageScript
  SwapRepair Support RectangleAtlas

variable {U L B H K : Type} [Field K] [Finite K] [Fintype L] [Nonempty L] [DecidableEq L]
  [Fintype B] [Fintype H] {m b a : ℕ} [NeZero b] {rect : B → Rectangle L}
  {A : RectangleAtlas rect a} {D : U → Type} {ρ : Regime U} {l : U → ℕ}

theorem execute_predict_payload_bounded (F : Frame A m b) (I J : H → L)
    (mid : Matrix H H K) (e : Environment K m)
    (P G S : U → Tape) (f : U → ℕ) (hb : 2 ≤ b) (hf : ρ.Has (tally ∘ f))
    (hP : Told ρ P) (hG : Told ρ G) (hS : Told ρ S)
    (payload : (i : U) → Series (D i)) (hd : ∀ i, (payload i).count ≤ l i)
    (digit : K → Tree) (hj : Function.Injective digit)
    (lanes : Series (PackedPencil.Index m)) (labels : Series L)
    (x : (i : U) → Data K L (domain (J:=Fin (a+m+a)) (b:=b) P G S f i × D i) (width m) m) :
    let ord := Equiv.refl (Fin (a+m+a))
    let records := layoutRows (b:=b) ord P G S f
    let price := fun u : Move rect (Fin m) I J => (A.routeWord u).price
    let lay i := InterchangeSpectralFibre.withPayload (D i) (extendLayout (P i) (G i) (S i) (F.layout (f i)))
    let output := fun i => predict rect I J mid e (lay i) (x i)
    BChargedTyped (r:=ρ) (l:=l) (b:=b) ord P G S f (Good payload digit)
      (order m * (moveCharges (PackedPencil.Index m) price).count)
      (render records payload (lanes.cart labels) digit (streams x))
      (render records payload (lanes.cart labels) digit (streams output)) := by
  intro ord records price lay output
  let θ i := (extendLayout (P i) (G i) (S i) (F.layout (f i))).perm (I:=I) (J:=J)
  let prog := PackedPencil.program rect I J mid e
  let v (i : U) (w : L) (k : domain (J:=Fin (a+m+a)) (b:=b) P G S f i × D i)
      (t : PackedPencil.Index m) := components K m (x i w t.1 k) t.2
  have hw : 0 < width m := by
    simp only [width, OAI.LinearAlgebra.FiniteFourier.primePredictorRows, OAI.LinearAlgebra.FiniteFourier.countPencilOrder]
    positivity
  let : Nonempty (PackedPencil.Index m) := ⟨⟨⟨0,hw⟩,⟨0,pow_pos (by decide) _⟩⟩⟩
  choose ops legal spec using fun u : Move rect (Fin m) I J => F.native_move u
  have single u y hy good := (execute_bounded_typed (r:=ρ) (l:=l) ord P G S f (Good payload digit)
    hb hf hP hG hS (ops u) (legal u) y hy good).monotone (show (_ : ℤ) ≤ (price u : ℤ) by
      exact_mod_cast (spec u).1)
  have acts (u : Move rect (Fin m) I J) (i : U) :
      recreation ord (P i) (G i) (S i) (f i) (ops u) (legal u) = θ i u := (spec u).2 ..
  simp_rw [acts] at single
  have ret := InterchangeSpace.run_packed records (layoutRows_station ord P G S f hb hf hP hG hS)
    payload hd digit hj 0 θ price single (repeatProgram prog (order m)) lanes labels labels v
  have hc : Fintype.card (PackedPencil.Index m) * cost price (repeatProgram prog (order m)) =
      order m * (moveCharges (PackedPencil.Index m) price).count := by
    rw [cost_repeatProgram, Nat.mul_left_comm]
    congr 1
    exact scalar_stage_cost (PackedPencil.Index m) mid _ _ price
      (A.routeWord_price_idle I J) (A.routeWord_price_align I J) (A.routeWord_price_unalign I J)
  rw [hc] at ret
  have hperm (i : U) : (lay i).perm (I:=I) (J:=J) = InterchangePayloadBank.withPayload D θ i :=
    funext (InterchangeSpectralFibre.withPayload_perm (D i) _)
  have hout : streams output = fun i (t : PackedPencil.Index m × L) k =>
      eval (InterchangePayloadBank.withPayload D θ i) (repeatProgram prog (order m)) (v i) t.2 k t.1 := by
    funext i t k
    rcases t with ⟨⟨u,d⟩,w⟩
    dsimp only [output, streams, predict]
    rw [LinearEquiv.apply_symm_apply, hperm, eval_repeatProgram]
  rw [hout]
  exact ret

end Interchange.RepairSchedule

end

end NearSquareRoot
end Computability
end OAI
