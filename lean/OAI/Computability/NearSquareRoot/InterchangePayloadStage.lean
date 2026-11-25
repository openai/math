import OAI.Computability.NearSquareRoot.InterchangePayloadTemplate
import OAI.Computability.NearSquareRoot.InterchangeStageScriptCost

/-!
# Charged execution of a rectangle stage on packed data

The output below is the sum of the actual stage operators on each fixed
payload coordinate. The outer header never supplies the payload ruler.
All child requests contain packed records with inherited dimensions.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangePayloadBank

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Loom NearSquareRoot.InterchangeAddress NearSquareRoot.Interchange
  NearSquareRoot.Interchange.StageScript NearSquareRoot.Interchange.StageRoute
  NearSquareRoot.Interchange.StageLedger

/-- Each payload position is an independent copy of the semantic program. -/
theorem eval_at_payload {I M E A B : Type} {X D : I → Type}
    (θ : (i:I) → M → Equiv.Perm (X i)) (p : Program M E A B) (i : I) (d : D i)
    (v : A → X i × D i → E) :
    (fun b a => eval (withPayload D θ i) p v b (a,d)) =
    eval (θ i) p (fun a k => v a (k,d)) := by
  induction p with
  | table => rfl
  | route => rfl
  | seq p q ip iq =>
    simp only [eval_seq]
    exact (iq _).trans (congrArg (eval (θ i) q) (ip v))

variable {I L H B Q K Row E J : Type} [DecidableEq L] [Fintype L] [Nonempty L]
    [Fintype H] [Fintype B] [Fintype Q] [Fintype Row] [Nonempty Row] [Finite E]
    [Field K] [AddCommGroup E] [Module K E] [DecidableEq J] {D : I → Type}
    {p n : ℕ} [NeZero p] {r : Regime I} {l : I → ℕ}

/-- One tape stage, charged at the sparse matrix ledger. Width and record
count are dynamic. Every pivot's work is issued as a recursive request on
the original packed alphabet. -/
theorem execute_stage (ord : J ≃ Fin n) (P G S : I → Dims.Tape) (f : I → ℕ)
    (hp : 2 ≤ p) (hf : r.Has (tally ∘ f)) (hP : Told r P) (hG : Told r G) (hS : Told r S)
    (payload : (i:I) → Series (D i)) (h : ∀ i, (payload i).count ≤ l i)
    (src : E → Tree) (inj : Function.Injective src) (rect : B → Rectangle L)
    (selRow selCol : H → L) (g : (i:I) → Layout rect Q (domain (J:=J) (b:=p) P G S f i))
    (mid : Matrix H H K) (hM : (rectangleMatrix (K:=K) rect).submatrix id selCol * mid *
      (rectangleMatrix rect).submatrix selRow id = rectangleMatrix rect)
    (A₀ : (Row → E) →+ (Row → E)) (A : Q → (Row → E) →+ (Row → E))
    (price : Move rect Q selRow selCol → ℕ) (hi : price .idle = 0)
    (ha : ∀ j e, price (.align j e) = 0) (hu : ∀ j e, price (.unalign j e) = 0)
    (ops : Move rect Q selRow selCol → List (Lag J p))
    (legal : ∀ m a, a ∈ ops m → a.legal (ranking ord))
    (acts : ∀ i m, recreation ord (P i) (G i) (S i) (f i) (ops m) (legal m) = (g i).perm m)
    (paid : ∀ m, ((ops m).map Lag.prices).sum ≤ price m)
    (lanes : Series Row) (labels : Series L)
    (v : (i:I) → L → domain (J:=J) (b:=p) P G S f i × D i → Row → E) :
    let points := layoutRows (b:=p) ord P G S f
    let rows := lanes.cart labels
    ChargedTyped (r:=r) (l:=l) ord P G S f (b:=p) (Good payload src)
      (moveCharges Row price).count
      (render points payload rows src (fun i ra k => v i ra.2 k ra.1))
      (render points payload rows src (fun i rw k => (A₀ (v i rw.2 k) + ∑ j,
        A j (v i rw.2 (((g i).S j rw.2).symm ((g i).T j rw.2 k.1), k.2))) rw.1)) := by
  let program := stage rect selRow selCol mid A₀ A
  let θ := fun i => (g i).perm (I:=selRow) (J:=selCol)
  have step m x hx good := (execute_charged_typed (r:=r) (l:=l) ord P G S f (Good payload src)
    hp hf hP hG hS (ops m) (legal m) x hx good).monotone (show (_ : ℤ) ≤ (price m : ℤ) by
      exact_mod_cast paid m)
  simp_rw [acts] at step
  have t := run (layoutRows (b:=p) ord P G S f) (layoutRows_station ord P G S f hp hf hP hG hS)
    payload h src inj 0 θ price step program lanes labels labels v
  dsimp only
  have ev (i : I) w k : eval (withPayload D θ i) program (v i) w k =
      A₀ (v i w k) + ∑ j, A j (v i w (((g i).S j w).symm ((g i).T j w k.1),k.2)) := by
    obtain ⟨a,d⟩ := k
    have e := congrFun (congrFun (eval_at_payload θ program i d (v i)) w) a
    exact e.trans (eval_stage selRow selCol (g i) (fun w a => v i w (a,d)) mid hM A₀ A w a)
  simp_rw [ev] at t
  simpa only [program, scalar_stage_cost Row mid A₀ A price hi ha hu] using t

end InterchangePayloadBank

end NearSquareRoot
end Computability
end OAI
