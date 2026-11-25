import OAI.Computability.NearSquareRoot.InterchangeBankRun
import OAI.Computability.NearSquareRoot.InterchangeStageScriptCost

/-!
# Charged tape execution of a shared sum of swaps

The scalar backend compiles concrete address instruction lists. Each request
has the encoded payload of an original row and inherits its tape dimensions.
The shared stage runs on these rows with an explicit ledger counting each
endpoint conversion and each incidence of a selected row or column.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeBank

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Loom NearSquareRoot.InterchangeAddress NearSquareRoot.Interchange
  NearSquareRoot.Interchange.StageRoute NearSquareRoot.Interchange.StageLedger

variable {I M J F : Type} [DecidableEq J] [Finite F] {n b : ℕ} [NeZero b]
  {r : Regime I} {l : I → ℕ} (ord : J ≃ Fin n) (P G S : I → Dims.Tape) (f : I → ℕ)

/-- Child descriptors preserve both the symbol representation and the allowed
width, record count and spectator dimensions. -/
abbrev symbolZone (sym : F → Tree) (i : I) (a : Request b) :=
  (allowed f (countRows (b:=b) ord P G S f) l i a ∧ ∀ k, a.contents k ∈ Set.range sym) ∧
    inherited b (P i) (G i) (S i) a

/-- Compiler directly backed by P192 layout programs on one physical row. -/
def addressCompiler (hb : 2 ≤ b) (hf : r.Has (tally ∘ f))
    (hp : Told r P) (hg : Told r G) (hs : Told r S) (sym : F → Tree)
    (hinj : Function.Injective sym)
    (sem : (i : I) → M → Equiv.Perm (domain (J:=J) (b:=b) P G S f i))
    (price : M → ℕ) (ops : M → List (Lag J b))
    (legal : ∀ u a, a ∈ ops u → a.legal (ranking ord))
    (acts : ∀ i u, recreation ord (P i) (G i) (S i) (f i) (ops u) (legal u) = sem i u)
    (paid : ∀ u, ((ops u).map Lag.prices).sum ≤ price u) :
    Compiler r (countRows (b:=b) ord P G S f) l (Request.job b)
      (symbolZone (l:=l) ord P G S f sym) F sem price 1 := by
  apply symbolCompiler (layoutRows ord P G S f) (layoutRows_station ord P G S f hb hf hp hg hs) sym hinj
  intro u v
  have h := execute_charged_typed (r:=r) (l:=l) ord P G S f
    (fun _ t => t ∈ Set.range sym) hb hf hp hg hs (ops u) (legal u)
    (fun i => sym ∘ v i) (finite_manifest _ _) (fun i k => Set.mem_range_self _)
  simp_rw [acts] at h
  exact h.monotone (by exact_mod_cast paid u)

section Stage

variable {I Y L H B Q K Row E : Type} [DecidableEq L]
    [Fintype L] [Fintype H] [Fintype B] [Fintype Q] [Fintype Row]
    [Field K] [AddCommGroup E] [Module K E]
    {X : I → Type} {r : Regime I} {N l : I → ℕ} {job : Job Y} {zone : I → Y → Prop}
    (rect : B → Rectangle L) (selRow selCol : H → L)
    (g : (i : I) → Layout rect Q (X i))

/-- A complete pencil application as one P192 recursive tape-program
certificate. The ledger is computed from the actual sparse backing rows of
the script, and the result holds for arbitrary inputs at every address. -/
theorem execute_shared_stage (mid : Matrix H H K)
    (hM : (rectangleMatrix (K:=K) rect).submatrix id selCol * mid *
      (rectangleMatrix rect).submatrix selRow id = rectangleMatrix rect)
    (A₀ : (Row → E) →+ (Row → E)) (A : Q → (Row → E) →+ (Row → E))
    (quote : Move rect Q selRow selCol → ℕ)
    (hi : quote .idle = 0) (ha : ∀ j e, quote (.align j e) = 0)
    (hu : ∀ j e, quote (.unalign j e) = 0)
    (machine : Compiler r N l job zone E (fun i => (g i).perm) quote 1)
    (rows : Series Row) (labels : Series L) (x : (i : I) → L → X i → Row → E) :
    let render := (machine.lanes rows).render (A:=L) labels
    Hopto job r N l zone ((moveCharges Row quote).count : ℤ) (together r.header (render x))
      (render fun i w a => A₀ (x i w a) +
        ∑ j, A j (x i w (((g i).S j w).symm ((g i).T j w a)))) := by
  let prog := stage rect selRow selCol mid A₀ A
  have run := (machine.lanes rows).run prog labels labels x
  have eval : (fun i => StageScript.eval (g i).perm prog (x i)) =
      (fun i w a => A₀ (x i w a) + ∑ j, A j (x i w (((g i).S j w).symm ((g i).T j w a)))) := by
    funext i w a
    exact eval_stage selRow selCol (g i) (x i) mid hM A₀ A w a
  rw [eval] at run
  simpa only [Nat.one_mul, prog, scalar_stage_cost Row mid A₀ A quote hi ha hu] using run

end Stage

end InterchangeBank

end NearSquareRoot
end Computability
end OAI
