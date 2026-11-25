import OAI.Computability.NearSquareRoot.PrecisionNodeRecursion
import OAI.Computability.NearSquareRoot.KernelComputableTemplateSearch

/-! # A computable numerical error budget from the raw template

Each opcode receives an integer bound from its declared bank sizes and its
literal signed numerators. The product of these bounds controls the decoded
template, including malformed syntax and the parser's default zero bank.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode

open KernelPass KernelPass.ComputableSyntax KernelComputableDyadic PhysicalWalsh PhysicalWalshGrid

private def mass (l : List Code) : ℕ :=
  l.foldr (fun c b => c.1.1 + c.1.2 + b) 0

private theorem mass_lookup (l : List Code) (j : ℕ) :
    (coefficient (l.getD j zero)).1.natAbs ≤ mass l := by
  induction l generalizing j with
  | nil => simp [List.getD, coefficient, mass, zero]
  | cons c s ih =>
    cases j with
    | zero =>
      change ((c.1.1 : ℤ) - c.1.2).natAbs ≤ c.1.1 + c.1.2 + mass s
      exact (Int.natAbs_sub_le _ _).trans (Nat.le_add_right _ _)
    | succ j =>
      change (coefficient (s.getD j zero)).1.natAbs ≤ c.1.1+c.1.2+mass s
      exact (ih j).trans (Nat.le_add_left _ _)

private theorem mass_primrec : Primrec mass :=
  Primrec.list_foldr .id (.const 0)
    (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp .snd)))
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp .snd)))) (Primrec.snd.comp .snd)).to₂

private def budget (op : Op) : ℕ := 32 + arg op 0 + (arg op 1 + 1)*(arg op 0 + 1)*(mass op.2.2 + 1)

private theorem budget_primrec : Primrec budget := by
  have a := primrec_arg.comp Primrec.id (.const 0)
  have b := primrec_arg.comp Primrec.id (.const 1)
  have v : Primrec (fun op : Op => mass op.2.2) := mass_primrec.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.nat_add.comp (Primrec.nat_add.comp (.const 32) a)
    (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.nat_add.comp b (.const 1))
      (Primrec.nat_add.comp a (.const 1))) (Primrec.nat_add.comp v (.const 1)))

private def score {a : ℕ} (p : Packed (a+1)) := p.i + templateFactor p.plan + 4

private theorem score_empty (a : ℕ) : score (Packed.empty (a+1)) = 5 := by
  simp [score,Packed.empty,templateFactor,numericalFactor,coefficientFactor,mixGain]

private theorem score_zero (a : ℕ) : score (Packed.zeroRow (a+1)) = 6 := by
  simp [score,Packed.zeroRow,templateFactor,numericalFactor,coefficientFactor,mixGain]

private theorem score_leaf (a : ℕ) (op : Op) : score (Packed.leaf (a+1) op) ≤ budget op := by
  have hM (j : ℕ) := mass_lookup op.2.2 j
  have limit (c : Fin (arg op 1) → Fin (arg op 0) → Coefficient)
      (hc : ∀ b i, (c b i).1.natAbs ≤ mass op.2.2) :
      mixGain c ≤ arg op 1 * arg op 0 * mass op.2.2 := by
    unfold mixGain
    calc
      _ ≤ ∑ _ : Fin (arg op 1), ∑ _ : Fin (arg op 0), mass op.2.2 :=
        Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun i _ => hc b i
      _ = _ := by simp [Nat.mul_assoc]
  have scale : KernelScaleNorm.gain (KernelComputableSelector.table (q := arg op 0) op.2.2) ≤ 1 + mass op.2.2 := by
    apply Nat.add_le_add_left
    exact Finset.sup_le fun s _ => hM _
  unfold Packed.leaf
  split
  · let c := fun (b : Fin (arg op 1)) (i : Fin (arg op 0)) => coefficient (op.2.2.getD (b.val*arg op 0+i.val) zero)
    have hc := limit c (fun b i => hM _)
    change arg op 0 + (mixGain c + 1) + 4 ≤ budget op
    unfold budget
    nlinarith
  · split
    · split
      · split
        · change 1 + (0+1) + 4 ≤ budget op
          unfold budget
          omega
        · rw [score_zero]; unfold budget; omega
      · rw [score_zero]; unfold budget; omega
    · split
      · change 1 + (KernelScaleNorm.gain (KernelComputableSelector.table (q := arg op 0) op.2.2) + 1) + 4 ≤ _
        have hmass : mass op.2.2 + 1 ≤ (arg op 1+1)*(arg op 0+1)*(mass op.2.2+1) :=
          Nat.le_mul_of_pos_left _ (by positivity)
        unfold budget
        omega
      · split
        · split
          · change 1 + (0+1) + 4 ≤ budget op
            unfold budget
            omega
          · rw [score_zero]; unfold budget; omega
        · rw [score_empty]; unfold budget; omega

private theorem score_seq {a : ℕ} (p q : Packed (a+1)) : score (Packed.seq p q) ≤ score p * score q := by
  obtain ⟨i,o,p⟩ := p
  obtain ⟨j,k,q⟩ := q
  by_cases h : k = i
  · subst k
    simp only [Packed.seq]
    change j + (templateFactor p * (templateFactor q + 1)) + 4 ≤
      (i + templateFactor p + 4) * (j + templateFactor q + 4)
    nlinarith
  · rw [Packed.seq,dite_eq_right h,score_empty]
    unfold score
    nlinarith

private theorem score_parallel {a : ℕ} (p q : Packed (a+1)) :
    score (Packed.parallel p q) ≤ score p * score q := by
  change p.i+q.i+max (templateFactor p.plan) (templateFactor q.plan)+4 ≤
    (p.i + templateFactor p.plan + 4) * (q.i + templateFactor q.plan + 4)
  rw [Nat.max_def]
  split <;> nlinarith

private def stackWeight {a : ℕ} (s : List (Packed (a+1))) := (s.map score).prod
private def wordWeight (w : List Op) := w.foldr (fun op s => budget op * s) 1

private theorem step_le {a : ℕ} (op : Op) (s : List (Packed (a+1))) :
    stackWeight ((Packed.algebra (a+1)).step op s) ≤ budget op * stackWeight s := by
  have hb : 25 ≤ budget op := by unfold budget; omega
  have merge (f : Packed (a+1) → Packed (a+1) → Packed (a+1))
      (hf : ∀ p q, score (f p q) ≤ score p * score q) :
      stackWeight (f (s.getD 0 (Packed.empty _)) (s.getD 1 (Packed.empty _)) :: s.drop 2) ≤
        budget op * stackWeight s := by
    cases s with
    | nil =>
      simpa [stackWeight,score_empty] using
        (hf (Packed.empty _) (Packed.empty _)).trans (by simpa [score_empty] using hb : _ ≤ budget op)
    | cons p s =>
      cases s with
      | nil =>
        change score (f p (Packed.empty _)) * 1 ≤ budget op * (score p * 1)
        simp only [mul_one]
        calc
          _ ≤ score p * score (Packed.empty _) := hf p _
          _ = 5*score p := by rw [score_empty,mul_comm]
          _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
      | cons q s =>
        change score (f p q) * stackWeight s ≤ budget op * (score p*(score q*stackWeight s))
        exact (Nat.mul_le_mul_right _ (hf _ _)).trans (by rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega))
  unfold Algebra.step
  split
  · exact merge Packed.seq score_seq
  · split
    · exact merge Packed.parallel score_parallel
    · exact Nat.mul_le_mul_right _ (score_leaf a op)

private theorem parse_score (a : ℕ) (ops : List Op) :
    score (Packed.decode (a+1) ops) ≤ 5 * wordWeight ops := by
  have run : stackWeight (ops.foldr (Packed.algebra (a+1)).step []) ≤ wordWeight ops := by
    induction ops with
    | nil => exact le_rfl
    | cons op w ih => exact (step_le op _).trans (Nat.mul_le_mul_left _ ih)
  have pos (s : List (Packed (a+1))) : 0 < stackWeight s := by
    induction s with
    | nil => exact Nat.zero_lt_one
    | cons p s ih => exact Nat.mul_pos (by unfold score; omega) ih
  generalize ht : ops.foldr (Packed.algebra (a+1)).step [] = s at run
  change score ((ops.foldr (Packed.algebra (a+1)).step []).getD 0 (Packed.empty _)) ≤ _
  rw [ht]
  cases s with
  | nil =>
    rw [List.getD_nil,score_empty]
    change 1 ≤ wordWeight ops at run
    omega
  | cons p ps =>
    change score p ≤ _
    change score p * stackWeight ps ≤ wordWeight ops at run
    exact ((Nat.le_mul_of_pos_right _ (pos _)).trans run).trans (by omega)

/-- Bound computed solely from the emitted raw arity and prefix instructions. -/
def rawFactor (r : Raw) : ℕ := (5 * wordWeight r.2 + 2)^2

theorem rawFactor_primrec : Primrec rawFactor := by
  have word : Primrec wordWeight := Primrec.list_foldr .id (.const 1)
    (Primrec.nat_mul.comp (budget_primrec.comp (Primrec.fst.comp .snd)) (Primrec.snd.comp .snd)).to₂
  exact Generator.primrecNatPow.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (.const 5) (word.comp .snd)) (.const 2)) (.const 2)

/-- Every typed square plan decoded from the literal raw program has this
numerical amplification bound, including on recursively substituted children. -/
theorem recursionFactor_le_rawFactor {a W : ℕ} (ops : List Op) (p : Plan (a+1) W W)
    (h : Packed.decode (a+1) ops = ⟨W,W,p⟩) : recursionFactor p ≤ rawFactor (a+1,ops) := by
  have hle := parse_score a ops
  rw [h] at hle
  change W + templateFactor p + 4 ≤ _ at hle
  unfold recursionFactor rawFactor
  rw [pow_two]
  exact Nat.mul_le_mul (by dsimp; omega) (by dsimp; omega)

end PhysicalWalshNode

end NearSquareRoot
end Computability
end OAI
