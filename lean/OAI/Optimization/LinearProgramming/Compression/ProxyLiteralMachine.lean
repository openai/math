import OAI.Optimization.LinearProgramming.Compression.ComputedProxyOperands
import OAI.Optimization.LinearProgramming.Compression.PowerTapeCombined

/-! Product sign for the true computed proxy vector from literal, explicitly constructed
exponent bits. The native runtime includes the conversion from bits to opcodes. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM
open scoped BigOperators

private theorem literalBits_le_opcodeBudget (ps : List (ℚ × ℤ)) :
    ((ps.map Prod.snd).map fun e => e.natAbs.size + 2).sum ≤
      (ps.map fun p => 2*p.2.natAbs.size + 3).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.map_cons,List.sum_cons]; omega

theorem computedProxyLiteralRAM_correct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (fuel prec B : ℕ) {A : ℤ} (c : ℤ) (a : ι → ℤ) (mag : ι → ℚ)
    (hm : ∀ i, 0 < mag i) (hbits : ∀ i, ratBits (mag i) ≤ B)
    (hform : |c| + ∑ i, |a i| ≤ A) (hcut : (2 : ℤ)^prec * A ≤ 2^fuel)
    (hsym : ∃ j, logProxyNumerator fuel prec (mag j) = none)
    (indices : List ι) (hindices : indices.Perm
      ((Finset.univ.filter fun i => logProxyNumerator fuel prec (mag i) = none).toList)) :
    let data i := logProxyNumerator fuel prec (mag i)
    let large := Finset.univ.filter (fun i => data i = none)
    let D := (2 : ℕ)^(prec+2)
    let grid i := (data i).getD 0
    let ps := proxyPowerOperands indices (clearedProxyOffset large D c a grid) D a mag
    let form := (c : ℝ) + ∑ i, (a i : ℝ) * logProxyValue prec (mag i) (data i)
    ∃ k ≤ 30*(2*(2*fuel+3)+3+Fintype.card ι*(2*(fuel+3)+3))+9, ∃ tr : Fin (k+1) → State ℚ,
      Trace literalPowerCompareProgram (start (powerEncoderAddressInput (signedBitTape (ps.map Prod.snd)))
        (powerTapeScalarInput (ps.map Prod.fst))) k tr ∧
      (tr (Fin.last k)).data 2 = proxyProduct large D c a grid mag ∧
      (tr (Fin.last k)).output = some (if form < 0 then 0 else if 0 < form then 2 else 1) ∧
      ∀ i, scalarBound (10 + 16*B^2 + Fintype.card ι*(3+(4*B+1)*B)) (tr i) := by
  let data i := logProxyNumerator fuel prec (mag i)
  let large := Finset.univ.filter (fun i => data i = none)
  let D : ℕ := 2^(prec+2)
  let grid i := (data i).getD 0
  let offset := clearedProxyOffset large D c a grid
  let ps := proxyPowerOperands indices offset D a mag
  obtain ⟨j,hj⟩ := hsym
  have hlarge : large.Nonempty := ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
  have hperm : indices.Perm large.toList := hindices
  have hlegal := proxyPowerOperands_legal large indices hperm offset D a mag (fun i _ => hm i)
  obtain ⟨out,run,hval,_⟩ := productOps_run ps hlegal
  have hresult : out.product = proxyProduct large D c a grid mag := hval.trans
    (proxyOperands_value _ _ hperm _ _ _ _ _)
  obtain ⟨k,hk,tr,ht,hr,ho,hs⟩ := literalPowerCompareProgram_correct (ps.map Prod.snd)
    (ps.map Prod.fst) run (fun _ h => ⟨h.1,h.2.1,h.2.2.1⟩) run.safe_start.2.2.2
  rw [hresult] at hr ho
  have hD : 0 < D := by dsimp [D]; positivity
  rw [proxyProductTag large hlarge D hD c a grid mag (fun i _ => hm i)] at ho
  have hreal := logProxyAffine_eq fuel prec c a mag
  change proxyAffine large D c a grid mag = _ at hreal
  rw [hreal] at ho
  obtain ⟨hK,hE,hclock⟩ := computedProxy_operand_bounds fuel prec B c a mag hm hbits hform hcut ⟨j,hj⟩
  have hps : ps.Perm (proxyPowerOperands large.toList offset D a mag) :=
    List.Perm.cons _ (hperm.map (fun i => (mag i,(D : ℤ)*a i)))
  have htime := (literalBits_le_opcodeBudget ps).trans
    ((hps.map (fun p => 2*p.2.natAbs.size+3)).sum_eq.le.trans hclock)
  have hbound := proxyPowerOperands_budget large indices hperm offset D a mag hK
    (fun i _ => hE i) (fun i _ => hbits i)
  have hscale : 10 + 4*(4*B^2) + large.card*(3+(4*B+1)*B) ≤
      10 + 16*B^2 + Fintype.card ι*(3+(4*B+1)*B) := by
    have hcard := Nat.mul_le_mul_right (3+(4*B+1)*B) (Finset.card_le_univ large)
    omega
  exact ⟨k,hk.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 30 htime) 9),tr,ht,hr,ho,
    fun i j => (hs i j).trans (hbound.trans hscale)⟩

end Compression
end LinearProgramming
end Optimization
end OAI
