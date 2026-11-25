import OAI.Optimization.LinearProgramming.Lattice.BitProbeTrace

/-! The continuation's signed numerator, denominator, and chronological row at every bisection. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver
namespace Probe

private def numerator {p : ℕ} (o : (Fin p→ℤ)→Bool) (a b : Fin p→ℤ) (t : ℕ) : ℤ :=
  SignQueries.run o (dyadicSearchQ a b t)

def coordinate {p : ℕ} (o : (Fin p→ℤ)→Bool) (a b : Fin p→ℤ) (t : ℕ) : ℚ :=
  ((SignQueries.run o (dyadicSearchQ a b t) : ℤ) : ℚ) / (2:ℚ)^t

private theorem numerator_succ {p : ℕ} (o : (Fin p→ℤ)→Bool) (a b : Fin p→ℤ) (t : ℕ) :
    numerator o a b (t+1) = 2*numerator o a b t + if o (dyadicQuery a b t (numerator o a b t)) then 1 else -1 := by
  simp only [numerator,dyadicSearchQ,SignQueries.run_bind,SignQueries.run]
  rfl

private theorem dyadic_queryRows_succ {p : ℕ} (o : (Fin p→ℤ)→Bool) (a b : Fin p→ℤ) (t : ℕ) :
    queryRows o (dyadicSearchQ a b (t+1)) =
      queryRows o (dyadicSearchQ a b t) ++ [List.ofFn (dyadicQuery a b t (numerator o a b t))] := by
  simp only [numerator,dyadicSearchQ,queryRows_bind,queryRows_ask,queryRows_done]

private def ratioSlot {p : ℕ} (o : (Fin p→ℤ)→Bool) (a b : Fin p→ℤ) (z : Params)
    (tail : IntMatrix) (vs : List ℚ) (total t : ℕ) : Ratio :=
  (((z,List.ofFn b),(List.ofFn a,tail)),((numerator o a b t,2^t),(total-t-1,vs)))

private def afterRatio {p : ℕ} (o : (Fin p→ℤ)→Bool) (a b : Fin p→ℤ) (z : Params)
    (tail : IntMatrix) (vs : List ℚ) (total t : ℕ) : Action :=
  if t=total then nextRow (z,List.ofFn b) tail (coordinate o a b t :: vs)
  else emitRatio (ratioSlot o a b z tail vs total t)

private theorem ratio_tick {p : ℕ} (O : Row→Bool) (o : (Fin p→ℤ)→Bool)
    (h : ∀ a, O (List.ofFn a) = o a) (a b : Fin p→ℤ) (z : Params)
    (tail : IntMatrix) (vs : List ℚ) (total t : ℕ) (ht : t<total) :
    Steps O (afterRatio o a b z tail vs total t) [List.ofFn (dyadicQuery a b t (numerator o a b t))]
      (afterRatio o a b z tail vs total (t+1)) := by
  let s := ratioSlot o a b z tail vs total t
  let q := dyadicQuery a b t (numerator o a b t)
  have he : emitRatio s = ask (List.ofFn q) (.inr (.inr s)) := by
    simp [emitRatio,s,ratioSlot,q,dyadic_combine_pack]
  rw [afterRatio,ite_eq_right (Nat.ne_of_lt ht),he]
  apply Steps.ask
  rw [h]
  have hd : 2*(2^t : ℕ) = 2^(t+1) := by rw [pow_succ,Nat.mul_comm]
  have next : advance (o q) (.inr (.inr s)) = afterRatio o a b z tail vs total (t+1) := by
    by_cases last : t+1=total
    · have hl : total-t-1=0 := by omega
      rw [afterRatio,ite_eq_left last]
      simp only [advance,ratioReply,s,ratioSlot,hl,ite_true,hd]
      change nextRow _ _ (((2*numerator o a b t + (if o q then 1 else -1) : ℤ) : ℚ) /
        ((2^(t+1) : ℕ) : ℚ) :: vs) = _
      have hnum := numerator_succ o a b t
      change numerator o a b (t+1) = 2*numerator o a b t+(if o q then 1 else -1) at hnum
      rw [← hnum]
      simp [coordinate,numerator]
    · have hl : total-t-1≠0 := by omega
      have hs : total-t-1-1=total-(t+1)-1 := by omega
      simp only [advance,ratioReply,s,ratioSlot,ite_eq_right hl,hd,afterRatio,ite_eq_right last,hs,numerator_succ,q]
  rw [next]
  exact .stop _

/-- A complete run on one input row returns its dyadic rational and continues to the
next row. The queried coefficient at depth `t` uses exactly denominator `2^t`. -/
theorem ratio_prefix {p : ℕ} (O : Row→Bool) (o : (Fin p→ℤ)→Bool) (h : ∀ a, O (List.ofFn a) = o a)
    (a b : Fin p→ℤ) (z : Params) (tail : IntMatrix) (vs : List ℚ) (hk : 0<z.1.2) :
    Steps O (nextRow (z,List.ofFn b) (List.ofFn a :: tail) vs) (queryRows o (dyadicSearchQ a b z.1.2))
      (nextRow (z,List.ofFn b) tail (coordinate o a b z.1.2 :: vs)) := by
  let k := z.1.2
  have iter (t : ℕ) (ht : t≤k) : Steps O (afterRatio o a b z tail vs k 0)
      (queryRows o (dyadicSearchQ a b t)) (afterRatio o a b z tail vs k t) := by
    induction t with
    | zero => exact .stop _
    | succ t ih =>
      rw [dyadic_queryRows_succ]
      exact (ih (by omega)).append (ratio_tick O o h a b z tail vs k t (by omega))
  change 0<k at hk
  simpa only [afterRatio,ite_eq_right (Nat.ne_of_lt hk),ite_true,ratioSlot,numerator,dyadicSearchQ,
    SignQueries.run,pow_zero,Nat.sub_zero,k,nextRow] using iter k le_rfl

end Probe
end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
