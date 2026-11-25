import OAI.Computability.MultitapeWeakETH.SparsePreparation
import OAI.Computability.MultitapeWeakETH.VariableClock

/-! # Reading the variable count and constructing the dyadic reciprocal sparsification budget -/

namespace OAI.Computability.MultitapeWeakETH.SparsePreparation

open IntegerMultiplication Code Bits Strip Staff Carry
open Algorithms.SubexponentialSAT
open scoped Classical
noncomputable section

private abbrev Scan := Bool × Tally × Word

private def advance (p : Scan × Bool) : Scan :=
  let st := p.1
  bif st.1 then
    bif p.2 then (true,()::st.2.1,st.2.2) else (false,st.2.1,st.2.2)
  else (false,st.2.1,st.2.2 ++ [p.2])

private theorem advance_poly : Poly advance := by unfold advance; fun_prop

private def scanning (w : Word) (st : Scan) := w.foldl (fun s b => advance (s,b)) st

private theorem advance_size (s : Scan) (b : Bool) : size (advance (s,b)) ≤ size s+2 := by
  rcases s with ⟨r,n,x⟩
  have snoc (bit : Bool) : size (x++[bit]) = size x+2 := by
    have h := size_append_right x [bit]
    simp only [size_cons,size_nil,show size bit=1 from rfl] at h
    omega
  cases r <;> cases b <;> simp [advance,snoc,show size ()=1 from rfl] <;> omega

private theorem scanning_poly : Poly (fun q : Word × Scan => scanning q.1 q.2) := by
  apply Poly.fold_left advance_poly 5 1
  rintro ⟨w,s⟩ l h
  have cost (bs : Word) (s : Scan) : size (scanning bs s) ≤ size s+2*bs.length := by
    induction bs generalizing s with
    | nil => simp [scanning]
    | cons b bs ih =>
      change size (scanning bs (advance (s,b))) ≤ _
      have hs := advance_size s b
      specialize ih (advance (s,b))
      simp only [List.length_cons,Nat.mul_add] at *
      omega
  have hl := h.length_le
  change l.length ≤ w.length at hl
  have sz := duration w
  exact (cost l s).trans (by simp only [size_prod,pow_one]; omega)

def header (w : Word) : Tally × Word := (scanning w (true,[],[])).2

theorem header_poly : Poly header :=
  ((Poly.identity.pair (Code.Poly.const _)).compose scanning_poly).sndCompose

theorem header_eq (n : ℕ) (body : Word) : header (Encoding.encodeNat n++body) = (tally n,body) := by
  have read (w acc : Word) (n : Tally) : scanning w (false,n,acc) = (false,n,acc++w) := by
    induction w generalizing acc with
    | nil => simp [scanning]
    | cons b w ih =>
      change scanning w (false,n,acc++[b]) = _
      rw [ih,List.append_assoc]; rfl
  have scanOnes (i j : ℕ) : scanning (Encoding.encodeNat i++body) (true,tally j,[]) =
      (false,tally (j+i),body) := by
    induction i generalizing j with
    | zero => simpa [Encoding.encodeNat,scanning,List.foldl_cons,advance] using read body [] (tally j)
    | succ i ih =>
      change scanning ((List.replicate (i+1) true ++ [false])++body) (true,tally j,[]) = _
      rw [List.replicate_succ,List.cons_append,List.cons_append]
      change scanning (Encoding.encodeNat i++body) (true,tally (j+1),[]) = _
      rw [ih,show j+1+i=j+(i+1) by omega]
  simpa only [header,Nat.zero_add,show tally 0=[] from rfl] using congrArg Prod.snd (scanOnes n 0)

private theorem floor_log (n : ℕ) : Nat.log 2 n = Nat.clog 2 (n+1)-1 := by
  by_cases hn : n=0
  · subst n; simp
  have upper := (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr
    (show n+1 ≤ 2^(Nat.log 2 n+1) from Nat.lt_pow_succ_log_self (by decide) n)
  have lower := (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).mpr
    (show 2^(Nat.log 2 n) < n+1 from Nat.lt_succ_of_le (Nat.pow_log_le_self 2 hn))
  omega

theorem reciprocal {I : Type} {r : Regime I} {n : I → ℕ} (known : Realizes r n) (q : ℕ) :
    Figure r (fun i => sparseBudget q (n i)) := by
  let bits := ((Figure.of_spoken known).added (Figure.natural 1)).short_log
  let logs := (Figure.of_spoken bits).subtracted (Figure.natural 1)
  let exps := logs.quotients (Figure.natural q)
  have lim := (diameter _ bits).mono (fun i => (Nat.div_le_self _ q).trans (Nat.sub_le _ 1))
  convert (Figure.natural 2).repeated (exps.pay lim) using 1
  funext i
  rw [sparseBudget,floor_log]

theorem reciprocal_le (q n : ℕ) : sparseBudget q n ≤ n+1 := by
  by_cases hn : n=0
  · subst n; simp [sparseBudget]
  exact (Nat.pow_le_pow_right (by decide : 0<2) (Nat.div_le_self _ _)).trans ((Nat.pow_log_le_self 2 hn).trans (by omega))

theorem binary_value (w : Word) : BinaryArithmetic.toNat w = value w := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [BinaryArithmetic.toNat,ih]

end
end OAI.Computability.MultitapeWeakETH.SparsePreparation
