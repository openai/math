import OAI.Computability.MultitapeWeakETH.WitnessWalkSpace
import OAI.Computability.MultitapeWeakETH.WitnessForestCodes

/-! # Bounding every accepted traversal by a decreasing row weight -/

namespace OAI.Computability.MultitapeWeakETH.WitnessWalk

open IntegerMultiplication Code
open private none_iter from OAI.Computability.MultitapeWeakETH.WitnessWalkExact

variable {D : Type} {visit : Visit D} {ctx : D}

/-- Successful local visits on admissible packets preserve admissibility,
decrease the total pending weight, and return a shorter or equal stream. -/
def Descent (visit : Visit D) (ctx : D) (ok : Job → Prop) (weight : Job → ℕ) :=
  ∀ j, ok j → ∀ bits children next names, visit ((ctx,j),bits) = some ((children,next),names) →
    (∀ child ∈ children, ok child) ∧ (children.map weight).sum < weight j ∧ next.length ≤ bits.length

variable {ok : Job → Prop} {weight : Job → ℕ} (h : Descent visit ctx ok weight)

include h in
private theorem trace_of_run (n : ℕ) (jobs : List Job) (bits : Bits.Word) (prior : List Tally)
    (tail : Bits.Word) (labels : List Tally) (good : ∀ j ∈ jobs, ok j)
    (accepted : (advance visit ctx)^[n] (some ((jobs,bits),prior)) = some (([],tail),labels)) :
    ∃ seen, Transcript visit ctx ((jobs,bits),prior) seen tail labels ∧
      (∀ j ∈ seen, ok j) ∧ seen.length ≤ (jobs.map weight).sum := by
  induction n generalizing jobs bits prior with
  | zero =>
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := (Prod.mk.inj (Option.some.inj accepted)).imp_left Prod.mk.inj
    exact ⟨[],.done _ _,by simp,le_rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply] at accepted
    cases jobs with
    | nil => exact ih [] bits prior good accepted
    | cons j js =>
      rw [advance_cons] at accepted
      cases e : visit ((ctx,j),bits) with
      | none => simp only [e,Option.map_none,none_iter,reduceCtorEq] at accepted
      | some ans =>
        obtain ⟨⟨children,next⟩,names⟩ := ans
        obtain ⟨child,less,shrunk⟩ := h j (good _ List.mem_cons_self) _ _ _ _ e
        simp only [e,Option.map_some] at accepted
        obtain ⟨seen,trace,legal,budget⟩ := ih (children++js) next (prior++names)
          (fun x hx => (List.mem_append.mp hx).elim (child x) (fun hx => good _ (List.mem_cons_of_mem _ hx))) accepted
        refine ⟨j::seen,.step e shrunk trace,?_,?_⟩
        · intro x hx
          exact (List.mem_cons.mp hx).elim (fun eqn => eqn ▸ good j List.mem_cons_self) (legal x)
        · simp only [List.map_append,List.sum_append,List.map_cons,List.sum_cons,List.length_cons] at *
          omega

include h in
/-- Sufficient unary cutoffs for an accepted code, uniformly over all traversal
prefixes. The parameters bound the complete label list and individual packets. -/
theorem evaluate_of_descent [Codec D] {jobs : List Job} {bits tail : Bits.Word} {labels : List Tally}
    (accept : Accepts visit ctx jobs bits tail labels) (good : ∀ j ∈ jobs, ok j) (fuel cap : Tally)
    (time : (jobs.map weight).sum ≤ fuel.length) (jobSize labelSize : ℕ)
    (bounded : ∀ j, ok j → size j ≤ jobSize) (small : ∀ l ∈ labels, l.length ≤ labelSize)
    (room : (jobSize+1)*fuel.length + 2*bits.length + (2*labelSize+2)*labels.length + 5 ≤ cap.length) :
    evaluate visit (fuel,(ctx,cap),some ((jobs,bits),[])) = some (tail,labels) := by
  obtain ⟨n,parse⟩ := accept
  have final : (advance visit ctx)^[n] (some ((jobs,bits),[])) = some (([],tail),labels) := by
    simpa only [List.append_nil,List.nil_append] using Parses.run visit parse [] []
  obtain ⟨seen,trace,legal,used⟩ := trace_of_run h n jobs bits [] tail labels good final
  have steps := used.trans time
  apply trace.evaluate fuel cap steps jobSize labelSize (fun j hj => bounded j (legal j hj)) small
  exact le_trans (by gcongr) room

/-- Fixed branching at strictly smaller layers supplies a weight independent of
the guessed payload. The depth of a sparse chronological branch is logarithmic. -/
theorem layer_weight {degree depth : ℕ} (jobs : List Job) (count : jobs.length ≤ degree)
    (earlier : ∀ j ∈ jobs, j.1.1.length < depth) :
    (jobs.map (fun j => (degree+1)^j.1.1.length)).sum < (degree+1)^depth := by
  cases depth with
  | zero =>
    cases jobs with
    | nil => simp
    | cons j js => exact False.elim (Nat.not_lt_zero _ (earlier j List.mem_cons_self))
  | succ n =>
    let weights := jobs.map (fun j => (degree+1)^j.1.1.length)
    have single (d) (hd : d ∈ weights) : d ≤ (degree+1)^n := by
      obtain ⟨j,mem,rfl⟩ := List.mem_map.mp hd
      exact Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_of_lt_succ (earlier j mem))
    have sum := List.sum_le_length_nsmul weights _ single
    have width : weights.length ≤ degree := by simpa only [weights,List.length_map] using count
    have total : weights.sum ≤ degree*((degree+1)^n) := sum.trans (Nat.mul_le_mul_right _ width)
    have strict := Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self degree) (Nat.pow_pos (n:=n) (Nat.succ_pos degree))
    exact total.trans_lt (strict.trans_eq (by rw [pow_succ,Nat.mul_comm]))

end OAI.Computability.MultitapeWeakETH.WitnessWalk
