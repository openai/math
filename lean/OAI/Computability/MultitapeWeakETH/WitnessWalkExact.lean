import OAI.Computability.MultitapeWeakETH.WitnessWalk

/-! # Exact recognition of depth-first witness forests -/

namespace OAI.Computability.MultitapeWeakETH.WitnessWalk

open IntegerMultiplication Code
variable {D : Type} {visit : Visit D} {ctx : D}

/-- Splitting the initial pending forest also splits the consumed time and
coefficient sequence, with the same intermediate suffix on the two sides. -/
private theorem split_forest {jobs bits steps tail labels}
    (h : Parses visit ctx jobs bits steps tail labels) (left right : List Job) (he : jobs = left ++ right) :
    ∃ k₁ k₂ middle l₁ l₂, Parses visit ctx left bits k₁ middle l₁ ∧
      Parses visit ctx right middle k₂ tail l₂ ∧ steps = k₁+k₂ ∧ labels = l₁++l₂ := by
  induction h generalizing left right with
  | nil bits =>
    obtain ⟨rfl,rfl⟩ := List.append_eq_nil_iff.mp he.symm
    exact ⟨0,0,bits,[],[],.nil _,.nil _,rfl,rfl⟩
  | @cons j js bits children next own kc afterChild lc ks final ls node child siblings ihc ihs =>
    cases left with
    | nil =>
      change j::js = right at he
      subst right
      exact ⟨0,_,bits,[],_,.nil _,.cons node child siblings,(Nat.zero_add _).symm,rfl⟩
    | cons v vs =>
      obtain ⟨rfl,eq⟩ := List.cons.inj he
      obtain ⟨k₁,k₂,middle,l₁,l₂,first,second,time,words⟩ := ihs vs right eq
      exact ⟨_,k₂,middle,_,l₂,.cons node child first,second,by omega,by simp only [words,List.append_assoc]⟩

private theorem none_iter (fuel : ℕ) : (advance visit ctx)^[fuel] none = none := by
  induction fuel with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,advance_none]

/-- Reaching an empty frontier certifies a parse of precisely the starting
forest. Padding the clock after the last site introduces no choices or labels. -/
theorem run_sound (fuel : ℕ) (jobs : List Job) (bits tail : Bits.Word) (prefixLabels out : List Tally)
    (accept : (advance visit ctx)^[fuel] (some ((jobs,bits),prefixLabels)) = some (([],tail),out)) :
    ∃ steps ≤ fuel, ∃ labels, Parses visit ctx jobs bits steps tail labels ∧ out = prefixLabels ++ labels := by
  induction fuel generalizing jobs bits prefixLabels with
  | zero =>
    change some ((jobs,bits),prefixLabels) = some (([],tail),out) at accept
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := Prod.mk.inj (Option.some.inj accept) |>.imp_left Prod.mk.inj
    exact ⟨0,le_rfl,[],.nil _,(List.append_nil _).symm⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply] at accept
    cases jobs with
    | nil =>
      rw [advance_done] at accept
      obtain ⟨steps,time,labels,parse,endLabels⟩ := ih _ _ _ accept
      exact ⟨steps,time.trans (Nat.le_succ _),labels,parse,endLabels⟩
    | cons j js =>
      rw [advance_cons] at accept
      cases e : visit ((ctx,j),bits) with
      | none =>
        simp only [e,Option.map_none,none_iter] at accept
        contradiction
      | some v =>
        rcases v with ⟨⟨children,next⟩,own⟩
        simp only [e,Option.map_some] at accept
        obtain ⟨steps,time,labels,parse,endLabels⟩ := ih _ _ _ accept
        obtain ⟨kc,ks,middle,lc,ls,child,siblings,eqK,eqL⟩ := split_forest parse children js rfl
        exact ⟨_,by omega,_,.cons e child siblings,by simp only [endLabels,eqL,List.append_assoc]⟩

end OAI.Computability.MultitapeWeakETH.WitnessWalk
