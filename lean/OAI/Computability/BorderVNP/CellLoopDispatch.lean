import OAI.Computability.BorderVNP.CellLoopIteration

/-! # The physical sparse repeat instruction -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.Generator.Loop

open VPVNP.RAMTape RationalHitting.StackLanguage

private def limitPorts : IO → Ports
  | .row => .inr .limit
  | .env => .inl .env
  | .out => .inl .out

private theorem limitPorts_inj : Function.Injective limitPorts := by
  intro i j h; cases i <;> cases j <;> simp_all [limitPorts]

/-- Loop payload stores one expression and just one body, irrespective of the bound. -/
def payload (expr body : List Bool) := codeWord expr ++ body

/-- Actual private repeat dispatcher, including expression evaluation, index update and
release of every retained input and work word. -/
def dispatch (evaluator child : Fragment IO) : Fragment IO := Fragment.hide <|
  (Fragment.split (.inl .row) (.inr .limit)).seq <|
  (evaluator.mount limitPorts).seq <|
  (loopBound (.inr .limit) (.inr .remaining)).seq <|
  (Fragment.each (.inr .remaining) (iteration child)).seq <|
  (Fragment.erase (.inr .index)).seq (Fragment.erase (.inl .row))

private def baseFrame (body env out : List Bool) (i n : ℕ) : Frame :=
  {row := body,env := env,out := out,index := i.bits,remaining := List.replicate n true}

/-- Dynamic time of the repeat sweep with actual child costs; empty loops still check the
end marker. -/
def sweepCost (body env : List Bool) (cost : ℕ → ℕ) (i : ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => 1 + (overhead body env i + cost i) + sweepCost body env cost (i+1) n

/-- Chronological concatenation over consecutive ordinal numbers. -/
def emittedRange (emit : ℕ → List Bool) (i : ℕ) : ℕ → List Bool
  | 0 => []
  | n+1 => emit i ++ emittedRange emit (i+1) n

/-- Starting at zero, the native ascending loop visits exactly the pure generator's
ordinal list. -/
theorem emittedRange_zero (emit : ℕ → List Bool) (n : ℕ) :
    emittedRange emit 0 n = (List.range n).flatMap emit := by
  have h (i n : ℕ) : emittedRange emit i n = (List.range' i n).flatMap emit := by
    induction n generalizing i with
    | zero => rfl
    | succ n ih => simp only [emittedRange, List.range'_succ, List.flatMap_cons, ih]
  rw [List.range_eq_range']; exact h 0 n

private theorem sweep_run (child : Fragment IO) (body env out : List Bool) (emit : ℕ → List Bool)
    (cost : ℕ → ℕ) (i n : ℕ)
    (h : ∀ j, i ≤ j → j < i+n → ∀ acc, ∃ t ≤ cost j, child.Runs t
      (io body (codeWord j.bits ++ env) acc) (io [] (codeWord j.bits ++ env) ((emit j).reverse ++ acc))) :
    ∃ t ≤ sweepCost body env cost i n,
      (Fragment.each (.inr .remaining) (iteration child)).Runs t (baseFrame body env out i n).store
        (baseFrame body env ((emittedRange emit i n).reverse ++ out) (i+n) 0).store := by
  induction n generalizing i out with
  | zero =>
    exact ⟨1, le_rfl, Fragment.each_empty _ _ _ rfl⟩
  | succ n ih =>
    obtain ⟨d,hd,hc⟩ := h i le_rfl (by omega) out
    obtain ⟨u,hu,hr⟩ := iteration_run child body env out ((emit i).reverse ++ out) (List.replicate n true) i hc
    obtain ⟨v,hv,ht⟩ := ih ((emit i).reverse ++ out) (i+1) (fun j hj hj' => h j (by omega) (by omega))
    refine ⟨1+u+v, ?_, ?_⟩
    · rw [sweepCost]; omega
    · simp only [emittedRange, List.reverse_append, List.append_assoc, show i+(n+1) = i+1+n by omega]
      apply Fragment.each_cons (u := (baseFrame body env ((emit i).reverse ++ out) (i+1) n).store)
        (rest := List.replicate n true) (by simp [baseFrame,Frame.store,List.replicate_succ]) _ ht
      rw [Frame.update_store]
      exact hr

/-- Decoding and releasing the preserved body and bounds. -/
def overheadDispatch (expr body : List Bool) (n : ℕ) : ℕ :=
  2*(7*expr.length+10) + (7*n+8)*n.bits.length+3 + 2*(2*n.bits.length+1) + 2*(2*body.length+1)

/-- The actual repeat instruction emits the concatenated private bytecode for all copies.
Expression time and child time refer to checked executions of the installed fragments. -/
theorem dispatch_run (evaluator child : Fragment IO) (expr body env out : List Bool)
    (n : ℕ) (emit : ℕ → List Bool) (cost : ℕ → ℕ) {e : ℕ}
    (he : evaluator.Runs e (io expr env out) (io n.bits env out))
    (hc : ∀ j < n, ∀ acc, ∃ t ≤ cost j, child.Runs t
      (io body (codeWord j.bits ++ env) acc) (io [] (codeWord j.bits ++ env) ((emit j).reverse ++ acc))) :
    ∃ t ≤ overheadDispatch expr body n + e + sweepCost body env cost 0 n,
      (dispatch evaluator child).Runs t (io (payload expr body) env out)
        (io [] env (((List.range n).flatMap emit).reverse ++ out)) := by
  let f : Frame := {row := payload expr body,env := env,out := out}
  let f₁ : Frame := {f with row := body, limit := expr}
  let f₂ : Frame := {f₁ with limit := n.bits}
  let newOut := ((List.range n).flatMap emit).reverse ++ out
  let f₃ := baseFrame body env newOut n 0
  obtain ⟨a,ha,ra⟩ := Fragment.split_run (src := (Sum.inl IO.row : Ports)) (dst := .inr .limit)
    (by simp) f.store expr body rfl rfl
  rw [Frame.update_store,Frame.update_store] at ra
  have rb : (evaluator.mount limitPorts).Runs e f₁.store f₂.store := by
    apply evaluator.runs_mount limitPorts_inj he
    · intro j; cases j <;> rfl
    · intro j; cases j <;> rfl
    · rintro (j|j) hj <;> cases j <;> first | rfl | exact (hj .row rfl).elim
  obtain ⟨b,hb,rc⟩ := loopBound_run (src := (Sum.inr Aux.limit : Ports)) (dst := .inr .remaining)
    (by simp) f₂.store n rfl rfl
  rw [Frame.update_store,Frame.update_store] at rc
  obtain ⟨d,hd,rd⟩ := sweep_run child body env out emit cost 0 n (fun j _ hj => hc j (by omega))
  rw [emittedRange_zero, Nat.zero_add] at rd
  obtain ⟨g,hg,rg⟩ := Fragment.erase_run (.inr .index) f₃.store
  rw [Frame.update_store] at rg
  obtain ⟨k,hk,rk⟩ := Fragment.erase_run (.inl .row) (baseFrame body env newOut 0 0).store
  rw [Frame.update_store] at rk
  refine ⟨a+(e+(b+(d+(g+k)))), ?_, ?_⟩
  · change g ≤ 2*(2*n.bits.length+1) at hg
    change k ≤ 2*(2*body.length+1) at hk
    unfold overheadDispatch; omega
  · have hi : f.store = Sum.elim (io (payload expr body) env out) (fun _ => []) := by
      funext k; rcases k with k|k <;> cases k <;> rfl
    have ho : ((baseFrame body env newOut 0 0).set (.inl .row) []).store =
        Sum.elim (io [] env newOut) (fun _ => []) := by
      funext k; rcases k with k|k <;> cases k <;> rfl
    rw [hi] at ra
    rw [ho] at rk
    apply Fragment.runs_hide
    exact Fragment.runs_seq _ _ ra (Fragment.runs_seq _ _ rb (Fragment.runs_seq _ _ rc
      (Fragment.runs_seq _ _ rd (Fragment.runs_seq _ _ rg rk))))

end CellMacro.Generator.Loop

end BorderVNP
end Computability
end OAI
