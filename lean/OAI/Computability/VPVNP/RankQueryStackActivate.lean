import OAI.Computability.VPVNP.RankQueryStackEngineSpec
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord

/-! # Installing the six computed child words as the next live Schur query -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Engine.Activate

open RAMTape

variable {K : Type} [DecidableEq K]

/-- Live-frame slot for one of the six encoded query words, numbered one through six. -/
def querySlot (i : Fin 6) : Fin 10 := (Fin.castAdd 3 i).succ

private theorem querySlot_injective : Function.Injective querySlot := by
  intro a b h
  exact Fin.ext (Nat.succ.inj (congrArg Fin.val h))

private def copies (src : Fin 6 → K) (tmp : K) : List (Fin 6) → FiniteRoutine (Engine.Port K)
  | [] => .ret
  | i :: is => (copies src tmp is).followedBy
      (SuccessorFields.prependCopy (.aux (src i)) (.frame (.inl (querySlot i))) (.aux tmp))

/-- Copy the six pending query words into the live frame using a temporary stack. -/
def machine (src : Fin 6 → K) (tmp : K) := copies src tmp (List.finRange 6)

variable {n U Z : ℕ}

private def partialFields (w : ℕ) (q : Key n U Z) (ks : List (Fin 6)) : Data :=
  Fin.cons [] (Fin.append (fun i => if i ∈ ks then UniversalCountStack.digits w (q.words i) else []) ![[],[],[]])

private theorem addField (w : ℕ) (q : Key n U Z) (ks : List (Fin 6)) (i : Fin 6) :
    Function.update (partialFields w q ks) (querySlot i) (UniversalCountStack.digits w (q.words i)) =
      partialFields w q (i :: ks) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · rw [Function.update_of_ne (show 0 ≠ querySlot i from Fin.succ_ne_zero _ |>.symm)]
    rfl
  · refine Fin.addCases (motive := fun j => Function.update (partialFields w q ks) (querySlot i)
      (UniversalCountStack.digits w (q.words i)) j.succ = partialFields w q (i :: ks) j.succ)
      (fun x : Fin 6 => ?_) (fun x : Fin 3 => ?_) j
    · change Function.update _ (querySlot i) _ (querySlot x) = _
      by_cases h : x = i
      · subst x; rw [Function.update_self]; simp [partialFields]
      · rw [Function.update_of_ne (querySlot_injective.ne h)]
        simp [partialFields, querySlot, h]
    · have hne : (Fin.natAdd 6 x).succ ≠ querySlot i := by
        intro h; have := congrArg Fin.val h; simp [querySlot] at this; omega
      simp [partialFields, Function.update_of_ne hne]

private theorem setLive (l h : Data) (sig ret : List Bool) (aux : Stacks K) (i : Fin 10) (xs : List Bool) :
    Function.update (store l h sig ret aux) (.frame (.inl i)) xs = store (Function.update l i xs) h sig ret aux := by
  funext k; cases k with
  | frame j => cases j with
    | inl j => by_cases he : i = j <;> simp [he, store, Function.update]
    | inr => rfl
  | _ => rfl

private theorem copies_runs (src : Fin 6 → K) (tmp : K) (hne : ∀ i, src i ≠ tmp)
    (w : ℕ) (q : Key n U Z) (h : Data) (aux : Stacks K) (ht : aux tmp = [])
    (hs : ∀ i, aux (src i) = UniversalCountStack.digits w (q.words i))
    (ks : List (Fin 6)) (hn : ks.Nodup) :
    (copies src tmp ks).Runs (ks.length*(5*w+2)+1) (store (fun _ => []) h [] [] aux)
      (store (partialFields w q ks) h [] [] aux) := by
  induction ks with
  | nil =>
    have h0 : partialFields w q [] = fun _ => [] := by
      funext j; fin_cases j <;> rfl
    rw [h0]; simp only [List.length_nil, Nat.zero_mul, Nat.zero_add]; exact StackRuns.cons (.goto rfl) (.nil ..)
  | cons i ks ih =>
    let s := store (partialFields w q ks) h [] [] aux
    have hd : s (.frame (.inl (querySlot i))) = [] := by simp [s, store, partialFields, querySlot, hn.notMem]
    have step := SuccessorFields.prependCopy_runs (Engine.Port.aux (src i)) (.frame (.inl (querySlot i))) (.aux tmp)
      (by simp) (fun e => hne i (Engine.Port.aux.inj e)) (by simp) s ht
    change (SuccessorFields.prependCopy _ _ _).Runs (5*(aux (src i)).length+2) _ _ at step
    rw [show s (.aux (src i)) = UniversalCountStack.digits w (q.words i) from hs i, hs, hd,
      List.append_nil, UniversalCountStack.length_digits, setLive, addField] at step
    have both := FiniteRoutine.Runs.followedBy (ih hn.of_cons) step
    rw [show (i :: ks).length*(5*w+2)+1 = ks.length*(5*w+2)+1+(5*w+2) by simp only [List.length_cons]; ring]
    exact both

/-- Enter the pending child, preserving the full auxiliary register bank and
all ten encoded histories. -/
theorem machine_runs (src : Fin 6 → K) (tmp : K) (hne : ∀ i, src i ≠ tmp)
    {p e : ℕ} {c : SliceArithmetic.Vector p e} (w v : ℕ) (q : Key n U Z) (fs : List (F n U Z c)) (aux : Stacks K)
    (ht : aux tmp = []) (hs : ∀ i, aux (src i) = UniversalCountStack.digits w (q.words i)) :
    (machine src tmp).Runs (6*(5*w+2)+1) (store (fun _ => []) (history w v fs) [] [] aux)
      (atControl w v (.enter q) fs aux) := by
  have he : partialFields w q (List.finRange 6) = fields w [] q [] [] [] := by
    simp [partialFields, fields]
  simpa only [machine, List.length_finRange, atControl, live, output, he] using
    copies_runs src tmp hne w q (history w v fs) aux ht hs (List.finRange 6) (List.nodup_finRange 6)

end RankQuery.Stack.Engine.Activate

end VPVNP
end Computability
end OAI
