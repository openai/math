import OAI.Computability.BorderVNP.FiniteTeamReplay
import OAI.Computability.BorderVNP.FiniteOutputProduct
import OAI.Computability.BorderVNP.TeamLink

/-! # Bijection on physical choice tapes under field instrumentation

The field accumulator changes only the next control label. Supplying the same
choice bits to the original and augmented stack programs yields identical
stacks and elapsed time, and one uniquely determined final field element.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldStack

open VPVNP.RAMTape TeamPrivateFragment
open private step_unique from OAI.Computability.BorderVNP.TeamContractionReplayRun
variable {K Q : Type} [DecidableEq K] {F : Type*} [Field F] [Fintype F]

omit [DecidableEq K] in
private theorem replay_row (c : StackCode K Q) (w : Q → F) (q : Q) (bs : List Bool) (acc : F) :
    replay (productCode c w) ((q,Fintype.equivFin F acc),bs) =
      (replay c (q,bs)).rename id (fun z => ((z.1,Fintype.equivFin F (acc*w q)),z.2)) := by
  cases op : c q with
  | choose l h => cases bs with
    | nil => simp [replay,productCode,op,StackOp.rename]
    | cons b bs => cases b <;> simp [replay,productCode,op,StackOp.rename]
  | _ => simp [replay,productCode,op,StackOp.rename,Function.comp_def]

private theorem lift_step (c : StackCode K Q) (w : Q → F) {q s u out}
    (h : StackStep (replay c) q s u out) (acc : F) :
    StackStep (replay (productCode c w)) ((q.1,Fintype.equivFin F acc),q.2) s
      ((u.1,Fintype.equivFin F (acc*w q.1)),u.2) out := by
  cases h with
  | push h => exact .push (by rw [replay_row,h]; rfl)
  | @pop k f h =>
    exact .pop (k := k) (f := fun b => (((f b).1,Fintype.equivFin F (acc*w q.1)),(f b).2))
      (by rw [replay_row,h]; rfl)
  | goto h => exact .goto (by rw [replay_row,h]; rfl)

/-- Every replay on the original program has a field-augmented replay with exactly
the same steps, consumed choice suffix and stack contents. -/
theorem replay_lift (c : StackCode K Q) (w : Q → F) {q s u out t}
    (h : StackRuns (replay c) t q s u out) (acc : F) :
    ∃ v : F, StackRuns (replay (productCode c w)) t ((q.1,Fintype.equivFin F acc),q.2) s
      ((u.1,Fintype.equivFin F v),u.2) out := by
  induction h generalizing acc with
  | nil => exact ⟨acc,.nil ..⟩
  | cons step _ ih =>
    obtain ⟨v,tail⟩ := ih (acc * w _)
    exact ⟨v,.cons (lift_step c w step acc) tail⟩

/-- Forgetting the finite control's accumulator recovers the literal original replay. -/
theorem replay_project (c : StackCode K Q) (w : Q → F) {q s u out t bs rest v v'}
    (h : StackRuns (replay (productCode c w)) t ((q,v),bs) s ((u,v'),rest) out) :
    StackRuns (replay c) t (q,bs) s (u,rest) out := by
  have lift := TeamLink.replay_lift h c id Function.injective_id Prod.fst s (by
    rintro ⟨z,i⟩ _
    simp only [productCode]
    cases c z <;> rfl)
  have same (b : Stacks K) : installStacks id s b = b := funext fun i => installStacks_at Function.injective_id s b i
  simpa only [same] using lift

private theorem same_end {R : Type} {C : StackCode K R} {t q s u v out out'}
    (h : StackRuns C t q s u out) (h' : StackRuns C t q s v out') : u = v ∧ out = out' := by
  induction h with
  | nil => cases h'; exact ⟨rfl,rfl⟩
  | cons step _ ih =>
    cases h' with
    | cons step' tail =>
      have eq : _ ∧ _ := show _ from step_unique step step'
      obtain ⟨rfl,rfl⟩ := eq
      exact ih tail

/-- There is a bijection on bounded executions and the final accumulator is
unique even when it is zero. No additional choice tape is required. -/
theorem replay_unique_iff (c : StackCode K Q) (w : Q → F) (t : ℕ) (q u : Q) (bs rest : List Bool)
    (s out : Stacks K) (acc : F) :
    (∃! v : F, StackRuns (replay (productCode c w)) t ((q,Fintype.equivFin F acc),bs) s
      ((u,Fintype.equivFin F v),rest) out) ↔ StackRuns (replay c) t (q,bs) s (u,rest) out := by
  constructor
  · rintro ⟨v,h,_⟩; exact replay_project c w h
  · intro h
    obtain ⟨v,hv⟩ := replay_lift c w h acc
    refine ⟨v,hv,?_⟩
    intro u hu
    apply (Fintype.equivFin F).injective
    exact congrArg (fun z => z.1.2) (same_end hu hv).1

omit [DecidableEq K] in
private theorem halt_iff (c : StackCode K Q) (w : Q → F) (q : Q) (v : Fin (Fintype.card F)) :
    productCode c w (q,v) = .halt true ↔ c q = .halt true := by
  cases op : c q <;> simp [productCode,op]

/-- The accepting field leaves and signed leaves have precisely the same physical
choice tapes at the same clock. -/
theorem accepting_choices_iff (c : StackCode K Q) (w term : Q → F) (neg : Q → Bool)
    (t : ℕ) (q : Q) (s : Stacks K) (bs : List Bool) (acc : F) :
    (∃ v, (bs,v) ∈ FieldReplay.leaves (productCode c w) (productOutput w term) t (q,Fintype.equivFin F acc) s) ↔
      ∃ sg, (bs,sg) ∈ TeamContraction.Replay.leaves c neg t q s := by
  constructor
  · rintro ⟨v,hv⟩
    obtain ⟨k,hk,⟨u,acc'⟩,out,run,halt,_⟩ := (FieldReplay.mem_leaves_iff ..).mp hv
    exact ⟨neg u,(TeamContraction.Replay.mem_leaves_iff ..).mpr ⟨k,hk,u,out,replay_project c w run,
      (halt_iff ..).mp halt,rfl⟩⟩
  · rintro ⟨sg,hm⟩
    obtain ⟨k,hk,u,out,run,halt,_⟩ := (TeamContraction.Replay.mem_leaves_iff ..).mp hm
    obtain ⟨v,hr⟩ := replay_lift c w run acc
    exact ⟨_,(FieldReplay.mem_leaves_iff ..).mpr ⟨k,hk,_,out,hr,(halt_iff ..).mpr halt,rfl⟩⟩

/-- Match each original signed accepting leaf with the unique instrumented leaf
having exactly the same physical choice tape. -/
noncomputable def leafEquiv (c : StackCode K Q) (w term : Q → F) (neg : Q → Bool)
    (t : ℕ) (q : Q) (s : Stacks K) (acc : F) :
    ↥(TeamContraction.Replay.leaves c neg t q s) ≃
    ↥(FieldReplay.leaves (productCode c w) (productOutput w term) t (q,Fintype.equivFin F acc) s) := by
  let forward (x : ↥(TeamContraction.Replay.leaves c neg t q s)) :=
    (accepting_choices_iff c w term neg t q s x.val.1 acc).mpr ⟨x.val.2,x.property⟩
  let backward (x : ↥(FieldReplay.leaves (productCode c w) (productOutput w term) t (q,Fintype.equivFin F acc) s)) :=
    (accepting_choices_iff c w term neg t q s x.val.1 acc).mp ⟨x.val.2,x.property⟩
  refine { toFun := fun x => ⟨(x.val.1,(forward x).choose),(forward x).choose_spec⟩
           invFun := fun x => ⟨(x.val.1,(backward x).choose),(backward x).choose_spec⟩
           left_inv := ?_
           right_inv := ?_ }
  · intro x
    apply Subtype.ext
    apply Prod.ext
    · rfl
    exact TeamContraction.Replay.sign_unique c neg t q s x.val.1 (backward ⟨(x.val.1,(forward x).choose),(forward x).choose_spec⟩).choose_spec x.property
  · intro x
    apply Subtype.ext
    apply Prod.ext
    · rfl
    exact FieldReplay.output_unique _ _ _ _ _ x.val.1 (forward ⟨(x.val.1,(backward x).choose),(backward x).choose_spec⟩).choose_spec x.property

/-- Matching leaves preserves the entire consumed bit list. -/
theorem leafEquiv_choices (c : StackCode K Q) (w term : Q → F) (neg : Q → Bool)
    (t : ℕ) (q : Q) (s : Stacks K) (acc : F) (x : ↥(TeamContraction.Replay.leaves c neg t q s)) :
    ((leafEquiv c w term neg t q s acc) x).val.1 = x.val.1 := rfl

end FieldStack

end BorderVNP
end Computability
end OAI
