import OAI.Computability.BorderVNP.FiniteProcessorWeightSegments

/-! # Accumulated field products along native private paths

All choices of a bounded native path replay on the same input and at the
original elementary clock. Its sole field update occurs at the native halt,
before the private workspace is cleared.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldProcessor

open VPVNP.RAMTape TeamSite TeamPrivateTape TeamPrivateFragment
open private ambient from OAI.Computability.BorderVNP.TeamPrivateValue

variable {Q Γ : Type} {m g d : ℕ} {F : Type*} [Field F] [Fintype F]

/-- Decode the arbitrary field value on the synchronized native bit tracks. -/
def trackReturn (T : Table Q d) (w : Q → (Fin d → Bool) → Bool → F) :
    ℕ → Q → (Fin d → Track) → List Bool → Option F
  | 0, _, _, _ => none
  | f+1, q, ts, bs => match T q (heads ts) with
    | .halt ok neg => if ok && bs.isEmpty then some (w q (heads ts) neg) else none
    | .one c => trackReturn T w f c.next (c.apply ts) bs
    | .two l h => match bs with
      | [] => none
      | b :: tail => let c := if b then h else l; trackReturn T w f c.next (c.apply ts) tail

omit [Field F] [Fintype F] in
/-- The field-valued native observation is the same on symbol tapes and their synchronized tracks. -/
theorem trackReturn_eq (M : Macro Q Γ m g) (w : FieldSelect.Return Q Γ F m)
    (f : ℕ) (q : Q) (ts : Fin m → SymbolTape Γ) (bs : List Bool) :
    trackReturn (trackTable M.alphabet M.table) (fun q h b => w q (symbols M.alphabet h) b)
      f q (tracks M.alphabet ts) bs =
      FieldSelect.nativeReturn M.table M.alphabet.blank w f q ts bs := by
  induction f generalizing q ts bs with
  | zero => rfl
  | succ f ih =>
    have sym := symbols_tracks M.alphabet ts
    change (fun i : Fin m => M.alphabet.read (fun j => heads (tracks M.alphabet ts) (finProdFinEquiv (i,j)))) =
      (fun i => (ts i).head) at sym
    cases h : M.table q (fun i => (ts i).head) with
    | halt ok sg => simp only [trackReturn,FieldSelect.nativeReturn,trackTable,sym,h,symbols_tracks]
    | one c => simp only [trackReturn,FieldSelect.nativeReturn,trackTable,sym,h,tracks_apply]; exact ih ..
    | two l r =>
      cases bs with
      | nil => simp only [trackReturn,FieldSelect.nativeReturn,trackTable,sym,h]
      | cons b bs =>
        cases b <;> simp only [trackReturn,FieldSelect.nativeReturn,trackTable,sym,h,Bool.false_eq_true,
          ite_false,ite_true,tracks_apply] <;> exact ih ..

/-- The adjustment applied at the unique native terminal. A native rejection
keeps the field accumulator while the original signed validator records rejection. -/
def adjustment (out : Option Bool) (ret : Option F) : F :=
  match out,ret with
  | some sg, some v => signed sg v
  | _, _ => 1

theorem ready_run (M : Macro Q Γ m g) (w : FieldSelect.Return Q Γ F m)
    {n q t bs out u} (h : Run (trackTable M.alphabet M.table) n q t bs out u) (fuel : ℕ) (hf : n < fuel)
    (acc : F) (suffix : List Bool) :
    let ret := trackReturn (trackTable M.alphabet M.table) (fun q h b => w q (symbols M.alphabet h) b) fuel q t bs
    StackRuns (replay (privateCode M w)) (n*(2*(m*g)+2)+1+TeamPrivateCleanup.steps (bank u))
      ((.run (.inl (.ready q (heads t))),Fintype.equivFin F acc),bs++suffix) (ambient t)
      ((.result out,Fintype.equivFin F (acc * adjustment out ret)),suffix) (fun _ => []) := by
  induction h generalizing fuel with
  | @stop q t ok sg op =>
    cases fuel with
    | zero => omega
    | succ f =>
      let out := if ok then some sg else none
      let delta := if ok then signed sg (w q (symbols M.alphabet (heads t)) sg) else 1
      have row : privateCode M w (.run (.inl (.ready q (heads t))),Fintype.equivFin F acc) =
          .goto (.run (.inr (out,(TeamPrivateCleanup.all (Port (m*g))).body.entry)),Fintype.equivFin F (acc*delta)) := by
        cases ok <;> simp [privateCode,FieldStack.productCode,privateFactor,TeamPrivateCompiler.code,
          TeamPrivateFragment.rows,TeamPrivateTape.code,TeamPrivateTape.negative,op,delta,out,StackOp.rename]
      have r := replay_segment (cleanup M w out t (acc*delta)) suffix
      have first := StackRuns.cons (StackStep.goto (q := ((.run (.inl (.ready q (heads t))),Fintype.equivFin F acc),suffix)) (by simp [replay,row])) r
      cases ok <;> simpa only [trackReturn,op,adjustment,Bool.false_and,Bool.true_and,List.isEmpty_nil,
        Bool.false_eq_true,ite_false,ite_true,Nat.zero_mul,Nat.zero_add,List.nil_append,Nat.add_comm 1,
        delta,out,mul_one] using first
  | @one q t c n bs out u op _ ih =>
    cases fuel with
    | zero => omega
    | succ f =>
      have row : privateCode M w (.run (.inl (.ready q (heads t))),Fintype.equivFin F acc) =
          .goto (.run (.inl (.sweep c 0 (heads t))),Fintype.equivFin F acc) := by
        simp [privateCode,FieldStack.productCode,privateFactor,TeamPrivateCompiler.code,TeamPrivateFragment.rows,
          TeamPrivateTape.code,op,StackOp.rename]
      have tail := (replay_segment (sweep M w c t acc) (bs++suffix)).trans (ih f (by omega))
      rw [show (n+1)*(2*(m*g)+2)+1+TeamPrivateCleanup.steps (bank u) =
        ((2*(m*g)+1)+(n*(2*(m*g)+2)+1+TeamPrivateCleanup.steps (bank u)))+1 by ring]
      simpa only [trackReturn,op] using StackRuns.cons (StackStep.goto (by simp [replay,row])) tail
  | @two q t l r n bs out u b op _ ih =>
    cases fuel with
    | zero => omega
    | succ f =>
      let c := if b then r else l
      have row : privateCode M w (.run (.inl (.ready q (heads t))),Fintype.equivFin F acc) =
          .choose (.run (.inl (.sweep l 0 (heads t))),Fintype.equivFin F acc)
            (.run (.inl (.sweep r 0 (heads t))),Fintype.equivFin F acc) := by
        simp [privateCode,FieldStack.productCode,privateFactor,TeamPrivateCompiler.code,TeamPrivateFragment.rows,
          TeamPrivateTape.code,op,StackOp.rename]
      have tail := (replay_segment (sweep M w c t acc) (bs++suffix)).trans (ih f (by omega))
      rw [show (n+1)*(2*(m*g)+2)+1+TeamPrivateCleanup.steps (bank u) =
        ((2*(m*g)+1)+(n*(2*(m*g)+2)+1+TeamPrivateCleanup.steps (bank u)))+1 by ring]
      simp only [trackReturn,op]
      apply StackRuns.cons _ tail
      apply StackStep.goto
      cases b <;> simp [replay,row,c]

/-- The entire field-instrumented private execution starts at raw input and ends
with cleared stacks. It has the same clock and consumes precisely the same bits
as the native private path, with its real symbol-level value in the accumulator. -/
theorem private_run (M : Macro Q Γ m g) (w : FieldSelect.Return Q Γ F m) (raw : List Bool)
    {n choices out u} (h : Run (trackTable M.alphabet M.table) n M.start
      (tracks M.alphabet (input M.alphabet.blank M.digit M.inputTape raw)) choices out u)
    (fuel : ℕ) (hf : n < fuel) (acc : F) (suffix : List Bool) :
    let ret := FieldSelect.nativeReturn M.table M.alphabet.blank w fuel M.start
      (input M.alphabet.blank M.digit M.inputTape raw) choices
    StackRuns (replay (privateCode M w))
      (TeamPrivateInput.steps g raw + (n*(2*(m*g)+2)+1+TeamPrivateCleanup.steps (bank u)))
      ((.load .start,Fintype.equivFin F acc),choices++suffix) (TeamPrivateInput.initial raw)
      ((.result out,Fintype.equivFin F (acc * adjustment out ret)),suffix) (fun _ => []) := by
  have hrun := ready_run M w h fuel hf acc suffix
  dsimp only at hrun ⊢
  rw [trackReturn_eq] at hrun
  exact (replay_segment (load M w raw acc) (choices++suffix)).trans hrun

end FieldProcessor

end BorderVNP
end Computability
end OAI
