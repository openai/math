import OAI.Computability.NearSquareRoot.ScheduleGeneratorSequenceRows
import OAI.Computability.NearSquareRoot.ScheduleGeneratorStackRows
import OAI.Computability.NearSquareRoot.ScheduleStagingPublish
import OAI.Computability.NearSquareRoot.ScheduleChunkWholeOutput

/-! # Effective transition tables for publication, fencing and output mirroring

These operations use fixed finite tables to transform the head symbols and commands.
Only the program-counter rank and the index of the source machine vary. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.EffectiveRows

open CommonAlphabet IntegerMultiplication TM Routing
variable {A I : Type} {Q : ℕ → Type} {a : Numbering A} {i : Numbering I}
    {q : ∀ j, Numbering (Q j)} {m : ∀ j, Rule A (Q j) I}

private abbrev X := ℕ × (ℕ × ℕ)
private theorem idx : Computable fun x : X => x.1 := Computable.fst
private theorem state : Computable fun x : X => x.2.1 := Computable.fst.comp Computable.snd
private theorem heads : Computable fun x : X => x.2.2 := Computable.snd.comp Computable.snd

/-- The mirror writes the filtered symbol to its fresh tape and follows the same movement. -/
theorem mirror (eff : EffectiveRows a i q m) (f : A → A) (out : I) :
    EffectiveRows a i.option q (fun j => ChunkWhole.Mirror.rule f out (m j)) := by
  obtain ⟨rows,hr,rc⟩ := eff
  let narrow := lookup (i.option.arrow a) fun read => ((i.arrow a).equiv fun k => read (some k)).val
  let expand := lookup (i.arrow (a.prod Numbering.move)) fun op =>
    ((i.option.arrow (a.prod Numbering.move)).equiv fun
        | none => (f (op out).1,(op out).2)
        | some k => op k).val
  let eval (j : ℕ) (p : ℕ × ℕ) := (rows j (p.1,narrow p.2)).map fun z => (z.1,expand z.2)
  refine ⟨eval,?_,?_⟩
  · exact Computable.option_map (hr.comp idx (state.pair ((primrec_lookup _ _).to_comp.comp heads)))
      ((Computable.fst.comp Computable.snd).pair ((primrec_lookup _ _).to_comp.comp
        (Computable.snd.comp Computable.snd)))
  · intro j s h
    simp only [eval,narrow,lookup_rank,rc,ChunkWhole.Mirror.rule]
    cases m j s (fun k => h (some k)) with
    | none => rfl
    | some z =>
      simp [expand,lookup_rank]
      apply congrArg (fun t => ((i.option.arrow (a.prod Numbering.move)).equiv t).val)
      funext k
      cases k <;> rfl

private def copyingMoves [DecidableEq I] (src : I) (bit : Bool → A) (b : Bool)
    (read : Option I → A) : Option I → A × Move
  | none => (bit b,.right)
  | some j => (read (some j),if j = src then .right else .stay)

/-- The additional publication phase begins after the source program halts. -/
theorem publish [DecidableEq I] (eff : EffectiveRows a i q m) (src : I)
    (decode : A → Option Bool) (bit : Bool → A) :
    EffectiveRows a i.option (fun j => (q j).option)
      (fun j => StagingPublish.rule (m j) src decode bit) := by
  obtain ⟨rows,hr,rc⟩ := eff
  let outer := i.option.arrow a
  let inner := i.arrow (a.prod Numbering.move)
  let actions := i.option.arrow (a.prod Numbering.move)
  let narrow := lookup outer fun h => ((i.arrow a).equiv fun k => h (some k)).val
  let live := lookup outer fun h => (decode (h (some src))).isSome.toNat
  let copy := lookup outer fun h => (actions.equiv
    (copyingMoves src bit ((decode (h (some src))).getD false) h)).val
  let extend := lookup₂ outer inner fun h op => (actions.equiv fun
    | none => (h none, Move.stay)
    | some k => op k).val
  let eval (j : ℕ) (p : ℕ × ℕ) :=
    bif decide (p.1 = 0) then
      bif decide (live p.2 = 0) then none else some (0,copy p.2)
    else
      some (((rows j (p.1-1,narrow p.2)).map (fun z => (z.1+1,extend p.2 z.2))).getD
        (0,holdRank a i.option p.2))
  refine ⟨eval,?_,?_⟩
  · have nar : Computable narrow := (primrec_lookup _ _).to_comp
    have li : Computable live := (primrec_lookup _ _).to_comp
    have cp : Computable copy := (primrec_lookup _ _).to_comp
    have ext : Computable₂ extend := (primrec_lookup₂ _ _ _).to_comp
    have stay : Computable (holdRank a i.option) := (primrec_lookup _ _).to_comp
    have call := hr.comp idx ((Primrec.nat_sub.to_comp.comp state (Computable.const 1)).pair (nar.comp heads))
    have put : Computable (fun x : X => (rows x.1 (x.2.1-1,narrow x.2.2)).map (fun z => (z.1+1,extend x.2.2 z.2))) := Computable.option_map call
      ((Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd)).pair
        (ext.comp (heads.comp Computable.fst) (Computable.snd.comp Computable.snd)))
    apply Computable.cond (Primrec.eq.decide.to_comp.comp state (Computable.const 0))
    · exact Computable.cond (Primrec.eq.decide.to_comp.comp (li.comp heads) (Computable.const 0))
        (Computable.const none) (Computable.option_some.comp ((Computable.const 0).pair (cp.comp heads)))
    · exact Computable.option_some.comp (Computable.option_getD put ((Computable.const 0).pair (stay.comp heads)))
  · intro j s h
    cases s with
    | none =>
      simp only [eval,StackRows.option_none,decide_true,Bool.cond_true,live,copy,outer,lookup_rank,StagingPublish.rule]
      cases decode (h (some src)) with
      | none => rfl
      | some b =>
        simp only [Option.isSome_some, Bool.toNat_true, Nat.one_ne_zero, decide_false,
          Bool.cond_false, Option.getD_some, Option.map_some, Option.some.injEq, Prod.mk.injEq,
          StackRows.option_none, true_and]
        apply congrArg (fun t => ((i.option.arrow (a.prod Numbering.move)).equiv t).val)
        funext k
        cases k <;> rfl
    | some s =>
      simp only [eval,StackRows.option_some,Nat.add_one_ne_zero,decide_false,Bool.cond_false,Nat.add_sub_cancel,
        narrow,outer,lookup_rank,rc,StagingPublish.rule]
      cases m j s (fun k => h (some k)) with
      | none => simp [holdRank,lookup_rank]
      | some z =>
        simp [extend,outer,inner,lookup₂_rank,actions]
        apply congrArg (fun t => ((i.option.arrow (a.prod Numbering.move)).equiv t).val)
        funext k
        cases k <;> rfl

/-- The active and aborted halves of the guarded state numbering have equal length. -/
theorem guard_false_rank {T : Type} (r : Numbering T) (t : T) :
    ((Numbering.bool.prod r).equiv (false,t)).val = (r.equiv t).val := by
  change (r.equiv t).val + r.size * 0 = _
  simp

theorem guard_true_rank {T : Type} (r : Numbering T) (t : T) :
    ((Numbering.bool.prod r).equiv (true,t)).val = (r.equiv t).val + r.size := by
  change (r.equiv t).val + r.size * 1 = _
  simp

/-- Fence checks use the source action and read vector, both over fixed finite banks. -/
theorem fence [Fintype I] (eff : EffectiveRows a i q m)
    (letters : Numbering (Uniform.Fence.Symbol A)) (size : Computable fun j => (q j).size) :
    EffectiveRows letters i (fun j => Numbering.bool.prod (q j)) (fun j => Uniform.Fence.guard (m j)) := by
  obtain ⟨rows,hr,rc⟩ := eff
  let outer := i.arrow letters
  let inner := i.arrow (a.prod Numbering.move)
  let actions := i.arrow (letters.prod Numbering.move)
  let narrow := lookup outer fun h => ((i.arrow a).equiv fun k => (h k).1).val
  let permit := lookup₂ outer inner fun h op => (decide (∀ k, Uniform.Fence.permits (h k).2 (op k).2 = true)).toNat
  let emit := lookup₂ outer inner fun h op => (actions.equiv fun k => (((op k).1,(h k).2),(op k).2)).val
  let eval (j : ℕ) (p : ℕ × ℕ) :=
    bif decide (p.1 < (q j).size) then
      (rows j (p.1,narrow p.2)).map fun z =>
        bif decide (permit p.2 z.2 = 0) then (p.1 + (q j).size,holdRank letters i p.2)
        else (z.1,emit p.2 z.2)
    else none
  refine ⟨eval,?_,?_⟩
  · have nar : Computable narrow := (primrec_lookup _ _).to_comp
    have chk : Computable₂ permit := (primrec_lookup₂ _ _ _).to_comp
    have put : Computable₂ emit := (primrec_lookup₂ _ _ _).to_comp
    have stay : Computable (holdRank letters i) := (primrec_lookup _ _).to_comp
    have call := hr.comp idx (state.pair (nar.comp heads))
    have num := size.comp idx
    have mask : Computable (fun t : X × (ℕ × ℕ) => permit t.1.2.2 t.2.2) := chk.comp (heads.comp Computable.fst) (Computable.snd.comp Computable.snd)
    apply Computable.cond (Primrec.nat_lt.decide.to_comp.comp state num) _ (Computable.const none)
    apply Computable.option_map call
    exact Computable.cond (Primrec.eq.decide.to_comp.comp mask (Computable.const 0))
      ((Primrec.nat_add.to_comp.comp (state.comp Computable.fst) (num.comp Computable.fst)).pair
        (stay.comp (heads.comp Computable.fst)))
      ((Computable.fst.comp Computable.snd).pair (put.comp (heads.comp Computable.fst)
        (Computable.snd.comp Computable.snd)))
  · rintro j ⟨flag,s⟩ h
    cases flag with
    | true =>
      simp [eval,guard_true_rank,Nat.not_lt_of_ge (Nat.le_add_left _ _),Uniform.Fence.guard]
    | false =>
      simp only [eval,guard_false_rank,((q j).equiv s).isLt,decide_true,Bool.cond_true,
        narrow,outer,lookup_rank,rc,Uniform.Fence.guard,Bool.false_eq_true,ite_false]
      cases ev : m j s (fun k => (h k).1) with
      | none => rfl
      | some z =>
        rcases z with ⟨target,op⟩
        by_cases ok : ∀ k, Uniform.Fence.permits (h k).2 (op k).2 = true
        · simp [permit,emit,outer,inner,actions,lookup₂_rank,ok,guard_false_rank]
        · simp [permit,outer,inner,lookup₂_rank,ok,guard_true_rank,holdRank,lookup_rank]

theorem size_fenced_publication (size : Computable fun j => (q j).size) :
    Computable fun j => (Numbering.bool.prod (q j).option).size :=
  Primrec.nat_mul.to_comp.comp (Computable.const 2) (Primrec.succ.to_comp.comp size)

theorem entry_fenced_publication (entry : ∀ j, Q j)
    (start : Computable fun j => ((q j).equiv (entry j)).val) :
    Computable fun j => ((Numbering.bool.prod (q j).option).equiv (false,some (entry j))).val := by
  simpa only [guard_false_rank,StackRows.option_some] using (Primrec.succ.to_comp.comp start)

end Generator.EffectiveRows

end NearSquareRoot
end Computability
end OAI
