import OAI.Computability.NearSquareRoot.CommonAlphabetPublicNumbering
import OAI.Computability.NearSquareRoot.ScheduleGeneratorStackFormula
import OAI.Computability.IntegerMultiplication.SM.Stack

/-! # Numeric transition rows of the physical stack-machine compiler -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.StackRows

open IntegerMultiplication CommonAlphabet
variable {A Q I : Type}

def action (a : Numbering A) : Numbering (SM.Action A) :=
  Numbering.ofEquiv
    { toFun := fun | .skip => none | .pop => some none | .push x => some (some x)
      invFun := fun | none => .skip | some none => .pop | some (some x) => .push x
      left_inv := by intro x; cases x <;> rfl
      right_inv := by rintro (_ | (_ | _)) <;> rfl } a.option.option

/-- Runnable source state, or an intermediate holding its destination and the
tuple of pending stack commands. -/
def pc (a : Numbering A) (q : Numbering Q) (i : Numbering I) : Numbering (SM.PC A Q I) :=
  q.sum (q.prod (i.arrow (action a)))

@[simp] theorem option_none (a : Numbering A) : (a.option.equiv none).val = 0 := by
  change ((finSuccEquiv a.size).symm none).val = 0
  simp

@[simp] theorem option_some (a : Numbering A) (x : A) :
    (a.option.equiv (some x)).val = (a.equiv x).val+1 := by
  change ((finSuccEquiv a.size).symm (some (a.equiv x))).val = _
  simp

@[simp] theorem action_skip (a : Numbering A) : ((action a).equiv .skip).val = 0 := by
  change (a.option.option.equiv none).val = _
  simp

@[simp] theorem action_pop (a : Numbering A) : ((action a).equiv .pop).val = 1 := by
  change (a.option.option.equiv (some none)).val = _
  simp

@[simp] theorem action_push (a : Numbering A) (x : A) : ((action a).equiv (.push x)).val = (a.equiv x).val+2 := by
  change (a.option.option.equiv (some (some x))).val = _
  simp

private theorem commandRank (a : Numbering A) (v : Option A) (m : TM.Move) :
    ((a.option.prod Numbering.move).equiv (v,m)).val =
      (Numbering.move.equiv m).val + 3*(a.option.equiv v).val := rfl

theorem first_eq (a : Numbering A) (op : SM.Action A) (top : Option A) :
    first ((action a).equiv op).val (a.option.equiv top).val =
      ((a.option.prod Numbering.move).equiv (op.first top)).val := by
  cases op <;> cases top <;> simp only [SM.Action.first,commandRank] <;> simp [first,Numbering.move]
  all_goals rfl

theorem second_eq (a : Numbering A) (op : SM.Action A) (top : Option A) :
    second ((action a).equiv op).val (a.option.equiv top).val =
      ((a.option.prod Numbering.move).equiv (op.second top)).val := by
  cases op <;> simp only [SM.Action.second,commandRank] <;> simp [second,Numbering.move]
  all_goals rfl

private theorem cmds_eq (a : Numbering A) (i : Numbering I)
    (f : ℕ → ℕ → ℕ) (g : SM.Action A → Option A → Option A × TM.Move)
    (h : ∀ op top, f ((action a).equiv op).val (a.option.equiv top).val =
      ((a.option.prod Numbering.move).equiv (g op top)).val)
    (actions : I → SM.Action A) (top : I → Option A) :
    cmds f a.size i.size ((i.arrow (action a)).equiv actions).val ((i.arrow a.option).equiv top).val =
      ((i.arrow (a.option.prod Numbering.move)).equiv (fun x => g (actions x) (top x))).val := by
  unfold cmds
  rw [← Numbering.encodeBase_arrow i (a.option.prod Numbering.move) (fun x => g (actions x) (top x))]
  have range : (List.finRange i.size).map Fin.val = List.range i.size := by
    apply List.ext_getElem <;> simp
  rw [← range, Numbering.all, List.map_map, List.map_map]
  apply congrArg (Numbering.encodeBase ((a.size+1)*3))
  apply List.map_congr_left
  intro k _
  let x := i.equiv.symm k
  have aDigit := Numbering.digit_arrow i (action a) actions x
  have tDigit := Numbering.digit_arrow i a.option top x
  simp only [x, Equiv.apply_symm_apply] at aDigit tDigit
  exact (congrArg₂ f aDigit tDigit).trans (h _ _)

/-- Encoded source step: the action vector is an `(a.size+2)`-ary number,
and the input tops form an `(a.size+1)`-ary number on exactly `i.size` tapes. -/
def Sources (a : Numbering A) (q : Numbering Q) (i : Numbering I) (m : SM.Rule A Q I)
    (orig : ℕ × ℕ → Option (ℕ × ℕ)) : Prop := ∀ s top,
  orig ((q.equiv s).val,((i.arrow a.option).equiv top).val) =
    (m s top).map fun z => ((q.equiv z.1).val,((i.arrow (action a)).equiv z.2).val)

/-- The effective row function computes exactly `SM.toTM m`, including
halting branches in the first phase and every pending write in the second. -/
theorem row_eq (a : Numbering A) (q : Numbering Q) (i : Numbering I) (m : SM.Rule A Q I)
    (orig : ℕ × ℕ → Option (ℕ × ℕ)) (source : Sources a q i m orig)
    (s : SM.PC A Q I) (top : I → Option A) :
    row a.size q.size i.size orig (((pc a q i).equiv s).val,((i.arrow a.option).equiv top).val) =
      (SM.toTM m s top).map fun z => (((pc a q i).equiv z.1).val,
        ((i.arrow (a.option.prod Numbering.move)).equiv z.2).val) := by
  let b := (a.size+2)^i.size
  have left (s : Q) : ((pc a q i).equiv (.inl s)).val = (q.equiv s).val := rfl
  have right (x : Q) (v : I → SM.Action A) : ((pc a q i).equiv (.inr (x,v))).val =
      q.size+(((i.arrow (action a)).equiv v).val+b*(q.equiv x).val) := rfl
  cases s with
  | inl s =>
    simp only [left, row, (q.equiv s).isLt, ↓reduceIte, SM.toTM]
    rw [source s top]
    cases m s top with
    | none => rfl
    | some z =>
      obtain ⟨x,v⟩ := z
      simp only [Option.map_some, right, Option.some.injEq, Prod.mk.injEq, b, true_and]
      exact cmds_eq a i first SM.Action.first (first_eq a) v top
  | inr z =>
    obtain ⟨x,v⟩ := z
    let r := ((i.arrow (action a)).equiv v).val
    have hr : r < b := ((i.arrow (action a)).equiv v).isLt
    have hb : 0 < b := Nat.zero_lt_of_lt hr
    have hd : (r+b*(q.equiv x).val)/b = (q.equiv x).val := by
      rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hr, Nat.zero_add]
    have he : (r+b*(q.equiv x).val)%b = r := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    simp only [right, row, Nat.not_lt_of_ge (Nat.le_add_right ..), ↓reduceIte, Nat.add_sub_cancel_left,
      SM.toTM, Option.map_some, left]
    change some ((r+b*(q.equiv x).val)/b, cmds second _ _ ((r+b*(q.equiv x).val)%b) _) = _
    rw [hd,he,cmds_eq a i second SM.Action.second (second_eq a) v top]

@[simp] theorem pc_size (a : Numbering A) (q : Numbering Q) (i : Numbering I) :
    (pc a q i).size = q.size + q.size * (a.size+2)^i.size := rfl

/-- Effective families of stack rows compile uniformly, with explicit arities and
row addresses for the resulting tape machines. -/
theorem compile_family {A Q I : ℕ → Type}
    (a : ∀ j, Numbering (A j)) (q : ∀ j, Numbering (Q j)) (i : ∀ j, Numbering (I j))
    (m : ∀ j, SM.Rule (A j) (Q j) (I j))
    (orig : ℕ → ℕ × ℕ → Option (ℕ × ℕ))
    (ha : Computable fun j => (a j).size) (hq : Computable fun j => (q j).size)
    (hi : Computable fun j => (i j).size) (ho : Computable₂ orig)
    (hs : ∀ j, Sources (a j) (q j) (i j) (m j) (orig j)) :
    let state := fun j => pc (a j) (q j) (i j)
    let letter := fun j => (a j).option
    let rows j := row (a j).size (q j).size (i j).size (orig j)
    Computable (fun j => (state j).size) ∧ Computable (fun j => (letter j).size) ∧
    Computable₂ rows ∧ ∀ j s top,
      rows j (((state j).equiv s).val,(((i j).arrow (letter j)).equiv top).val) =
        ((SM.toTM (m j)) s top).map fun z => (((state j).equiv z.1).val,
          (((i j).arrow ((letter j).prod Numbering.move)).equiv z.2).val) := by
  have pow : Computable fun j => ((a j).size+2)^(i j).size :=
    (KernelComputableAddress.primrec_pow (Primrec.nat_add.comp Primrec.fst (Primrec.const 2))
      Primrec.snd).to_comp.comp (ha.pair hi)
  exact ⟨Primrec.nat_add.to_comp.comp hq (Primrec.nat_mul.to_comp.comp hq pow),
    Primrec.nat_add.to_comp.comp ha (Computable.const 1), computable_row ha hq hi ho,
    fun j => row_eq _ _ _ _ _ (hs j)⟩

end Generator.StackRows

end NearSquareRoot
end Computability
end OAI
