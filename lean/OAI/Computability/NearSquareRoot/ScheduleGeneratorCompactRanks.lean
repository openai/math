import OAI.Computability.NearSquareRoot.ScheduleGeneratorCompactFormula
import OAI.Computability.NearSquareRoot.ScheduleGeneratorStackRows
import OAI.Computability.NearSquareRoot.CommonAlphabetPublic

/-! # Exact ranks of the public compactor's control and tape commands -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.CompactRows

open IntegerMultiplication CommonAlphabet Numbering StackRows

abbrev buffer (w : ℕ) := (Numbering.fin w).arrow ternary
abbrev rankBuf {w : ℕ} (v : Letters w) := ((buffer w).equiv v).val
abbrev rankState {w : ℕ} (s : Compact.Phase w) := ((compact w).equiv s).val
abbrev rankLetter (x : Public.Letter) := (publicLetter.equiv x).val
abbrev rankTernary (x : Option Bool) := (ternary.equiv x).val

@[simp] theorem rank_prev (w : ℕ) : rankState (.prev : Compact.Phase w) = 0 := by
  apply option_none

@[simp] theorem rank_done (w : ℕ) : rankState (.done : Compact.Phase w) = 1 := by
  change ((((buffer w).prod (fin w)).sum (ternary.sum (fin w))).option.option.equiv (some none)).val = 1
  simp

@[simp] theorem rank_scan {w : ℕ} (v : Letters w) (j : Fin w) :
    rankState (.scan v j) = scanState w (rankBuf v) j.val := by
  change ((((buffer w).prod (fin w)).sum (ternary.sum (fin w))).option.option.equiv
    (some (some (.inl (v,j))))).val = _
  simp only [option_some]
  rfl

@[simp] theorem rank_emit (w : ℕ) (v : Option Bool) :
    rankState (.emit v : Compact.Phase w) = emitState w (rankTernary v) := by
  change ((((buffer w).prod (fin w)).sum (ternary.sum (fin w))).option.option.equiv
    (some (some (.inr (.inl v))))).val = _
  simp only [option_some]
  rfl

@[simp] theorem rank_back {w : ℕ} (j : Fin w) :
    rankState (.back j) = backState w j.val := by
  change ((((buffer w).prod (fin w)).sum (ternary.sum (fin w))).option.option.equiv
    (some (some (.inr (.inr j))))).val = _
  simp only [option_some]
  rfl

theorem rank_public_none : rankLetter none = 0 := StackRows.option_none ternary

theorem rank_public_some (b : Option Bool) : rankLetter (some b) = rankTernary b+1 := StackRows.option_some _ _

theorem rank_join (b : Public.Letter) : rankLetter b-1 = rankTernary b.join := by
  cases b with
  | none => rfl
  | some b => simp only [rank_public_some, Nat.add_sub_cancel, Option.join_some]

theorem rank_blank (d : Public.Letter) : (rankLetter d = 0) ↔ d.isNone = true := by
  cases d with
  | none => decide
  | some d => simp [rank_public_some]

theorem rank_start {A : Type} (c : Code A) :
    rankState (Compact.start c) = scanState c.width 0 0 := by
  have h : rankBuf (fun _ : Fin c.width => (none : Option Bool)) = 0 := by
    change (finFunctionFinEquiv (fun _ : Fin c.width => (0 : Fin 3))).val = 0
    simp
  exact (rank_scan _ _).trans (congrArg (fun b => scanState c.width b 0) h)

theorem store_eq {w : ℕ} (v : Letters w) (j : Fin w) (d : Option Bool) :
    storeDigit w (rankBuf v) j.val (rankTernary d) =
      rankBuf (Function.update v j d) := by
  change _ = (((Numbering.fin w).arrow ternary).equiv (Function.update v j d)).val
  rw [← Numbering.encodeBase_arrow (Numbering.fin w) ternary (Function.update v j d)]
  unfold storeDigit
  apply congrArg (encodeBase 3)
  have range : (List.finRange w).map Fin.val = List.range w := by
    apply List.ext_getElem <;> simp
  rw [← range, List.map_map, Numbering.all, List.map_map]
  apply List.map_congr_left
  intro k _
  change (if k.val = j.val then rankTernary d else digit 3 (rankBuf v) k.val) = rankTernary ((Function.update v j d) k)
  by_cases h : k=j
  · subst k
    simp
  · have hn := Fin.val_ne_of_ne h
    simp only [hn, ↓reduceIte, Function.update_of_ne h]
    exact digit_arrow (Numbering.fin w) ternary v k

theorem operations_eq (f : Bool → Public.Letter × TM.Move) :
    ((bool.arrow (publicLetter.prod Numbering.move)).equiv f).val =
      operations (rankLetter (f false).1) (rankLetter (f true).1)
        (Numbering.move.equiv (f false).2).val (Numbering.move.equiv (f true).2).val := by
  rw [← encodeBase_arrow]
  change encodeBase 12 ([false,true].map _) = _
  simp [encodeBase,Nat.ofDigits,operations, Numbering.prod, finProdFinEquiv]
  rfl

end Generator.CompactRows

end NearSquareRoot
end Computability
end OAI
