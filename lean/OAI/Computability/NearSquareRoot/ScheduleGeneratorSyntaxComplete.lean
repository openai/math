import OAI.Computability.NearSquareRoot.ScheduleGeneratorStackRows
import OAI.Computability.IntegerMultiplication.SM.Output
import Batteries.Tactic.OpenPrivate

/-! # Numbered transition rows for the final stack output copy

The new output tape and the copying state both have index zero. All previous
heads and runnable states shift by one. A blank at the designated source head
ends copying.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.CompleteRows

open IntegerMultiplication CommonAlphabet Numbering
open StackRows (option_none option_some)

def pack (b n : ℕ) (f : ℕ → ℕ) := encodeBase b ((List.range n).map f)

def oldReads (b n reads : ℕ) := pack b n fun j => digit b reads (j+1)

def keep (b reads j : ℕ) := 1+3*digit b reads j

def oldCmd (b reads acts j : ℕ) :=
  if j = 0 then keep b reads j else digit (b*3) acts (j-1)

def copyCmd (b k reads j : ℕ) :=
  if j = 0 then 2+3*digit b reads (k+1)
  else if j = k+1 then 2 else keep b reads j

/-- Extend an existing tape row with the physical output head and copying phase. -/
def row (b n k : ℕ) (orig : ℕ × ℕ → Option (ℕ × ℕ)) (p : ℕ × ℕ) : Option (ℕ × ℕ) :=
  if p.1 = 0 then
    if digit b p.2 (k+1) = 0 then none else some (0, pack (b*3) (n+1) (copyCmd b k p.2))
  else (orig (p.1-1,oldReads b n p.2)).elim
    (some (0,pack (b*3) (n+1) (keep b p.2)))
    (fun z => some (z.1+1,pack (b*3) (n+1) (oldCmd b p.2 z.2)))

variable {A Q I : Type}

private theorem pack_eq {G H : Type} (g : Numbering G) (h : Numbering H)
    (f : ℕ → ℕ) (v : G → H) (digits : ∀ x, f ((g.equiv x).val) = (h.equiv (v x)).val) :
    pack h.size g.size f = ((g.arrow h).equiv v).val := by
  rw [← encodeBase_arrow]
  unfold pack
  have range : (List.finRange g.size).map Fin.val = List.range g.size := by
    apply List.ext_getElem <;> simp
  rw [← range, Numbering.all, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  exact (by simpa using digits (g.equiv.symm k))

private theorem cmdRank (a : Numbering A) (v : Option A) (m : TM.Move) :
    ((a.option.prod Numbering.move).equiv (v,m)).val =
      (Numbering.move.equiv m).val+3*(a.option.equiv v).val := rfl

private theorem read_eq (a : Numbering A) (i : Numbering I) (top : Option I → Option A) :
    oldReads a.option.size i.size ((i.option.arrow a.option).equiv top).val =
      ((i.arrow a.option).equiv (fun x => top (some x))).val :=
  pack_eq i a.option _ _ fun x => (by
    simpa only [option_some] using digit_arrow i.option a.option top (some x))

open private preserve right from OAI.Computability.IntegerMultiplication.SM.Output

/-- The numeric output adapter preserves the lifted machine's ordinary rows and
implements the physical source-to-output copy when it reaches the copying state. -/
theorem row_eq [DecidableEq I] (a : Numbering A) (q : Numbering Q) (i : Numbering I)
    (k : I) (m : TM.Rule (Option A) Q I) (orig : ℕ × ℕ → Option (ℕ × ℕ))
    (source : ∀ s top, orig ((q.equiv s).val, ((i.arrow a.option).equiv top).val) =
      (m s top).map fun z => ((q.equiv z.1).val, ((i.arrow (a.option.prod Numbering.move)).equiv z.2).val))
    (s : Option Q) (top : Option I → Option A) :
    row a.option.size i.size (i.equiv k).val orig
      ((q.option.equiv s).val, ((i.option.arrow a.option).equiv top).val) =
      (SM.withOutput k m s top).map fun z => ((q.option.equiv z.1).val,
        ((i.option.arrow (a.option.prod Numbering.move)).equiv z.2).val) := by
  let R := ((i.option.arrow a.option).equiv top).val
  let b := a.option.size
  let rank := (i.equiv k).val
  have read (j : Option I) : digit b R (i.option.equiv j).val = (a.option.equiv (top j)).val :=
    digit_arrow i.option a.option top j
  have sourceRead : digit b R (rank+1) = (a.option.equiv (top (some k))).val := by
    simpa only [option_some, rank] using read (some k)
  have preserveRank (j : Option I) :
      keep b R (i.option.equiv j).val = ((a.option.prod Numbering.move).equiv (preserve (top j))).val := by
    rw [keep, read, preserve, cmdRank]
    rfl
  change row b i.size rank orig ((q.option.equiv s).val, R) = _
  cases s with
  | some s =>
    simp only [row, option_some, Nat.succ_ne_zero, ↓reduceIte, Nat.add_one_sub_one, SM.withOutput]
    rw [read_eq a i top, source]
    cases hm : m s (fun x => top (some x)) with
    | none =>
      simp only [Option.map_none, Option.elim_none, Option.map_some, option_none]
      exact congrArg (fun v => some (0,v))
        (pack_eq i.option (a.option.prod Numbering.move) _ _ preserveRank)
    | some z =>
      obtain ⟨s',o⟩ := z
      simp only [Option.map_some, Option.elim_some, option_some, Option.some.injEq, Prod.mk.injEq, true_and]
      apply pack_eq i.option (a.option.prod Numbering.move)
      intro j
      cases j with
      | none => simpa only [oldCmd, option_none, ↓reduceIte] using preserveRank none
      | some j =>
        have base : (a.option.prod Numbering.move).size = b*3 := rfl
        simpa only [oldCmd, option_some, Nat.succ_ne_zero, ↓reduceIte, Nat.add_one_sub_one, base]
          using digit_arrow i (a.option.prod Numbering.move) o j
  | none =>
    simp only [row, option_none, ↓reduceIte, SM.withOutput, sourceRead]
    cases hk : top (some k) with
    | none => simp only [option_none, ↓reduceIte, Option.map_none]
    | some v =>
      simp only [option_some, Nat.succ_ne_zero, ↓reduceIte, Option.map_some, option_none,
        Option.some.injEq, Prod.mk.injEq, true_and]
      apply pack_eq i.option (a.option.prod Numbering.move)
      intro j
      cases j with
      | none =>
        rw [option_none, copyCmd, ite_eq_left rfl, sourceRead, hk, right, cmdRank]
        rfl
      | some j =>
        rw [option_some, copyCmd, ite_eq_right (Nat.succ_ne_zero _)]
        by_cases h : j = k
        · subst j
          simp only [rank, ↓reduceIte, right, cmdRank, option_none, Nat.mul_zero, Nat.add_zero]
          rfl
        · have ne : (i.equiv j).val + 1 ≠ rank + 1 :=
            fun e => h (i.equiv.injective (Fin.ext (Nat.succ.inj e)))
          rw [ite_eq_right ne]
          simpa only [option_some, ite_eq_right h] using preserveRank (some j)

end Generator.CompleteRows

end NearSquareRoot
end Computability
end OAI
