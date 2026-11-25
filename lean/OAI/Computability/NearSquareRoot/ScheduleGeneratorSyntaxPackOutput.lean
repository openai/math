import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxPackInput
import OAI.Computability.NearSquareRoot.ScheduleGeneratorStackRows

/-! # Packed destinations and action tuples for the structured stack compiler -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Pack

open IntegerMultiplication CommonAlphabet Generator.SyntaxAddress Generator.StackRows Transition

def stateDigit (sites : List Site) (q : Option Site) : ℕ :=
  q.elim 0 fun s => rank sites s + 1

def symbolDigit (aSize : ℕ) (sites : List Site) (s : Symbol) : ℕ :=
  s.elim id fun p => aSize + rank sites p

def actionDigit (aSize : ℕ) (sites : List Site) (cmd : Option (Option Symbol)) : ℕ :=
  cmd.elim 0 fun push => push.elim 1 fun s => symbolDigit aSize sites s + 2

def stackNames (sites : List Site) : List ℕ := 0 :: (registerNames sites).dedup.map Nat.succ

def changeAt (change : Option (ℕ × Option Symbol)) (j : ℕ) : Option (Option Symbol) :=
  change.bind fun (i,a) => if i = j then some a else none

/-- Serialize a compiler row using the stack numbering and its little-endian action tuple. -/
def output (aSize : ℕ) (sites : List Site) (r : Result) : Option (ℕ × ℕ) :=
  r.map fun (q,change) =>
    (stateDigit sites q, Numbering.encodeBase (aSize + size sites + 2)
      ((stackNames sites).map fun j => actionDigit aSize sites (changeAt change j)))


variable {A : Type} [Fintype A] (a : Numbering A) (U : List (Prog.Loc A))

private theorem stateDigit_eq (q : Prog.Pc U) :
    stateDigit (U.map (site (letter a))) (pcKey (letter a) U q) = ((pcs a U).equiv q).val := by
  cases q with
  | none => exact (option_none _).symm
  | some p => exact (option_some (ptrNumbering (letter a) U) p).symm

private theorem symbolDigit_eq (s : Prog.Sym U) :
    symbolDigit a.size (U.map (site (letter a))) (symbolKey (letter a) U s) =
      ((symbols a U).equiv s).val := by
  cases s with
  | inl x => rfl
  | inr p => rfl

private theorem actionDigit_eq (op : SM.Action (Prog.Sym U)) :
    actionDigit a.size (U.map (site (letter a))) (actionKey (letter a) U op) =
      ((action (symbols a U)).equiv op).val := by
  cases op <;> simp [actionKey, actionDigit, symbolDigit_eq]

private theorem stack_index (k : Prog.Ix U) :
    (stackNames (U.map (site (letter a))))[((Pack.stacks U).equiv k).val]? = some (register U k) := by
  cases k with
  | none =>
    rw [show ((Pack.stacks U).equiv none).val = 0 from option_none (idxNumbering U)]
    rfl
  | some k =>
    have h : ((Pack.stacks U).equiv (some k)).val = rank (Prog.used U) k.val + 1 :=
      (option_some (idxNumbering U) k).trans (congrArg Nat.succ (idx_rank U k))
    rw [h]
    simp only [stackNames, registerNames_sites, List.getElem?_cons_succ, List.getElem?_map,
      register, Option.elim_some]
    unfold rank
    rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem (List.mem_dedup.mpr k.property))]
    simp

private theorem stackNames_eq :
    stackNames (U.map (site (letter a))) = (Pack.stacks U).all.map (register U) := by
  have len : (stackNames (U.map (site (letter a)))).length = (Pack.stacks U).size := by
    simp [Pack.stacks, Numbering.option, idx_size, stackNames, registerNames_sites, size]
  apply List.ext_getElem
  · simpa only [List.length_map, Numbering.all, List.length_finRange] using len
  · intro i hi hj
    let j : Fin (Pack.stacks U).size := ⟨i,len ▸ hi⟩
    have h := stack_index a U ((Pack.stacks U).equiv.symm j)
    rw [Equiv.apply_symm_apply] at h
    change (stackNames (U.map (site (letter a))))[i]? = _ at h
    rw [List.getElem?_eq_getElem hi] at h
    simpa [Numbering.all, j] using Option.some.inj h

/-- Pointwise agreement with the stack compiler determines its entire packed row,
including the halt case and all unchanged registers. -/
theorem output_correct (raw : Result)
    (actual : Option (Prog.Pc U × (Prog.Ix U → SM.Action (Prog.Sym U))))
    (rows : ∀ j, rowAt raw (register U j) = nativeAt (letter a) U actual j) :
    output a.size (U.map (site (letter a))) raw = actual.map fun z =>
      (((pcs a U).equiv z.1).val, (((Pack.stacks U).arrow (action (symbols a U))).equiv z.2).val) := by
  cases raw with
  | none => cases actual <;> have h := rows none <;> simp_all [output, rowAt, nativeAt]
  | some v =>
    obtain ⟨q,change⟩ := v
    cases actual with
    | none => simpa [rowAt, nativeAt] using rows none
    | some z =>
      obtain ⟨next,ops⟩ := z
      have eqs (j : Prog.Ix U) : q = pcKey (letter a) U next ∧
          changeAt change (register U j) = actionKey (letter a) U (ops j) := by
        simpa only [rowAt, nativeAt, Option.map_some, Option.some.injEq, Prod.mk.injEq, changeAt]
          using rows j
      rw [(eqs none).1]
      simp only [output, Option.map_some, Option.some.injEq, Prod.mk.injEq, stateDigit_eq, true_and]
      rw [← Numbering.encodeBase_arrow]
      change Numbering.encodeBase _ _ = Numbering.encodeBase (a.size + size _ + 2) _
      congr 1
      rw [stackNames_eq, List.map_map]
      apply List.map_congr_left
      intro j _
      exact (congrArg (actionDigit a.size _) (eqs j).2).trans (actionDigit_eq a U (ops j))

end GeneratorSyntax.Pack

end NearSquareRoot
end Computability
end OAI
