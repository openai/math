import OAI.Computability.BorderVNP.CellFragmentControl

/-! # Word records inside the sparse generator -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.Generator.Fragment

open VPVNP.RAMTape RationalHitting.StackLanguage

variable {K : Type} [DecidableEq K]

private theorem bank_set (r : Fragment K) (s : Stacks K) (k : K) (xs : List Bool) :
    Function.update (r.bank s) (.inl k) xs = r.bank (Function.update s k xs) := by
  funext i
  cases i with
  | inl j => by_cases h : j = k <;> simp [bank, h]
  | inr j => simp [bank]

private theorem bank_temp (r : Fragment K) (s : Stacks K) (k : r.Scratch) :
    Function.update (r.bank s) (.inr k) [] = r.bank s := Function.update_eq_self (.inr k) (r.bank s)

/-- Copy a stack verbatim, overwriting the destination. -/
def copyWord (src dst : K) : Fragment K where
  Scratch := Unit
  body := Structured.lower (copy (.inl src) (.inl dst) (.inr ()))

/-- A copy reads the source once and clears any preceding destination value. -/
theorem copyWord_run {src dst : K} (hd : src ≠ dst) (s : Stacks K) :
    ∃ t ≤ 2*(7*(s src).length+2*(s dst).length+7),
      (copyWord src dst).Runs t s (Function.update s dst (s src)) := by
  let r := copyWord src dst
  have h := eval_copy (a := Sum.inl src) (b := Sum.inl dst) (tmp := Sum.inr ())
    (by simpa) (by simp) (by simp) (r.bank s)
  obtain ⟨t,ht,hr⟩ := Structured.run h
  erw [bank_set r s dst (s src), bank_temp r _ ()] at hr
  exact ⟨t, ht, hr⟩

/-- Add a framed copy of the source to the front of the destination, consuming the source. -/
def prepend (src dst : K) : Fragment K where
  Scratch := Unit
  body := Structured.lower (prependRecord (.inl src) (.inl dst) (.inr ()))

/-- Framing one input field uses six source scans plus fixed control overhead. -/
theorem prepend_run {src dst : K} (hd : src ≠ dst) (s : Stacks K) :
    ∃ t ≤ 2*(6*(s src).length+5), (prepend src dst).Runs t s
      (Function.update (Function.update s src []) dst (codeWord (s src) ++ s dst)) := by
  let r := prepend src dst
  have h := eval_prependRecord (a := Sum.inl src) (b := Sum.inl dst) (tmp := Sum.inr ())
    (by simpa) (by simp) (by simp) (r.bank s) rfl
  obtain ⟨t,ht,hr⟩ := Structured.run h
  erw [bank_set r s src [], bank_set r _ dst (codeWord (s src) ++ s dst)] at hr
  exact ⟨t,ht,hr⟩

private def splitPorts (src dst : K) : Fin 3 → K ⊕ Unit := threeRegs (.inl src) (.inl dst) (.inr ())

/-- Remove one self-delimiting word from the source, putting its digits in order on the
empty destination and retaining the unconsumed suffix on the source. -/
def split (src dst : K) : Fragment K where
  Scratch := Unit
  body := (Structured.lower (splitPair (K := Fin 3) 1 0 2)).onPorts (splitPorts src dst)

/-- Extraction costs depend on the extracted word; subsequent records are never scanned. -/
theorem split_run {src dst : K} (hd : src ≠ dst) (s : Stacks K) (x rest : List Bool)
    (hs : s src = codeWord x ++ rest) (he : s dst = []) :
    ∃ t ≤ 2*(7*x.length+10), (split src dst).Runs t s
      (Function.update (Function.update s src rest) dst x) := by
  obtain ⟨t, ht, hr⟩ := Structured.run (eval_splitPair (K := Fin 3) (a := 1) (b := 0) (tmp := 2)
    (by decide) (by decide) (by decide) x rest)
  refine ⟨t, ht, ?_⟩
  apply (Structured.lower (splitPair (K := Fin 3) 1 0 2)).runs_onPorts_framed (ports := splitPorts src dst) (threeRegs_inj (a := (Sum.inl src : K ⊕ Unit)) (b := .inl dst) (c := .inr ()) (by simpa : Sum.inl src ≠ (Sum.inl dst : K ⊕ Unit))
    (by simp) (by simp)) hr
  · intro i
    fin_cases i
    · change s src = single (0 : Fin 3) (codeWord x ++ rest) 0
      simpa using hs
    · change s dst = single (0 : Fin 3) (codeWord x ++ rest) 1
      simpa [single] using he
    · change [] = single (0 : Fin 3) (codeWord x ++ rest) 2
      simp [single]
  · intro i
    fin_cases i
    · change Function.update (Function.update s src rest) dst x src = both (1 : Fin 3) 0 x rest 0
      simp [both, hd]
    · change Function.update (Function.update s src rest) dst x dst = both (1 : Fin 3) 0 x rest 1
      simp [both, single]
    · change [] = both (1 : Fin 3) 0 x rest 2
      simp [both, single]
  · intro j hn
    cases j with
    | inr j => rfl
    | inl j =>
      have h₁ : src ≠ j := by intro h; exact hn 0 (by simp [splitPorts, threeRegs, h])
      have h₂ : dst ≠ j := by intro h; exact hn 1 (by simp [splitPorts, threeRegs, h])
      change Function.update (Function.update s src rest) dst x j = s j
      rw [Function.update_of_ne h₂.symm, Function.update_of_ne h₁.symm]

end CellMacro.Generator.Fragment

end BorderVNP
end Computability
end OAI
