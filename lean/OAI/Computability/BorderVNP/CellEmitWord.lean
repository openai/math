import OAI.Computability.BorderVNP.CellDirectoryTyped
import OAI.Computability.BorderVNP.CellGeneratorWire
import OAI.Computability.QuantumFactoring.BitStackBooleans
import OAI.Computability.QuantumFactoring.BitStackConstants

/-! # Physical emitters for compact generator words

These procedures operate on actual finite Boolean stacks. The outer packet
transport and the specialized generator use the zero-tag framing of
`StackLanguage.codeWord`. It differs from the internal tuple framing used by
`BitStackProgram.Procedure`.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram
open RationalHitting.StackLanguage (codeWord pairWord)

/-- A deterministic finite program printing an actual bit string. -/
abbrev Word {α : Type} (ea : α → List Bool) (f : α → List Bool) := Procedure ea id f

/-- Print a sparse statement with the native generator's fixed address depth. -/
abbrev Statement {α : Type} (ea : α → List Bool) (s : α → Stmt) :=
  Word ea (fun x => CellMacro.Generator.serialized 8 (s x))

/-- Print the padded address representation for every compile-time depth. -/
abbrev Address {α : Type} (ea : α → List Bool) (a : α → NatExpr) :=
  ∀ d, Word ea (fun x => CellMacro.Generator.exprBits d (a x))

/-- A Boolean expression can be printed at any supplied temporary stack depth. -/
abbrev Boolean {α : Type} (ea : α → List Bool) (a : α → Term) :=
  Statement (prodCode ea Nat.bits) (fun x => (a x.1).emit x.2)

variable {α : Type} {ea : α → List Bool} {a b : α → List Bool}

/-- Print two dynamically produced strings in order. -/
noncomputable def wordAppend (p : Word ea a) (q : Word ea b) : Word ea (fun x => a x ++ b x) :=
  Procedure.append.comp (p.pair q)

/-- Prepend a fixed command tag to the computed payload. -/
noncomputable def wordPrepend (tag : List Bool) (p : Word ea a) : Word ea (fun x => tag ++ a x) :=
  ((Procedure.prepend id tag).comp p).result (fun _ => rfl)

/-- A constant bit-string field. -/
noncomputable def constWord (w : List Bool) : Word ea (fun _ => w) := Procedure.constant _ _ w

private def frameLoop : Program (Fin 3) := .loop 0
  (.seq (.push 2 false) (.push 2 false)) (.seq (.push 2 false) (.push 2 true))

private theorem frameLoop_runs (s : Store (Fin 3)) :
    Runs frameLoop s (Function.update (Function.update s 0 []) 2 ((pairWord (s 0)).reverse ++ s 2))
      (3*(s 0).length+1) := by
  generalize hs : s 0 = xs at *
  induction xs generalizing s with
  | nil =>
    have h : Function.update (Function.update s 0 []) 2 ((pairWord []).reverse ++ s 2) = s := by
      simp only [RationalHitting.StackLanguage.pairWord_nil,List.reverse_nil,List.nil_append]
      rw [← hs,Function.update_eq_self,Function.update_eq_self]
    rw [h]
    exact Runs.loop_nil hs
  | cons x xs ih =>
    let u := Function.update s 0 xs
    let v := Function.update u 2 (x::false::u 2)
    have hv : v 0 = xs := by simp [v,u]
    have hb : Runs (.seq (.push 2 false) (.push 2 x)) u v 2 := by
      simpa only [Function.update_self,Function.update_idem] using
        Runs.seq (Runs.push u 2 false) (Runs.push (Function.update u 2 (false::u 2)) 2 x)
    have hh : Runs frameLoop s (Function.update (Function.update v 0 []) 2 ((pairWord xs).reverse ++ v 2))
        (3*xs.length+1+2+1) := by
      cases x
      · exact Runs.loop_false (a:=2) (b:=3*xs.length+1) hs hb (ih v hv)
      · exact Runs.loop_true (a:=2) (b:=3*xs.length+1) hs hb (ih v hv)
    convert hh using 1
    · funext k
      fin_cases k <;> simp [v,u,Function.update, List.append_assoc]

/-- A finite linear-time procedure for the exact native generator field framing. -/
noncomputable def codeWordP : Word id codeWord where
  K := Fin 3
  finiteK := inferInstance
  decideK := inferInstance
  input := 0
  output := 1
  program := .seq frameLoop (.seq (.push 2 true) (reverseMove 2 1))
  bound := Polynomial.C 7*Polynomial.X+Polynomial.C 5
  runs x := by
    let s := singletonStore (0 : Fin 3) x
    let u := Function.update (Function.update s 0 []) 2 ((pairWord x).reverse)
    let v := Function.update u 2 (true :: u 2)
    have h₀ : Runs frameLoop s u (3*x.length+1) := by
      simpa [s,u,singletonStore] using frameLoop_runs s
    have h := Runs.seq h₀ (Runs.seq (Runs.push u 2 true) (reverseMove_runs 2 1 (by decide) v))
    have hout : Function.update (Function.update v 2 []) 1 ((v 2).reverse ++ v 1) =
        singletonStore 1 (codeWord x) := by
      funext k
      fin_cases k <;> simp [s,u,v,singletonStore,Function.update,RationalHitting.StackLanguage.codeWord_pair]
    have hlen : (pairWord x).length = 2*x.length := by
      have hl := RationalHitting.StackLanguage.codeWord_length x
      rw [RationalHitting.StackLanguage.codeWord_pair,List.length_append] at hl
      simp only [List.length_singleton] at hl
      omega
    have ht : 2*(v 2).length+1+1+(3*x.length+1) = 7*x.length+5 := by
      simp only [v,u,Function.update_self,List.length_cons,List.length_reverse,hlen]
      omega
    rw [hout,ht] at h
    exact ⟨7*x.length+5,by simp,h⟩

/-- Frame one dynamically printed payload. -/
noncomputable def framed (p : Word ea a) : Word ea (fun x => codeWord (a x)) := codeWordP.comp p

/-- Record of one dynamic generator instruction. -/
noncomputable def singleRecord (p : Word ea a) :
    Word ea (fun x => CellMacro.Generator.records [a x]) :=
  (wordPrepend [true] (framed p)).congrFun (by intro x; simp [CellMacro.Generator.records])

/-- Framing commutes with concatenation of sparse instruction lists. -/
theorem records_append (xs ys : List (List Bool)) :
    CellMacro.Generator.records (xs ++ ys) = CellMacro.Generator.records xs ++ CellMacro.Generator.records ys := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp [CellMacro.Generator.records, ih, List.append_assoc]

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
