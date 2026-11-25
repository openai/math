import OAI.Computability.NearSquareRoot.ScheduleProgram
import OAI.Computability.NearSquareRoot.Specification

/-!
# Physical storage for the interpreter's ROM

All tapes use the same blank. On a program tape a data-side blank decodes as an
end-code marker. Normalization preserves the entire transition sequence, the physical
head positions, and the contents of every data tape.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Universal

open IntegerMultiplication
variable {A I : Type}

def romWord (blank : A) (code : List (Tag A I)) (p : ℤ) : TM.Tape (Letter A I) :=
  ⟨p, fun k => (TM.Tape.loaded (.inl blank) (code.map Sum.inr)).view (p+k)⟩

def loadedConf (blank : A) (code : List (Tag A I)) (d : I → TM.Tape A)
    (side : Bool) (phase : Phase) (p q : ℤ) :
    TM.Config (Letter A I) PC (Index I) :=
  ⟨(side,phase), fun
    | .inl i => dataCell (d i)
    | .inr b => romWord blank code (if b = side then p else q)⟩

/-- The data alphabet remains unchanged on data tapes. On ROM tapes all
data-side cells are read exactly as an end-of-code tag. -/
def normalizeLetter (i : Index I) (c : Letter A I) : Letter A I :=
  match i, c with
  | .inr _, .inl _ => .inr .endCode
  | _, c => c

def normalizeTape (i : Index I) (t : TM.Tape (Letter A I)) : TM.Tape (Letter A I) :=
  ⟨t.pos,fun k => normalizeLetter i (t.view k)⟩

def normalize (c : TM.Config (Letter A I) PC (Index I)) :
    TM.Config (Letter A I) PC (Index I) :=
  ⟨c.pc,fun i => normalizeTape i (c.tape i)⟩

theorem normalize_data (c : TM.Config (Letter A I) PC (Index I)) (i : I) :
    (normalize c).tape (.inl i) = c.tape (.inl i) := by
  cases h : c.tape (.inl i)
  simp [normalize,normalizeTape,normalizeLetter,h]

theorem normalize_loaded (blank : A) (code : List (Tag A I)) (d : I → TM.Tape A)
    (b : Bool) (ph : Phase) (p q : ℤ) :
    normalize (loadedConf blank code d b ph p q) = conf (fetch code) d b ph p q := by
  simp only [normalize, loadedConf, conf, TM.Config.mk.injEq, true_and]
  funext i
  cases i with
  | inl j => rfl
  | inr j =>
    change normalizeTape (.inr j) (romWord blank code (if j = b then p else q)) =
      atCell (fetch code) (if j = b then p else q)
    generalize (if j = b then p else q) = v
    unfold normalizeTape atCell romWord
    congr 1
    funext k
    change normalizeLetter (.inr j) ((TM.Tape.loaded (.inl blank) (code.map Sum.inr)).view (v+k)) = .inr (fetch code (v+k))
    cases z : v+k with
    | negSucc n => rfl
    | ofNat n =>
      simp only [TM.Tape.loaded, List.getElem?_map, fetch]
      cases code[n]? <;> rfl

private def normHeads (v : Index I → Letter A I) (i : Index I) :=
  normalizeLetter i (v i)

private def normCommand (op : PC × (Index I → Letter A I × TM.Move)) :
    PC × (Index I → Letter A I × TM.Move) :=
  (op.1,fun i => (normalizeLetter i (op.2 i).1, (op.2 i).2))

private theorem norm_read (blank : A) (v : Index I → Letter A I) :
    readData blank (normHeads v) = readData blank v := rfl

private theorem norm_tag (v : Index I → Letter A I) (b : Bool) :
    tagAt (normHeads v) b = tagAt v b := by
  unfold tagAt normHeads
  cases v (.inr b) <;> rfl

private theorem norm_issue (v : Index I → Letter A I) (b : Bool) (q : PC)
    (x y : TM.Move) (o : Option (I → A × TM.Move)) :
    issue (normHeads v) b q x y o = (issue v b q x y o).map normCommand := by
  unfold issue normCommand
  congr 3
  funext i
  cases i with
  | inl i => cases o <;> rfl
  | inr j => rfl

private theorem norm_rule [Finite A] [Finite I] (blank : A) (q : PC)
    (v : Index I → Letter A I) :
    rule blank q (normHeads v) = (rule blank q v).map normCommand := by
  classical
  obtain ⟨b,q⟩ := q
  cases q with
  | seek =>
    simp only [rule,norm_tag,norm_read]
    cases tagAt v b with
    | branch r op => by_cases h : r = readData blank v <;> cases op <;> simp [h,norm_issue]
    | _ => apply norm_issue
  | skip =>
    simp only [rule,norm_tag]
    cases tagAt v (!b) <;> apply norm_issue
  | dest | rewind =>
    simp only [rule,norm_tag]
    cases tagAt v b <;> apply norm_issue

private theorem norm_apply (i : Index I) (t : TM.Tape (Letter A I)) (cmd : Letter A I × TM.Move) :
    (normalizeTape i t).apply (normalizeLetter i cmd.1,cmd.2) =
      normalizeTape i (t.apply cmd) := by
  simp only [normalizeTape,TM.Tape.apply,TM.Tape.mk.injEq,true_and]
  funext d
  split <;> simp_all

/-- Every transition commutes with decoding physically blank ROM cells. -/
theorem normalize_advance [Finite A] [Finite I] (blank : A)
    (c : TM.Config (Letter A I) PC (Index I)) :
    TM.advance (rule blank) (normalize c) = (TM.advance (rule blank) c).map normalize := by
  let v := fun i => (c.tape i).view 0
  change (rule blank c.pc (normHeads v)).map _ = ((rule blank c.pc v).map _).map _
  rw [norm_rule]
  cases op : rule blank c.pc v with
  | none => rfl
  | some cmds =>
    simp only [Option.map_some,Option.some.injEq]
    congr 1
    funext i
    exact norm_apply i _ _

/-- Pull an ideal trace back to the real finite ROM words with the same number of steps. -/
theorem pull_trace [Finite A] [Finite I] {blank : A}
    {c y : TM.Config (Letter A I) PC (Index I)} {n : ℕ}
    (r : Trace (TM.advance (rule blank)) (normalize c) n y) :
    ∃ z, Trace (TM.advance (rule blank)) c n z ∧ normalize z = y := by
  generalize h : normalize c = x at r
  induction r generalizing c with
  | nil => exact ⟨c,.nil _,h⟩
  | @cons x u y n hu _ ih =>
    rw [← h,normalize_advance] at hu
    cases hc : TM.advance (rule blank) c with
    | none => simp [hc] at hu
    | some c' =>
      have e : normalize c' = u := by simpa [hc] using hu
      obtain ⟨z,hz,eq⟩ := ih e
      exact ⟨z,.cons hc hz,eq⟩

theorem pull_halt [Finite A] [Finite I] {blank : A} {c : TM.Config (Letter A I) PC (Index I)}
    (h : TM.advance (rule blank) (normalize c) = none) : TM.advance (rule blank) c = none := by
  simpa only [normalize_advance, Option.map_eq_none_iff] using h

private theorem issue_rom {v : Index I → Letter A I} {b : Bool} {q : PC}
    {x y : TM.Move} {o : Option (I → A × TM.Move)} {op}
    (h : issue v b q x y o = some op) (j : Bool) : (op.2 (.inr j)).1 = v (.inr j) := by
  cases h
  rfl

private theorem rule_rom [Finite A] [Finite I] (blank : A) {v : Index I → Letter A I}
    {q : PC} {op} (h : rule blank q v = some op) (j : Bool) : (op.2 (.inr j)).1 = v (.inr j) := by
  classical
  obtain ⟨b,ph⟩ := q
  cases ph with
  | seek =>
    simp only [rule] at h
    cases hh : tagAt v b with
    | branch r o =>
      cases o <;> by_cases hm : r = readData blank v <;> simp [hh,hm] at h <;> exact issue_rom h j
    | _ => simp only [hh] at h; exact issue_rom h j
  | dest | rewind =>
    simp only [rule] at h
    cases hh : tagAt v b <;> simp only [hh] at h <;> exact issue_rom h j
  | skip =>
    simp only [rule] at h
    cases hh : tagAt v (!b) <;> simp only [hh] at h <;> exact issue_rom h j

/-- Both ROM copies retain their exact absolute contents, including physical blanks. -/
theorem rom_unchanged [Finite A] [Finite I] {blank : A}
    {x y : TM.Config (Letter A I) PC (Index I)} {n : ℕ}
    (r : Trace (TM.advance (rule blank)) x n y) (b : Bool) :
    (y.tape (.inr b)).absolute = (x.tape (.inr b)).absolute := by
  induction r with
  | nil => rfl
  | @cons x u y n h _ ih =>
    rw [ih]
    cases hw : rule blank x.pc (fun i => (x.tape i).view 0) with
    | none => simp [TM.advance,hw] at h
    | some op =>
      simp only [TM.advance,hw,Option.map_some,Option.some.injEq] at h
      subst u
      funext k
      rw [TM.Tape.absolute_apply,rule_rom blank hw]
      split
      · next e => simp [e,TM.Tape.absolute]
      · rfl

private theorem eq_of_absolute {X : Type} (a b : TM.Tape X) (hp : a.pos = b.pos)
    (h : a.absolute = b.absolute) : a = b := by
  rcases a with ⟨p,f⟩
  rcases b with ⟨q,g⟩
  change p = q at hp
  subst q
  congr 1
  funext k
  simpa [TM.Tape.absolute] using congrFun h (k+p)

private theorem romWord_absolute (blank : A) (code : List (Tag A I)) (p : ℤ) :
    (romWord blank code p).absolute = (TM.Tape.loaded (.inl blank) (code.map Sum.inr)).absolute := by
  funext k
  simp [romWord,TM.Tape.absolute,TM.Tape.loaded]

/-- Traces between ideal interpreter configurations run verbatim on finite words.
Both endpoints retain canonical finite representations, at the exact physical head
positions prescribed by the ideal execution. -/
theorem pull_loaded_trace [Finite A] [Finite I] {blank : A} {code : List (Tag A I)}
    {d d' : I → TM.Tape A} {b b' : Bool} {ph ph' : Phase} {p q p' q' : ℤ} {n : ℕ}
    (r : Trace (TM.advance (rule blank)) (conf (fetch code) d b ph p q) n
      (conf (fetch code) d' b' ph' p' q')) :
    Trace (TM.advance (rule blank)) (loadedConf blank code d b ph p q) n
      (loadedConf blank code d' b' ph' p' q') := by
  rw [← normalize_loaded blank] at r
  obtain ⟨z,hz,hn⟩ := pull_trace r
  suffices h : z = loadedConf blank code d' b' ph' p' q' by simpa [← h] using hz
  rcases z with ⟨pc,T⟩
  simp only [normalize,conf,TM.Config.mk.injEq] at hn
  obtain ⟨hp,hT⟩ := hn
  change pc = (b',ph') at hp
  subst pc
  congr 1
  funext i
  cases i with
  | inl j => exact congrFun hT (.inl j)
  | inr j =>
    have hpos := congrArg TM.Tape.pos (congrFun hT (.inr j))
    apply eq_of_absolute (T (.inr j)) (romWord blank code (if j = b' then p' else q')) hpos
    have hrom := rom_unchanged hz j
    change (T (.inr j)).absolute = (romWord blank code _).absolute at hrom ⊢
    simpa only [romWord_absolute] using hrom

/-- Normalization preserves prefix head positions, including the odd steps of any caller. -/
theorem pull_space [Finite A] [Finite I] {blank : A} {c : TM.Config (Letter A I) PC (Index I)}
    {n s : ℕ} (h : VisitsAtMost (rule blank) (normalize c) n s) :
    VisitsAtMost (rule blank) c n s := by
  obtain ⟨cells,hcard,hmem⟩ := h
  refine ⟨cells,hcard,?_⟩
  intro t ht z hz i
  have liftTrace {a b : TM.Config (Letter A I) PC (Index I)} {k : ℕ}
      (tr : Trace (TM.advance (rule blank)) a k b) :
      Trace (TM.advance (rule blank)) (normalize a) k (normalize b) := by
    induction tr with
    | nil => exact .nil _
    | cons step _ ih => exact .cons (by rw [normalize_advance,step]; rfl) ih
  exact hmem t ht (normalize z) (liftTrace hz) i

end Universal

end NearSquareRoot
end Computability
end OAI
