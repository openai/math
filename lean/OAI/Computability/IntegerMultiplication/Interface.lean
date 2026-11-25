import OAI.Computability.IntegerMultiplication.Goal
import OAI.Computability.IntegerMultiplication.Code.Task
import OAI.Computability.IntegerMultiplication.Prog.Compile
import Mathlib.Tactic.DeriveFintype

namespace OAI
namespace Computability
namespace IntegerMultiplication

/- Standard conversion for two input strings and one output. Specialized to Boolean letters.
Costs linear. -/

namespace Interface
open Code

deriving instance Fintype for Ltr

private def raw (l : List Ltr) : Reg Ltr := fun i => if i=0 then l else []

theorem letters_word (b : Bool) : send b=Tree.atom b := rfl

private theorem raw_push (l) (a : Ltr) :
    Function.update (raw l) 0 (a::raw l 0)=raw (a::l) := by
  funext i
  by_cases h : i=0
  · subst_vars; simp [raw]
  · simp [raw, h]

private theorem raw_pop (l) (a : Ltr) :
    Function.update (raw (a::l)) 0 (raw (a::l) 0).tail=raw l := by
  funext i; by_cases h : i=0
  · subst_vars; simp [raw]
  · simp [raw, h]

private abbrev Does (c : Cmd) (E : Env) (l w : List Ltr) (k) :=
  Prog.Run E c (raw l) k (raw w)

private theorem Does.push (E a s) : Does (.push 0 a) E s (a::s) 1 := by unfold Does; rw [← raw_push]; exact .push

private theorem Does.pop (E a s) : Does (.pop 0) E (a::s) s 1 := by unfold Does; rw [← raw_pop s a]; exact .pop

private theorem Does.br (a : Ltr) (f : Option Ltr → Cmd) (E x t y)
    (h : Does (f (some a)) E x y t) :
    Does (.look 0 fun v => Prog.join (.pop 0) (f v)) E (a::x) y (1+(1+1+1+t)) := by
  apply Prog.Run.look (c := fun v => .join _ _)
  rw [show ((raw (a::x)) 0).head? = some a from rfl]
  exact Prog.Run.join (Does.pop ..) h

private def inList (E₁ E₂ : Cmd) : Cmd :=
  .look 0 fun v => .join (.pop 0) <| match v with
  | some (.bit b) => .join (.again 0) (.join (.push 0 (.bit b)) (.push 0 .node))
  | some .sep => E₁
  | _ => E₂
-- if none, preceding pop allowed (empty no effect).

private def codeY : Cmd := inList (.pass) (.push 0 (.bit false))
private def codeX : Cmd := inList (.join (.tie codeY) (.push 0 (.bit false))) (.pass)

private theorem inList_cost (E₁ E₂ : Cmd) (s m : List Ltr) (L : ℕ) (E : Env)
    (h : Does (inList E₁ E₂) (inList E₁ E₂::E) s (Ltr.bit false::m) L) (x : List Bool) :
    Does (inList E₁ E₂) (inList E₁ E₂::E) (x.map Ltr.bit ++ s) ((send x).spell ++ m)
      (11*x.length+L) := by
  induction x with
  | nil => simpa [Tree.spell] using h
  | cons x l ih =>
    have he := Prog.Run.again (Γ:=inList E₁ E₂::E) (i:=0) (c:=inList E₁ E₂) (by simp) ih
    have hw := Prog.Run.join he (Prog.Run.join (Does.push _ (.bit x) _) (Does.push _ .node _))
    simp only [List.map_cons,List.cons_append,send_cons,letters_word,Tree.spell,List.append_assoc,List.length_cons]
    simp only [List.nil_append]
    -- cost: br4 + join two ops=4 + recursion via again1 + 2 join =7 ->11
    rw [show 11*(l.length+1)+L = 1+(1+1+1+(1+(1+(11*l.length+L))+1+(1+1+1+1))) by omega]
    exact Does.br (.bit x) _ _ _ _ _ hw

private theorem Ybase (E) : Does codeY (codeY::E) [] [.bit false] 5 := by
  have hpop : Does (.pop 0) (codeY::E) [] [] 1 := by
    have e : Function.update (raw []) 0 ((raw []) 0).tail=raw [] := by
      funext i
      cases i <;> simp [raw]
    simpa only [e] using (Prog.Run.pop (Γ:=codeY::E) (i:=0) (r:=raw []))
  change Does (.look 0 _) _ [] _ (1+(1+1+1+1))
  apply Prog.Run.look
  exact Prog.Run.join hpop (Does.push ..)

private theorem Xbase (y : List Bool) (E) :
    Does codeX (codeX::E) (.sep::y.map Ltr.bit) (.bit false::(send y).spell)
      (13+11*y.length) := by
  -- br4 + joining tieY (1+11len+5) and push1 gives 13
  have e := Prog.Run.tie (by simpa only [List.append_nil] using inList_cost _ _ [] [] 5 (codeX::E) (Ybase (codeX::E)) y)
  have h := Prog.Run.join e (Does.push _ (.bit false) _)
  rw [show 13+11*y.length=1+(1+1+1+(1+(1+(11*y.length+5))+1+1)) by omega]
  exact Does.br Ltr.sep _ _ _ _ _ h

private def go : Cmd := Prog.join (.tie codeX) (.push 0 .node)

theorem load (x y : List Bool) (E) :
    let t := 17+11*(x.length+y.length)
    Does go E (x.map Ltr.bit ++ .sep::y.map Ltr.bit) ((send (x,y)).spell) t := by
  have h := inList_cost _ _ _ _ _ _ (Xbase y E) x
  have g := Prog.Run.join (Prog.Run.tie h) (Does.push E Ltr.node _)
  dsimp only
  rw [show 17+11*(x.length+y.length)=1+(1+(11*x.length+(13+11*y.length)))+1+1 by omega]
  exact g

private def outList : Cmd :=
  .look 0 fun v => .join (.pop 0) <| match v with
  | some .node =>
    .look 0 fun v => .join (.pop 0) <| match v with
    | some (.bit b) => .join (.again 0) (.push 0 (.bit b))
    | _ => .pass
  | _ => .pass

private theorem unload (x : List Bool) (E : Env) :
    Does outList (outList::E) (send x).spell (x.map Ltr.bit) (5+12*x.length) := by
  induction x with
  | nil =>
    change Does _ _ (.bit false::[]) [] (1+(1+1+1+1))
    apply Does.br
    exact Prog.Run.pass
  | cons b x ih =>
    have h := Prog.Run.join (Prog.Run.again (i:=0) (Γ:=outList::E) (c:=outList) (by simp) ih) (Does.push _ (Ltr.bit b) _)
    -- 2 branches =8 plus join+again+push=4
    simp only [List.length_cons]
    rw [show 5+12*(x.length+1)=1+(1+1+1+(1+(1+1+1+(1+(1+(5+12*x.length))+1+1)))) by omega]
    apply Does.br .node
    apply Does.br (.bit b)
    exact h

abbrev Pair := List Bool × List Bool

/-- A machine existence statement for any specified inputs, outputs and time budget.
Always given conventional msb-first bits, output tape initially and otherwise blank.
-/
def Promise (Y : Type*) (q : Y → Pair) (w : Y → List Bool) (bound : Y → ℕ) : Prop :=
  ∃ (A Q I : Type) (_ : Finite A) (_ : Finite Q) (_ : Finite I)
    (bit : Bool → A) (sep blank : A) (inp out : I)
    (start : Q) (m : TM.Rule A Q I)
    (C : ℕ),
    Function.Injective bit ∧ (∀ b, bit b ≠ blank ∧ bit b ≠ sep) ∧ sep ≠ blank ∧
    ∀ y : Y, ∃ (finish : TM.Config A Q I) (t : ℕ),
      (∃ initTape : I → TM.Tape A,
        initTape inp = TM.Tape.loaded blank ((q y).1.map bit ++ [sep] ++ (q y).2.map bit) ∧
        (∀ i, i ≠ inp → initTape i = TM.Tape.loaded blank []) ∧
        Trace (TM.advance m) { pc := start, tape := initTape } t finish) ∧
      TM.advance m finish = none ∧
      TM.whole blank ((w y).map bit) (finish.tape out) ∧
      t ≤ C * (bound y+1)

private theorem frame (x : Tree) :
    letters (pile 0 x (fun _ => [])) = raw x.spell := by
  funext i; by_cases h : i=0
  · subst i; simp [letters,raw]
  · simp [letters,raw,h]

/-- Cost includes linear in lengths of both input and output (could absorb output from Task). -/
theorem Promise.stack {Y} {b : Y → ℕ} {q w} (h : Task b (fun i => send (q i : Pair)) (fun i => send (w i : List Bool))) :
    Promise Y q w (fun i => b i+(q i).1.length+(q i).2.length+(w i).length) := by
  classical
  obtain ⟨c,C,h⟩ := h
  let pr := go.join (c.join (.tie outList))
  obtain ⟨A,Q,I,_,_,_,sym,blank,inp,out,_,start,m,hi,hb,hg⟩ := Prog.release pr
  refine ⟨A,Q,I,inferInstance,inferInstance,inferInstance,sym ∘ Ltr.bit,sym .sep,blank,inp,out,start,m,
    100+2*C,hi.comp (fun _ _ => Ltr.bit.inj), (fun b => ⟨hb _,hi.ne (by simp)⟩), hb _, fun y => ?_⟩
  rcases e : q y with ⟨i,j⟩
  obtain ⟨t,ht,hr⟩ := h y [] (fun _ => [])
  simp only [e, frame] at hr
  have hd := Prog.Run.tie (unload (w y) [])
  have he := Prog.Run.join (load i j []) (Prog.Run.join hr hd)
  obtain ⟨z,T,u,v,hp,hm,hd'⟩ := hg _ _ _ he
  simp only [raw,↓reduceIte, List.length_map] at hp hd'
  refine ⟨z,_,⟨T,?_,v,hp⟩,hm,?_,?_⟩
  · simpa only [e,List.map_append,List.map_cons,List.map_map, List.append_assoc,List.cons_append,List.nil_append] using u
  · simpa only [List.map_map] using hd'
  -- hp input goal Trace mismatches map? hp passed, only initial equation
  dsimp only
  rw [e]
  rw [Nat.add_mul]
  dsimp only
  simp only [Nat.mul_add,Nat.mul_one, Nat.mul_assoc] at ht ⊢
  omega

end Interface

end IntegerMultiplication
end Computability
end OAI
