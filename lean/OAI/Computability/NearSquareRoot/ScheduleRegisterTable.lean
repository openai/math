import OAI.Computability.NearSquareRoot.ScheduleRegisterLookup
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxFold

/-! # An effective two-register lookup over finite tree spelling tables -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RegisterTable
open IntegerMultiplication Code CommonRegisters GeneratorSyntax

abbrev Word := List ℕ
abbrev Table := List (Word × Word)

def encode (t : List (Tree × Tree)) : Table :=
  t.map fun uv => (uv.1.spell.map ltr,uv.2.spell.map ltr)

def symbol : ℕ → Ltr
  | 0 => .bit false
  | 1 => .bit true
  | 2 => .node
  | _ => .sep

@[simp] theorem symbol_ltr (a : Ltr) : symbol (ltr a) = a := by
  rcases a with (⟨⟩|⟨⟩) | _ | _ <;> rfl

/-- Check a literal prefix, restore its tape and leave the result on register one. -/
def testStep (a : Ltr) (k : Cmd) : Cmd :=
  .look 0 fun s => if s = some a then (Prog.pop 0).join (k.join (.push 0 a)) else give 1 false

def testWord (w : Word) : Cmd := w.foldr (fun n k => testStep (symbol n) k) (give 1 true)

def literal (w : Word) : Cmd := w.foldr (fun n k => k.join (.push 0 (symbol n))) .pass

def entry (v : Word × Word) (rest : Cmd) : Cmd :=
  (testWord v.1).join (splitRoot 1 (fun b => bif b then (Code.discard 0).join (literal v.2) else rest) .pass)

def build (w : Table) := w.foldr entry .pass

def command (t : List (Tree × Tree)) := build (encode t)

theorem within {R : ℕ} (hR : 2 ≤ R) (t : Table) : Within R (build t) := by
  have ht (w : Word) : Within R (testWord w) := by
    induction w with
    | nil => exact lt_of_lt_of_le (by decide : 1 < 2) hR
    | cons a w ih =>
      change Within R (testStep (symbol a) (testWord w))
      refine ⟨by omega,fun s => ?_⟩
      dsimp only
      split <;> simp [Within,give,ih] <;> omega
  have hl (w : Word) : Within R (literal w) := by
    induction w with
    | nil => trivial
    | cons a w ih => exact ⟨ih,show 0<R by omega⟩
  induction t with
  | nil => trivial
  | cons v t ih =>
    change Within R (entry v (build t))
    simp [entry,Within,RegisterWitness.splitRoot_within,ht,hl,Code.discard,forward,forwardBody,
      ih,flood]
    omega

private abbrev setTape (r : Reg Ltr) (i : ℕ) (l : List Ltr) := Function.update r i l
private abbrev mark (r : Reg Ltr) (b : Bool) := setTape r 1 (.bit b :: r 1)

private theorem test_run (env : Env) (w : Word) (r : Reg Ltr) :
    ∃ t ≤ 8*w.length+1, Prog.Run env (testWord w) r t
      (mark r ((w.map symbol).isPrefixOf (r 0))) := by
  induction w generalizing r with
  | nil => exact ⟨1,by simp,.push⟩
  | cons a w ih =>
    let z := symbol a
    change ∃ t ≤ _, Prog.Run env (testStep z (testWord w)) _ t _
    by_cases e : (r 0).head? = some z
    · obtain ⟨tail,tail_eq⟩ := List.head?_eq_some_iff.mp e
      let rr := setTape r 0 tail
      obtain ⟨t,ht,h⟩ := ih rr
      let b := (w.map symbol).isPrefixOf tail
      change Prog.Run env (testWord w) rr t (mark rr b) at h
      have pop : Prog.Run env (.pop 0) r 1 rr := by
        simpa only [rr, tail_eq, List.tail_cons] using (Prog.Run.pop (Γ := env) (i := 0) (r := r))
      have push : Prog.Run env (.push 0 z) (mark rr b) 1 (mark r b) := by
        convert (Prog.Run.push (Γ := env) (i := 0) (x := z) (r := mark rr b)) using 1
        funext j
        by_cases h₀ : j = 0 <;> by_cases h₁ : j = 1 <;> simp_all [mark,rr,setTape,b]
      have done := pop.join (h.join push)
      refine ⟨1+(1+1+1+(1+t+1+1)),by simp at ht ⊢; omega,?_⟩
      unfold testStep
      apply Prog.Run.look
      simpa [e,tail_eq,b,z, List.isPrefixOf] using done
    · have bad : ((a::w).map symbol).isPrefixOf (r 0) = false := by
        cases he : r 0 with
        | nil => rfl
        | cons v vs =>
          have hv : v ≠ symbol a := by simpa [he,z] using e
          simp [List.isPrefixOf,hv.symm]
      refine ⟨2,by simp; omega,?_⟩
      rw [bad]
      unfold testStep
      apply Prog.Run.look (n := 1)
      simpa [e,give,mark,setTape] using (Prog.Run.push (Γ := env) (i := 1) (x := Ltr.bit false) (r := r))

private theorem literal_run (env : Env) (w : Word) (r : Reg Ltr) :
    Prog.Run env (literal w) r (3*w.length+1) (setTape r 0 (w.map symbol ++ r 0)) := by
  induction w with
  | nil => simpa [literal,setTape] using (Prog.Run.pass (Γ := env) (r := r) (A := Ltr))
  | cons a w ih =>
    let rr := setTape r 0 (w.map symbol ++ r 0)
    have h := ih.join (Prog.Run.push (Γ := env) (i := 0) (x := symbol a) (r := rr))
    convert h using 1
    · rfl
    · rw [List.length_cons]; omega
    · simp [rr,setTape]

private theorem spell_unique (x y : Tree) (r s : List Ltr) (e : x.spell++r = y.spell++s) :
    x=y ∧ r=s := by
  induction x generalizing y r s with
  | atom b =>
    cases y <;> simp_all [Tree.spell]
  | fork x₁ x₂ h₁ h₂ =>
    cases y with
    | atom b => simp [Tree.spell] at e
    | fork y₁ y₂ =>
      simp only [Tree.spell,List.cons_append,List.cons.injEq,true_and,List.append_assoc] at e
      obtain ⟨rfl,he⟩ := h₁ _ _ _ e
      obtain ⟨rfl,rfl⟩ := h₂ _ _ _ he
      exact ⟨rfl,rfl⟩

private theorem match_tree (u x : Tree) (rest : List Ltr) :
    u.spell.isPrefixOf (x.spell++rest) = decide (u=x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.isPrefixOf_iff_prefix,decide_eq_true_eq]
  exact ⟨fun ⟨t,ht⟩ => (spell_unique u x t rest ht).1,fun h => h ▸ ⟨rest,rfl⟩⟩

private theorem compare (env : Env) (u x : Tree) (r : Deck) :
    Fits env (testWord (u.spell.map ltr)) (pile 0 x r)
      (pile 1 (.atom (decide (u=x))) (pile 0 x r)) (8*u.count+1) := by
  obtain ⟨t,ht,h⟩ := test_run env (u.spell.map ltr) (letters (pile 0 x r))
  refine ⟨t,by simpa using ht,?_⟩
  simpa [letters_pile,mark,setTape,List.map_map,Function.comp_def,match_tree,Tree.spell] using h

private theorem write (env : Env) (v : Tree) (r : Deck) :
    Fits env (literal (v.spell.map ltr)) r (pile 0 v r) (3*v.count+1) := by
  refine ⟨3*v.count+1,le_rfl,?_⟩
  simpa [letters_pile,setTape,List.map_map,Function.comp_def] using
    literal_run env (v.spell.map ltr) (letters r)

def cost : List (Tree × Tree) → ℕ
  | [] => 1
  | (u,v)::t => 50*(u.count+v.count+1)+cost t

def result : List (Tree × Tree) → Tree → Tree
  | [], x => x
  | (u,v)::t, x => if u=x then v else result t x

/-- Every input, including one outside the finite table, preserves all parked data. -/
theorem run (t : List (Tree × Tree)) (x : Tree) (env : Env) (r : Deck) :
    Fits env (command t) (pile 0 x r) (pile 0 (result t x) r) (cost t) := by
  induction t with
  | nil => exact Fits.pass _
  | cons v t ih =>
    rcases v with ⟨u,v⟩
    let choose (b : Bool) : Cmd := bif b then (Code.discard 0).join (literal (v.spell.map ltr))
      else command t
    change Fits env ((testWord (u.spell.map ltr)).join (splitRoot 1 choose .pass))
      (pile 0 x r) (pile 0 (if u=x then v else result t x) r)
      (50*(u.count+v.count+1)+cost t)
    have cmp := compare env u x r
    by_cases e : u=x
    · subst u
      have ok := (fits_discard 0 x env r).join (write env v r)
      have branch := fits_bit (i := 1) (c := choose) (d := .pass) (b := true)
        (show Fits env (choose true) _ _ _ from ok)
      simp only [decide_true] at cmp
      simp only [ite_true,eq_self] at *
      exact (cmp.join branch).mono (by omega)
    · have branch := fits_bit (i := 1) (c := choose) (d := .pass) (b := false)
        (show Fits env (choose false) _ _ _ from ih)
      simp only [decide_eq_false e] at cmp
      rw [ite_eq_right e]
      exact (cmp.join branch).mono (by omega)

/-- The contract for any key occurring in the table, using the same selection
convention as the single-register lookup. -/
theorem run_lookup (t : List (Tree × Tree)) (x y : Tree) (hmem : (x,y) ∈ t)
    (hread : RegisterLookup.read t x = y) (env : Env) (r : Deck) :
    Fits env (command t) (pile 0 x r) (pile 0 y r) (cost t) := by
  have agrees : ∀ t : List (Tree × Tree), (x,y) ∈ t → result t x = RegisterLookup.read t x := by
    intro t
    induction t with
    | nil => simp
    | cons uv t ih =>
      rcases uv with ⟨u,v⟩
      intro h
      by_cases e : u=x
      · simp [e,result,RegisterLookup.read]
      · have tail : (x,y) ∈ t := (List.mem_cons.mp h).resolve_left (fun he => e (congrArg Prod.fst he).symm)
        simp [e,result,RegisterLookup.read,ih tail]
  simpa only [agrees t hmem,hread] using run t x env r

end RegisterTable

end NearSquareRoot
end Computability
end OAI
