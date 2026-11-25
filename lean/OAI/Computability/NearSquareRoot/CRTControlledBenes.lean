import OAI.Computability.IntegerMultiplication.Code.Iter
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-! # Beneš routing for controlled local address permutations

The network uses a fixed sequence of target positions for each block width. At a switch
only the target changes, by XOR with a function of the remaining bits.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes
open Finset

/-- Input and output switches can separate the edges of a permutation into two lanes.
The Hall condition counts both edges at each port, so parallel edges cause no exception. -/
theorem exists_lane_controls {A : Type*} [Fintype A] (p : Equiv.Perm (Bool × A)) :
    ∃ l r : A → Bool, ∀ x : Bool × A, (x.1 ^^ l x.2) = ((p x).1 ^^ r (p x).2) := by
  classical
  let neigh (a : A) := (univ : Finset Bool).image fun b => (p (b,a)).2
  have hh (s : Finset A) : s.card ≤ (s.biUnion neigh).card := by
    have : (univ ×ˢ s : Finset (Bool × A)).card ≤ (univ ×ˢ (s.biUnion neigh) : Finset (Bool × A)).card :=
      card_le_card_of_injOn p (by
        rintro ⟨b,a⟩ hx
        apply mem_product.mpr
        exact ⟨mem_univ _, mem_biUnion.mpr ⟨a, (mem_product.mp hx).2, mem_image.mpr ⟨b, mem_univ _, rfl⟩⟩⟩)
        p.injective.injOn
    simpa using this
  obtain ⟨f,hf,hm⟩ := (all_card_le_biUnion_card_iff_existsInjective' neigh).mp hh
  let g := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  have pick (a : A) : ∃ b : Bool, (p (b,a)).2 = g a := by
    obtain ⟨b,_,hb⟩ := mem_image.mp (hm a)
    exact ⟨b,hb⟩
  choose l hl using pick
  let r (y : A) := (p (l (g.symm y),g.symm y)).1
  have matchPair (a : A) : p (l a,a) = (r (g a), g a) := by
    apply Prod.ext (by simp [r]) (hl a)
  refine ⟨l, r, ?_⟩
  rintro ⟨b,a⟩
  have test : b = l a ↔ (p (b,a)).1 = r (p (b,a)).2 := by
    constructor
    · rintro rfl
      rw [matchPair]
    · intro hb
      let y := (p (b,a)).2
      have he : p (b,a) = p (l (g.symm y),g.symm y) := by
        rw [matchPair, g.apply_symm_apply]
        exact Prod.ext hb rfl
      have h₁ : b = l (g.symm y) := congrArg Prod.fst (p.injective he)
      have h₂ : a = g.symm y := congrArg Prod.snd (p.injective he)
      rwa [← h₂] at h₁
  generalize h₁ : l a = c at *
  generalize h₂ : (p (b,a)).1 = z at *
  generalize h₃ : r (p (b,a)).2 = w at *
  cases b <;> cases c <;> cases z <;> cases w <;> simp_all

/-- Each edge prescribes the XOR of the colors at its endpoints. -/
structure Equation (V : Type*) where
  left : V
  right : V
  parity : Bool

def Equation.Valid {V : Type*} (eq : Equation V) (c : V → Bool) : Prop :=
  (c eq.left ^^ c eq.right) = eq.parity

section Compile
variable {V : Type*} [DecidableEq V]

/-- The table stores a component name and relative color for each port. -/
abbrev Labels (V : Type*) := List (V × (V × Bool))

def label (t : Labels V) (v : V) : V × Bool := (t.lookup v).getD (v,false)

def amend (x y : V × Bool) (parity : Bool) (v : V × Bool) : V × Bool :=
  if v.1 = y.1 then (x.1, v.2 ^^ (x.2 ^^ y.2 ^^ parity)) else v

/-- Two sequential reads obtain the endpoint labels. One pass renames one component,
flipping all its relative colors when the two previous choices of orientation disagree. -/
def joinLabels (e : Equation V) (t : Labels V) : Labels V :=
  let u := label t e.left
  let v := label t e.right
  t.map fun row => (row.1, amend u v e.parity row.2)

private theorem lookup_rows {A B : Type*} (T : List (V × A)) (f : A → B) (v : V) :
    ((T.map fun p => (p.1,f p.2)).lookup v) = (T.lookup v).map f := by
  induction T with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨a,b⟩
    by_cases h : v = a
    · subst v; simp
    · have hb : (v == a) = false := by simpa using h
      simp [List.lookup_cons, hb, ih]

private theorem label_join {t : Labels V} (full : ∀ v : V, v ∈ t.map Prod.fst)
    (e : Equation V) (v : V) :
    label (joinLabels e t) v = amend (label t e.left) (label t e.right) e.parity (label t v) := by
  simp only [label, joinLabels, lookup_rows]
  cases h : t.lookup v with
  | none => obtain ⟨row, hrow, hv⟩ := List.mem_map.mp (full v)
            have hn := List.lookup_eq_none_iff.mp h row hrow
            simp [hv] at hn
  | some _ => rfl

private theorem complete_join (e : Equation V) (t : Labels V) :
    (joinLabels e t).map Prod.fst = t.map Prod.fst := by simp [joinLabels, List.map_map]

/-- A global solution induces one constant relative orientation for each component. -/
private def Coherent (t : Labels V) (w : V → Bool) : Prop :=
  ∀ u v, (label t u).1 = (label t v).1 →
    ((label t u).2 ^^ w u) = ((label t v).2 ^^ w v)

/-- Joined ports have the same component name. -/
private theorem joined {t : Labels V} (ht : ∀ v : V, v ∈ t.map Prod.fst) (e : Equation V) :
    (label (joinLabels e t) e.left).1 = (label (joinLabels e t) e.right).1 := by
  simp only [label_join ht, amend, ite_true]
  split <;> rfl

private theorem keep_join {t : Labels V} (ht : ∀ v : V, v ∈ t.map Prod.fst)
    (e : Equation V) {u v : V} (h : (label t u).1 = (label t v).1) :
    (label (joinLabels e t) u).1 = (label (joinLabels e t) v).1 := by
  simp only [label_join ht, amend, h]
  split <;> simp_all

private theorem phase_shift_both (a b u v t : Bool) :
    (a ^^ u) = (b ^^ v) → (a ^^ t ^^ u) = (b ^^ t ^^ v) := by revert a b u v t; decide

private theorem phase_join (a b l r u v x y p : Bool) :
    (a ^^ u) = (r ^^ y) → (l ^^ x) = (b ^^ v) → (x ^^ y) = p →
    (a ^^ (l ^^ r ^^ p) ^^ u) = (b ^^ v) := by revert a b l r u v x y p; decide

private theorem phase_correct (a b u v p : Bool) :
    (a ^^ u) = (b ^^ v) → (u ^^ v) = p → (a ^^ b) = p := by revert a b u v p; decide

private theorem coherent_join {t : Labels V} (ht : ∀ v : V, v ∈ t.map Prod.fst)
    (w : V → Bool) (hc : Coherent t w) (e : Equation V) (he : e.Valid w) :
    Coherent (joinLabels e t) w := by
  intro u v
  simp only [label_join ht, amend]
  by_cases hu : (label t u).1 = (label t e.right).1 <;>
    by_cases hv : (label t v).1 = (label t e.right).1 <;>
    simp only [hu, hv, ite_true, ite_false] <;> intro hh
  · have h := hc u v (hu.trans hv.symm)
    exact phase_shift_both _ _ _ _ _ h
  · have h₁ := hc u e.right hu
    have h₂ := hc e.left v hh
    unfold Equation.Valid at he
    exact phase_join _ _ _ _ _ _ _ _ _ h₁ h₂ he
  · have h₁ := hc v e.right hv
    have h₂ := hc u e.left hh
    unfold Equation.Valid at he
    exact (phase_join _ _ _ _ _ _ _ _ _ h₁ h₂.symm he).symm
  · exact hc u v hh

def compileEquations (eqs : List (Equation V)) (t : Labels V) : Labels V :=
  eqs.foldl (fun s e => joinLabels e s) t

@[simp] theorem compile_length (eqs : List (Equation V)) (t : Labels V) :
    (compileEquations eqs t).length = t.length := by
  induction eqs generalizing t with
  | nil => rfl
  | cons e tl ih =>
    change (compileEquations tl (joinLabels e t)).length = _
    simpa [joinLabels] using ih (joinLabels e t)

private def Joined (t : Labels V) (u v : V) : Prop := (label t u).1 = (label t v).1

private theorem compile_invariant (es : List (Equation V)) (w : V → Bool)
    (hw : ∀ e ∈ es, e.Valid w) (t : Labels V) (ht : ∀ v : V, v ∈ t.map Prod.fst)
    (hc : Coherent t w) :
    let t' := compileEquations es t
    Coherent t' w ∧ (∀ u v, Joined t u v → Joined t' u v) ∧
      ∀ e ∈ es, Joined t' e.left e.right := by
  induction es generalizing t with
  | nil => exact ⟨hc, fun _ _ h => h, by simp⟩
  | cons e es ih =>
    have hi := ih (fun f hf => hw _ (List.mem_cons_of_mem _ hf)) (joinLabels e t)
      (complete_join e t ▸ ht) (coherent_join ht w hc e (hw _ (by simp)))
    refine ⟨hi.1, fun u v h => hi.2.1 u v (keep_join ht e h), ?_⟩
    intro f hf
    rcases List.mem_cons.mp hf with h | h
    · subst f
      exact hi.2.1 _ _ (joined ht e)
    · exact hi.2.2 _ h

def initialLabels (ports : List V) : Labels V := ports.map fun v => (v,v,false)

private theorem label_initial (ports : List V) (v : V) :
    label (initialLabels ports) v = (v,false) := by
  induction ports with
  | nil => rfl
  | cons w tl ih =>
    by_cases h : v = w
    · subst v; simp [initialLabels,label]
    · have hb : (v == w) = false := by simpa using h
      simpa only [initialLabels,List.map_cons,label,List.lookup_cons,hb] using ih

/-- One list pass per equation suffices, with at most three row traversals per pass.
This counts table-row inspections, including both endpoint lookups and the rewrite. -/
def compileRowBudget (es : List (Equation V)) (t : Labels V) : ℕ :=
  match es with
  | [] => 0
  | e :: tl => 3*t.length + compileRowBudget tl (joinLabels e t)

theorem compileRowBudget_eq (es : List (Equation V)) (t : Labels V) :
    compileRowBudget es t = 3*es.length*t.length := by
  induction es generalizing t with
  | nil => simp [compileRowBudget]
  | cons e es ih => simp [compileRowBudget, joinLabels, ih]; ring

theorem compile_correct (ports : List V) (hports : ∀ v, v ∈ ports) (es : List (Equation V))
    (w : V → Bool) (hw : ∀ e ∈ es, e.Valid w) :
    ∀ e ∈ es, e.Valid (fun v => (label (compileEquations es (initialLabels ports)) v).2) := by
  have ht : ∀ v : V, v ∈ (initialLabels ports).map Prod.fst := by simpa [initialLabels] using hports
  have hc : Coherent (initialLabels ports) w := by
    intro u v h
    simpa only [label_initial] using congrArg (fun z => false ^^ w z) (show u = v by simpa only [label_initial] using h)
  have hi := compile_invariant es w hw (initialLabels ports) ht hc
  intro e he
  have hc' := hi.1 e.left e.right (hi.2.2 _ he)
  have he' := hw _ he
  unfold Equation.Valid at *
  exact phase_correct _ _ _ _ _ hc' he'

end Compile

/-- Left vertices are input pairs, right vertices output pairs. One equation per
input edge states which endpoint switch phases must differ. -/
def portEquation {A : Type*} (p : Equiv.Perm (Bool × A)) (x : Bool × A) : Equation (Bool × A) :=
  ⟨(false,x.2), (true,(p x).2), x.1 ^^ (p x).1⟩

def portTable {A : Type*} [DecidableEq A] (p : Equiv.Perm (Bool × A)) (ports : List (Bool × A)) :
    Labels (Bool × A) := compileEquations (ports.map (portEquation p)) (initialLabels ports)

private theorem lane_parity (a b c d : Bool) :
    ((b ^^ d) = (a ^^ c)) ↔ ((a ^^ b) = (c ^^ d)) := by revert a b c d; decide

theorem portTable_correct {A : Type*} [Fintype A] [DecidableEq A]
    (p : Equiv.Perm (Bool × A)) (ports : List (Bool × A)) (hports : ∀ v, v ∈ ports) :
    ∀ x : Bool × A, (x.1 ^^ (label (portTable p ports) (false,x.2)).2) =
      ((p x).1 ^^ (label (portTable p ports) (true,(p x).2)).2) := by
  obtain ⟨l,r,h⟩ := exists_lane_controls p
  let w (v : Bool × A) := if v.1 then r v.2 else l v.2
  have hw : ∀ e ∈ ports.map (portEquation p), e.Valid w := by
    intro _ he
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp he
    exact (lane_parity ..).mpr (h x)
  intro x
  exact (lane_parity ..).mp (compile_correct ports hports _ w hw _
    (List.mem_map.mpr ⟨x,hports x,rfl⟩))

theorem portTable_row_bound {A : Type*} [DecidableEq A]
    (p : Equiv.Perm (Bool × A)) (ports : List (Bool × A)) :
    compileRowBudget (ports.map (portEquation p)) (initialLabels ports) =
      3 * ports.length^2 := by simp [compileRowBudget_eq,initialLabels]; ring

abbrev Word (d : ℕ) := Fin d → Bool

/-- Lexicographic enumeration used to build the switch tables. -/
def words : (d : ℕ) → List (Word d)
  | 0 => [Fin.elim0]
  | n+1 => ((words n).map (Fin.cons false)) ++ ((words n).map (Fin.cons true))

theorem words_all (d : ℕ) (x : Word d) : x ∈ words d := by
  induction d with
  | zero => simp [words,Subsingleton.elim x Fin.elim0]
  | succ d ih =>
    obtain ⟨⟨b,v⟩,rfl⟩ := (Fin.consEquiv (fun _ : Fin (d+1) => Bool)).surjective x
    cases b <;> simp [words, List.mem_map, Fin.consEquiv, ih]

@[simp] theorem words_length (d : ℕ) : (words d).length = 2^d := by
  induction d with
  | zero => rfl
  | succ d ih => simp [words,ih,pow_succ]; omega

private def ports (d : ℕ) : List (Bool × Word d) :=
  (words d).map (Prod.mk false) ++ (words d).map (Prod.mk true)

private theorem ports_all (d : ℕ) (x : Bool × Word d) : x ∈ ports d := by
  rcases x with ⟨_ | _,x⟩ <;> simp [ports,words_all]

/-- A layer chooses its switch using only bits different from the target. -/
structure Switch {d : ℕ} (i : Fin d) where
  control : Word d → Bool
  reads : ∀ x y, (∀ j, j ≠ i → x j = y j) → control x = control y

def Switch.apply {d : ℕ} {i : Fin d} (s : Switch i) (x : Word d) : Word d :=
  Function.update x i (x i ^^ s.control x)

private def headSwitch {d : ℕ} (c : Word d → Bool) : Switch (0 : Fin (d+1)) where
  control x := c (Fin.tail x)
  reads _x _y h := congrArg c (funext fun i => h i.succ (Fin.succ_ne_zero _))

@[simp] private theorem head_apply {d : ℕ} (c : Word d → Bool) (b : Bool) (x : Word d) :
    (headSwitch c).apply (Fin.cons b x) = Fin.cons (b ^^ c x) x := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [headSwitch, Switch.apply]

private def liftSwitch {d : ℕ} {i : Fin d} (s : Bool → Switch i) : Switch i.succ where
  control x := (s (x 0)).control (Fin.tail x)
  reads x y h := by
    rw [h 0 (Fin.succ_ne_zero _).symm]
    exact (s (y 0)).reads _ _ fun j hj => h _ (Fin.succ_inj.not.mpr hj)

@[simp] private theorem lift_apply {d : ℕ} {i : Fin d} (s : Bool → Switch i) (b : Bool) (x : Word d) :
    (liftSwitch s).apply (Fin.cons b x) = Fin.cons b ((s b).apply x) := by
  funext j
  refine Fin.cases ?_ (fun q => ?_) j
  · simp [Switch.apply, Function.update_of_ne (Fin.succ_ne_zero i).symm]
  · by_cases h : q = i
    · subst q
      simp [Switch.apply, liftSwitch]
    · simp [Switch.apply, h]

/-- The type fixes the target position of every layer. -/
inductive Network {d : ℕ} : List (Fin d) → Type
  | nil : Network []
  | cons {i is} (s : Switch i) (rest : Network is) : Network (i :: is)

def Network.run {d : ℕ} {is : List (Fin d)} (c : Network is) (x : Word d) : Word d :=
  match c with
  | .nil => x
  | .cons s rest => rest.run (s.apply x)

def Network.append {d : ℕ} {l r : List (Fin d)} (p : Network l) (q : Network r) : Network (l ++ r) :=
  match p with
  | .nil => q
  | .cons s p => .cons s (p.append q)

theorem Network.run_append {d : ℕ} {l r : List (Fin d)} (p : Network l) (q : Network r) (x : Word d) :
    (p.append q).run x = q.run (p.run x) := by
  induction p generalizing x with
  | nil => rfl
  | cons _ _ ih => exact ih _

def Network.first {d : ℕ} {i : Fin d} {l : List (Fin d)} : Network (i::l) → Switch i
  | .cons s _ => s

def Network.rest {d : ℕ} {i : Fin d} {l : List (Fin d)} : Network (i::l) → Network l
  | .cons _ p => p

def Network.lift {d : ℕ} (l : List (Fin d)) (c : Bool → Network l) : Network (l.map Fin.succ) :=
  match l with
  | [] => .nil
  | _ :: is => .cons (liftSwitch fun b => (c b).first) (Network.lift is fun b => (c b).rest)

theorem Network.run_lift {d : ℕ} (l : List (Fin d)) (c : Bool → Network l) (b : Bool) (x : Word d) :
    (Network.lift l c).run (Fin.cons b x) = Fin.cons b ((c b).run x) := by
  induction l generalizing x with
  | nil => cases c b; rfl
  | cons i is ih =>
    simp only [Network.lift, Network.run, lift_apply]
    rw [ih]
    cases c b
    rfl

/-- Flip a head bit according to the tail of the address. -/
def port {A : Type*} (c : A → Bool) : Equiv.Perm (Bool × A) where
  toFun x := (x.1 ^^ c x.2, x.2)
  invFun x := (x.1 ^^ c x.2, x.2)
  left_inv x := by rcases x with ⟨b,x⟩; simp
  right_inv x := by rcases x with ⟨b,x⟩; simp

private structure Split {A : Type*} (p : Equiv.Perm (Bool × A)) where
  left : A → Bool
  right : A → Bool
  lane : Bool → Equiv.Perm A
  factor : ∀ b x, p (b,x) = port right (b ^^ left x, lane (b ^^ left x) x)

private def split {A : Type*} [Fintype A] [DecidableEq A] (p : Equiv.Perm (Bool × A))
    (rows : List (Bool × A)) (allRows : ∀ v, v ∈ rows) : Split p := by
  let T := portTable p rows
  let l (x : A) := (label T (false,x)).2
  let r (x : A) := (label T (true,x)).2
  let e := ((port l).trans p).trans (port r)
  have e_fst (x : Bool × A) : (e x).1 = x.1 := by
    have h := portTable_correct p rows allRows (port l x)
    change ((x.1 ^^ l x.2) ^^ l x.2) = (e x).1 at h
    simpa using h.symm
  have ei_fst (x : Bool × A) : (e.symm x).1 = x.1 := by simpa using (e_fst (e.symm x)).symm
  let q (b : Bool) : Equiv.Perm A :=
    { toFun x := (e (b,x)).2
      invFun x := (e.symm (b,x)).2
      left_inv x := by
        have he : (b,(e (b,x)).2) = e (b,x) := Prod.ext (e_fst (b,x)).symm rfl
        change (e.symm (b,(e (b,x)).2)).2 = x
        rw [he, e.symm_apply_apply]
      right_inv x := by
        have he : (b,(e.symm (b,x)).2) = e.symm (b,x) := Prod.ext (ei_fst (b,x)).symm rfl
        change (e (b,(e.symm (b,x)).2)).2 = x
        rw [he, e.apply_symm_apply] }
  have e_eq (b : Bool) (x : A) : e (b,x) = (b, q b x) := Prod.ext (e_fst _) rfl
  refine ⟨l,r,q,?_⟩
  intro b x
  have he := congrArg (port r).symm (e_eq (b ^^ l x) x)
  simpa [e,port] using he

/-- The common schedule across blocks of a given width. -/
def positions : (d : ℕ) → List (Fin d)
  | 0 => []
  | 1 => [0]
  | d+2 => 0 :: (positions (d+1)).map Fin.succ ++ [0]

@[simp] theorem positions_length (d : ℕ) : (positions d).length = 2*d-1 := by
  induction d using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more d _ h => simp [positions,h]; omega

private abbrev pair {d : ℕ} := Fin.consEquiv (fun _ : Fin (d+1) => Bool)

private def route_one (p : Equiv.Perm (Word 1)) :
    {c : Network (positions 1) // ∀ x, c.run x = p x} := by
  let c := p (fun _ => false) 0
  have hn : p (fun _ => true) 0 ≠ c := by
    intro h
    have he : p (fun _ => true) = p (fun _ => false) := by
      funext i
      fin_cases i
      exact h
    have := congrFun (p.injective he) 0
    contradiction
  refine ⟨.cons (headSwitch (fun _ => c)) .nil, ?_⟩
  intro x
  have xconst : x = (fun _ => x 0) := by funext i; fin_cases i; rfl
  funext i
  fin_cases i
  change (headSwitch _).apply x 0 = p x 0
  simp only [Switch.apply, Function.update_self,headSwitch]
  conv_rhs => rw [xconst]
  cases hx : x 0 with
  | false => simp [c]
  | true =>
    cases hz : p (fun _ : Fin 1 => true) 0 <;> cases hc : c <;> simp_all

/-- Compile a local permutation from its forward and inverse maps. Every recursive lane
uses both maps of its parent, and its switch decisions come from sequential table passes. -/
def compile : (d : ℕ) → (p : Equiv.Perm (Word d)) →
    {c : Network (positions d) // ∀ x, c.run x = p x}
  | 0, _ => ⟨.nil,fun _ => Subsingleton.elim _ _⟩
  | 1, p => route_one p
  | d+2, p => by
    let f := (pair.trans p).trans pair.symm
    let spl := split f (ports (d+1)) (ports_all _)
    let innFalse := compile (d+1) (spl.lane false)
    let innTrue := compile (d+1) (spl.lane true)
    let inner (b : Bool) := if b then innTrue.val else innFalse.val
    have hi (b : Bool) (x : Word (d+1)) : (inner b).run x = spl.lane b x := by
      cases b
      · exact innFalse.property x
      · exact innTrue.property x
    let inside := Network.lift (positions (d+1)) inner
    refine ⟨.cons (headSwitch spl.left) (inside.append (.cons (headSwitch spl.right) .nil)), ?_⟩
    intro x
    obtain ⟨⟨b,w⟩,rfl⟩ := pair.surjective x
    have hp := congrArg pair (spl.factor b w)
    change pair (pair.symm (p (pair (b,w)))) = _ at hp
    rw [Equiv.apply_symm_apply] at hp
    change (inside.append _).run ((headSwitch spl.left).apply (Fin.cons b w)) = p (pair (b,w))
    rw [Network.run_append, head_apply, Network.run_lift, hi]
    change (headSwitch spl.right).apply (Fin.cons _ _) = _
    rw [head_apply, hp]
    rfl

/-- Every block permutation admits the same target sequence, including the inverse.
Each stage's decision is independent of the bit it toggles. -/
theorem route (d : ℕ) (p : Equiv.Perm (Word d)) :
    ∃ c : Network (positions d), ∀ x, c.run x = p x :=
  ⟨(compile d p).val, (compile d p).property⟩

/-- The switch of a given stage, with identity padding when the block has finished. -/
def Network.stage {d : ℕ} {is : List (Fin d)} (c : Network is) (t : ℕ) : Word d → Word d :=
  match c, t with
  | .nil, _ => id
  | .cons g _, 0 => g.apply
  | .cons _ gs, t+1 => gs.stage t

private theorem run_stages {d : ℕ} {is : List (Fin d)} (c : Network is) (n : ℕ)
    (hn : is.length ≤ n) (x : Word d) :
    (List.range n).foldl (fun x t => c.stage t x) x = c.run x := by
  induction c generalizing n x with
  | nil =>
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      exact ih (Nat.zero_le _)
  | cons g tail ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
      apply ih
      simpa using hn

/-- At a common stage each block executes at most one targeted XOR, with its switch
depending only on the supplied external controls and the other bits of this block. -/
def blockStage {B X : Type*} (width : B → ℕ) (perm : (i : B) → X → Equiv.Perm (Word (width i)))
    (q : X) (t : ℕ) (x : (i : B) → Word (width i)) : (i : B) → Word (width i) :=
  fun i => (compile _ (perm i q)).val.stage t (x i)

theorem parallel_routing {B X : Type*} (width : B → ℕ)
    (perm : (i : B) → X → Equiv.Perm (Word (width i))) (q : X) (stages : ℕ)
    (h : ∀ i, 2*width i-1 ≤ stages) (x : (i : B) → Word (width i)) :
    (List.range stages).foldl (fun x t => blockStage width perm q t x) x =
      fun i => perm i q (x i) := by
  funext i
  have apply_fold (l : List ℕ) (v : (i : B) → Word (width i)) :
      l.foldl (fun x t => blockStage width perm q t x) v i =
        l.foldl (fun y t => (compile _ (perm i q)).val.stage t y) (v i) := by
    induction l generalizing v with
    | nil => rfl
    | cons s l ih => exact ih (blockStage width perm q s v)
  rw [apply_fold, run_stages _ _ (by simpa using h i)]
  exact (compile _ (perm i q)).property _

/-- Total row traversal budget for coloring at all nodes, including both recursive lanes. -/
def coloringBudget : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | d+2 => 3*(2^(d+2))^2 + 2*coloringBudget (d+1)

theorem coloringBudget_le (d : ℕ) : coloringBudget d ≤ 6*(2^d)^2 := by
  induction d using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more d _ ih =>
    rw [coloringBudget]
    rw [show 2^(d+2) = 2^(d+1)*2 by rw [pow_succ]]
    nlinarith

section Tape

open IntegerMultiplication.Code
variable {V : Type} [Codec V] [DecidableEq V] (v₀ : V)
  (eqCost : Poly (fun t : V × V => decide (t.1 = t.2)))

private def matching (inpt : V × (V × (V × Bool))) : List (V × Bool) :=
  bif decide (inpt.1 = inpt.2.1) then [inpt.2.2] else []

include eqCost in
private theorem poly_matching : Poly (matching (V:=V)) := by
  unfold matching
  have eqc : Poly (fun x : V × V × V × Bool => decide (x.1 = x.2.1)) :=
    (show Poly (fun x : V × V × V × Bool => (x.1,x.2.1)) by fun_prop).compose eqCost
  apply Poly.choose eqc _ (IntegerMultiplication.Code.Poly.const [])
  exact (Poly.pair (X := V×V×V×Bool) (by fun_prop) (IntegerMultiplication.Code.Poly.const [])).compose Poly.cons

omit [Codec V] in
private theorem matching_head (v : V) (t : Labels V) :
    ((polyPush matching (v,t)).flatten ++ [(v,false)]).headD (v₀,false) = label t v := by
  induction t with
  | nil => rfl
  | cons row t ih =>
    rcases row with ⟨a,b⟩
    by_cases h : v = a
    · subst v; simp [polyPush,matching,label]
    · have hb : (v == a) = false := by simpa using h
      simpa only [label,List.lookup_cons,polyPush,List.map_cons,List.flatten_cons,
        matching,decide_eq_false h,Bool.cond_false,List.nil_append,hb] using ih

include eqCost v₀ in
theorem label_poly : Poly (fun t : V × Labels V => label t.2 t.1) := by
  let rows : V × Labels V → List (V × Bool) := fun t => (polyPush matching t).flatten
  have hr : Poly rows := (Poly.push v₀ (v₀,(v₀,false)) (poly_matching eqCost)).compose Easy.flatten.poly
  have hd : Poly (fun t : V × Labels V => [(t.1,false)]) :=
    (Poly.pair (show Poly (fun t : V × Labels V => (t.1,false)) by fun_prop)
      (IntegerMultiplication.Code.Poly.const ([] : List (V × Bool)))).compose Poly.cons
  have H := (hr.app hd).compose (Iter.leader (v₀,false)).poly
  simpa only [rows, matching_head v₀] using H

abbrev Triple (V : Type*) := V × V × Bool

private def rewriteRow (D : ((V × Bool) × (V × Bool) × Bool) × Triple V) : Triple V :=
  let row := D.2
  let x := D.1.1
  let y := D.1.2.1
  let p := D.1.2.2
  (row.1,bif decide (row.2.1 = y.1) then (x.1,row.2.2 ^^ (x.2 ^^ y.2 ^^ p)) else row.2)

include eqCost in
private theorem rewrite_poly : Poly (rewriteRow (V:=V)) := by
  let X := ((V × Bool) × (V × Bool) × Bool) × Triple V
  have b : Poly (fun x : Bool × Bool => x.1 ^^ x.2) := (Easy.finite _).poly
  have test : Poly (fun x : X => decide (x.2.2.1 = x.1.2.1.1)) :=
    (show Poly (fun x : X => (x.2.2.1, x.1.2.1.1)) by fun_prop).compose eqCost
  have bits : Poly (fun x : X => ((x.1.1.2,x.1.2.1.2))) := by fun_prop
  have t₂ := ((bits.compose b).pair (show Poly (fun x : X => x.1.2.2) by fun_prop)).compose b
  have t₃ := ((show Poly (fun x : X => x.2.2.2) by fun_prop).pair t₂).compose b
  exact Poly.pair (by fun_prop) (Poly.choose test (Poly.pair (by fun_prop) t₃) (by fun_prop))

def asEq (x : Triple V) : Equation V := ⟨x.1,x.2.1,x.2.2⟩

include eqCost v₀ in
theorem joinLabels_poly : Poly (fun t : Labels V × Triple V => joinLabels (asEq t.2) t.1) := by
  let X := Labels V × Triple V
  have leftCost : Poly (fun t : X => label t.1 t.2.1) :=
    (show Poly (fun t : X => (t.2.1,t.1)) by fun_prop).compose (label_poly v₀ eqCost)
  have rightCost : Poly (fun t : X => label t.1 t.2.2.1) :=
    (show Poly (fun t : X => (t.2.2.1,t.1)) by fun_prop).compose (label_poly v₀ eqCost)
  have parameters := leftCost.pair (rightCost.pair (show Poly (fun t : X => t.2.2.2) by fun_prop))
  have h := (parameters.pair (show Poly (fun t : Labels V × Triple V => t.1) from Easy.fst.poly)).compose
    (Poly.push ((v₀,false),(v₀,false),false) (v₀,v₀,false) (rewrite_poly eqCost))
  convert h using 1
  funext t
  unfold joinLabels polyPush
  apply List.map_congr_left
  intro row _
  by_cases h : row.2.1 = (label t.1 t.2.2.1).1 <;> simp [asEq,rewriteRow,amend,h]
private def Small (B : ℕ) (t : Labels V) :=
  ∀ row ∈ t, size row.1 ≤ B ∧ size row.2.1 ≤ B

private theorem label_small {B : ℕ} {t : Labels V} (ht : Small B t) {v : V} (hv : size v ≤ B) :
    size (label t v).1 ≤ B := by
  unfold label
  cases h : t.lookup v with
  | none => exact hv
  | some q =>
    obtain ⟨s,u,hh,_⟩ := List.lookup_eq_some_iff.mp h
    have hm : (v,q) ∈ t := by simp [hh]
    exact (ht _ hm).2

private theorem small_join {B : ℕ} {t : Labels V} (ht : Small B t) (e : Triple V)
    (he : size e.1 ≤ B) : Small B (joinLabels (asEq e) t) := by
  intro _ hm
  obtain ⟨row,hrow,rfl⟩ := List.mem_map.mp hm
  refine ⟨(ht _ hrow).1,?_⟩
  simp only [amend]
  split
  · exact label_small ht he
  · exact (ht _ hrow).2

private theorem small_run {B : ℕ} (es : List (Triple V)) (hes : ∀ e ∈ es, size e.1 ≤ B)
    (t : Labels V) (ht : Small B t) : Small B (compileEquations (es.map asEq) t) := by
  induction es generalizing t with
  | nil => exact ht
  | cons e es ih =>
    exact ih (fun e he => hes e (by simp [he])) _ (small_join ht e (hes e (by simp)))

omit [DecidableEq V] in
private theorem small_bound {B : ℕ} (t : Labels V) (ht : Small B t) :
    size t ≤ t.length * (2*B+4) + 1 := by
  induction t with
  | nil => simp
  | cons row tl ih =>
    have a := ht row (by simp)
    have b := ih (fun v hv => ht v (by simp [hv]))
    rcases a with ⟨ha,hb⟩
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul, size_cons, size_prod, size_bit]
    omega

include eqCost v₀ in
theorem compileEquations_poly :
    Poly (fun t : List (Triple V) × Labels V => compileEquations (t.1.map asEq) t.2) := by
  have fold (es : List (Triple V)) (t : Labels V) : compileEquations (es.map asEq) t =
      es.foldl (fun T e => joinLabels (asEq e) T) t := by simp [compileEquations,List.foldl_map]
  simp_rw [fold]
  apply Poly.fold_left (joinLabels_poly v₀ eqCost) 6 2
  intro t l hl
  rw [← fold]
  let B := size t
  have hr : ∀ u ∈ t.2, size u.1 ≤ B ∧ size u.2.1 ≤ B := by
    intro u hu
    have h := size_bel hu
    dsimp [B]
    simp only [size_prod] at h ⊢
    omega
  have he : ∀ e ∈ l, size e.1 ≤ B := by
    intro e h
    have hd := size_bel (hl.subset h)
    dsimp [B]
    simp only [size_prod] at hd ⊢
    omega
  have hb := small_bound _ (small_run l he t.2 hr)
  rw [compile_length] at hb
  have hd := duration t.2
  have ht : t.2.length ≤ B := by change t.2.length ≤ size t.1 + size t.2 + 1; omega
  apply hb.trans
  change _ ≤ 6*(B+1)^2
  exact (Nat.add_le_add_right (Nat.mul_le_mul_right (2*B+4) ht) 1).trans (by nlinarith)

/-- Input and output table rows, with the pin's low bit stored separately. -/
abbrev Entry (A : Type) := (Bool × A) × (Bool × A)

def equationRow (row : Entry V) : Triple (Bool × V) :=
  ((false,row.1.2), (true,row.2.2), row.1.1 ^^ row.2.1)

/-- Polynomial-time tape program for preparing switch colors from a list of forward table
entries. The labels consist of one Boolean lane number and one encoded port index. -/
def prepareControls (x : List (Entry V)) : Labels (Bool × V) :=
  compileEquations ((x.map equationRow).map asEq) (initialLabels (x.map Prod.fst))

omit [Codec V] in
theorem prepareControls_spec (p : Equiv.Perm (Bool × V)) (ports : List (Bool × V)) :
    prepareControls (ports.map fun x => (x,p x)) = portTable p ports := by
  simp only [prepareControls, portTable, List.map_map]
  change compileEquations _ (initialLabels (ports.map id)) = _
  rw [List.map_id]
  rfl

include eqCost v₀ in
theorem prepareControls_poly : Poly (prepareControls (V := V)) := by

  have band : Poly (fun x : Bool × Bool => x.1 && x.2) := (Easy.finite _).poly
  have beq : Poly (fun x : Bool × Bool => decide (x.1 = x.2)) := (Easy.finite _).poly
  have bXor : Poly (fun x : Bool × Bool => x.1 ^^ x.2) := (Easy.finite _).poly
  have eq₁ := (show Poly (fun x : (Bool × V) × (Bool × V) => (x.1.1,x.2.1)) by fun_prop).compose beq
  have eq₂ := (show Poly (fun x : (Bool × V) × (Bool × V) => (x.1.2,x.2.2)) by fun_prop).compose eqCost
  have heq : Poly (fun x : (Bool × V) × (Bool × V) => decide (x.1 = x.2)) := by
    convert (eq₁.pair eq₂).compose band using 1
    funext x
    by_cases hf : x.1.1 = x.2.1 <;> by_cases hs : x.1.2 = x.2.2 <;> simp [Prod.ext_iff,hf,hs]
  have bits := (show Poly (fun x : Entry V => (x.1.1,x.2.1)) by fun_prop).compose bXor
  have E : Poly (equationRow (V:=V)) := Poly.pair (by fun_prop) (Poly.pair (by fun_prop) bits)
  have T : Poly (fun x : Entry V => (x.1,x.1,false)) := by fun_prop
  have setup := (Poly.maps _ E).pair (Poly.maps _ T)
  unfold prepareControls initialLabels
  simpa only [List.map_map, Function.comp_def] using
    setup.compose (compileEquations_poly (false,v₀) heq)

/-- Unary port numbers give a single physical polynomial-time program over growing
port sets. Every index for a block of width `d` has unary length at most `2^d`. -/
theorem prepareControls_tally : Poly (prepareControls (V:=Tally)) := by
  apply prepareControls_poly []
  have h := (Iter.linked (X:=Unit) (Y:=Unit)).poly
  convert h using 1
  funext t
  congr 1
  apply propext
  exact ⟨congrArg List.length, fun e => (recover_tally _).symm.trans ((congrArg tally e).trans (recover_tally _))⟩

section Rename
variable {A D : Type} [DecidableEq A] [DecidableEq D] (f : A → D) (hf : Function.Injective f)

def renameLabels (t : Labels A) : Labels D :=
  t.map fun row => (f row.1,f row.2.1,row.2.2)

def renameEq (e : Equation A) : Equation D := ⟨f e.left,f e.right,e.parity⟩

include hf in
private theorem label_rename (t : Labels A) (v : A) :
    label (renameLabels f t) (f v) = (f (label t v).1,(label t v).2) := by
  induction t with
  | nil => rfl
  | cons row t ih =>
    rcases row with ⟨u,c,b⟩
    by_cases h : v = u
    · subst v; simp [renameLabels,label]
    · have hb : (v == u) = false := by simpa using h
      have hf' : (f v == f u) = false := by simpa [hf.eq_iff] using h
      simpa only [renameLabels, List.map_cons, label, List.lookup_cons, hb, hf'] using ih

include hf in
private theorem join_rename (t : Labels A) (e : Equation A) :
    joinLabels (renameEq f e) (renameLabels f t) = renameLabels f (joinLabels e t) := by
  simp only [joinLabels, renameEq, label_rename f hf]
  simp only [renameLabels,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro row _
  by_cases he : row.2.1 = (label t e.right).1 <;> simp [amend, he, hf.eq_iff]

include hf in
private theorem compile_rename (es : List (Equation A)) (t : Labels A) :
    compileEquations (es.map (renameEq f)) (renameLabels f t) =
      renameLabels f (compileEquations es t) := by
  induction es generalizing t with
  | nil => rfl
  | cons e l ih =>
    change compileEquations _ (joinLabels (renameEq f e) (renameLabels f t)) = _
    rw [join_rename f hf, ih]
    rfl

end Rename

def indexedPort {A D : Type} (num : A → D) (v : Bool × A) : Bool × D := (v.1,num v.2)

/-- The polynomial-time coloring on unary-coded ports supplies exactly the lane
equations needed by the Beneš recursion on the finite logical address type. -/
theorem tapeColors_correct {A D : Type} [Fintype A] [DecidableEq A] [DecidableEq D] (num : A → D)
    (hn : Function.Injective num) (p : Equiv.Perm (Bool × A)) (ports : List (Bool × A))
    (hports : ∀ x, x ∈ ports) (x : Bool × A) :
    let entries := ports.map fun z => (indexedPort num z,indexedPort num (p z))
    let table := prepareControls entries
    (x.1 ^^ (label table (false,num x.2)).2) =
      ((p x).1 ^^ (label table (true,num (p x).2)).2) := by
  let f := indexedPort num
  have hf : Function.Injective f := by
    intro x y h
    have h₁ := congrArg (Prod.fst : Bool × D → Bool) h
    have h₂ := congrArg (Prod.snd : Bool × D → D) h
    exact Prod.ext h₁ (hn h₂)
  have H : prepareControls (ports.map (fun z => (f z,f (p z)))) =
      renameLabels f (portTable p ports) := by
    unfold prepareControls portTable
    rw [← compile_rename f hf]
    simp only [initialLabels, renameLabels, List.map_map, Function.comp_def]
    rfl
  change (x.1 ^^ (label (prepareControls _) (f (false,x.2))).2) =
    ((p x).1 ^^ (label (prepareControls _) (f (true,(p x).2))).2)
  rw [H,label_rename f hf,label_rename f hf]
  exact portTable_correct p ports hports x

/-- Unary addressing keeps a table of `M` rows polynomial in `M`. -/
theorem tapeTable_size {A : Type} (num : A → Tally) (p : Equiv.Perm (Bool × A))
    (ports : List (Bool × A)) (B : ℕ) (hn : ∀ a, (num a).length ≤ B) :
    size (ports.map fun z => (indexedPort num z,indexedPort num (p z))) ≤
      ports.length * (4*B+8) + 1 := by
  induction ports with
  | nil => simp
  | cons z zs ih =>
    simp only [List.map_cons,size_cons,size_prod,indexedPort, size_bit,size_tally,List.length_cons,Nat.add_mul,Nat.one_mul]
    simp only [indexedPort] at ih
    have h₁ := hn z.2
    have h₂ := hn (p z).2
    omega

/-- Actual P192 stack-machine task, with its charged polynomial bound in the number
of ports, for table generation. Arbitrary parked caller frames are preserved by `Task`. -/
theorem tapeTable_task {I : Type} {A : I → Type} (num : ∀ i, A i → Tally)
    (p : ∀ i, Equiv.Perm (Bool × A i)) (ports : ∀ i, List (Bool × A i))
    (hn : ∀ i a, (num i a).length ≤ (ports i).length) :
    let data (i : I) := (ports i).map fun z => (indexedPort (num i) z,indexedPort (num i) (p i z))
    Task.BT (fun i => (ports i).length) (fun i => send (data i)) (fun i => send (prepareControls (data i))) := by
  dsimp only
  apply prepareControls_tally.on
  refine ⟨2,12,fun i => (tapeTable_size _ _ _ _ (hn i)).trans ?_⟩
  nlinarith

end Tape
end Benes

end NearSquareRoot
end Computability
end OAI
