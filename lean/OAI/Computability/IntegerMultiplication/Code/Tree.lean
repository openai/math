import OAI.Computability.IntegerMultiplication.TMProgram
import Mathlib.Data.Fintype.EquivFin

/-!
Our tape programming API will use stacks of trees. Root first encoding means we may use
head inspection/construction in O(1) even if there is a long uncharged suffix.
-/

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code

inductive Tree
  | atom (b : Bool)
  | fork (x y : Tree)
deriving DecidableEq

inductive Ltr
  | bit (b : Bool)
  | node
  | sep
deriving DecidableEq

abbrev Cmd := Prog Ltr
abbrev Env := Scope Ltr
abbrev Deck := Reg Tree

namespace Tree

def count : Tree → ℕ
  | atom _ => 1
  | fork x y => count x + count y + 1

theorem count_pos (x : Tree) : 0 < count x := by cases x <;> simp [count]

def spell : Tree → List Ltr
  | atom b => [.bit b]
  | fork x y => .node :: spell x ++ spell y

@[simp]
theorem spell_length (x : Tree) : (spell x).length = x.count := by
  induction x <;> simp_all [spell,count]

/-- Consume by reversing the construction, so moved records arrive mirrored. -/
def flip : Tree → Tree
  | atom b => atom b
  | fork x y => fork y.flip x.flip

@[simp]
theorem flip_flip (x : Tree) : x.flip.flip = x := by induction x <;> simp_all [flip]

@[simp]
theorem count_flip (x : Tree) : x.flip.count = x.count := by
  induction x <;> simp_all [flip,count,add_comm]

end Tree

def letters (r : Deck) : Reg Ltr := fun i => (r i).flatMap Tree.spell

def pile (i : ℕ) (z : Tree) (r : Deck) : Deck := Function.update r i (z::r i)

@[simp]
theorem pile_self (i z r) : pile i z r i = z::r i := Function.update_self _ _ _

@[simp]
theorem pile_else (i z r j) (h : j ≠ i) : pile i z r j = r j := Function.update_of_ne h _ _

theorem letters_pile (i z r) :
    letters (pile i z r) = Function.update (letters r) i (Tree.spell z ++ letters r i) := by
  funext j
  by_cases h : j=i
  · subst j; simp [letters]
  · simp [letters,pile_else _ _ _ _ h,Function.update_of_ne h]

theorem pile_comm (i z r j w) (h : i≠j) :
    pile i z (pile j w r) = pile j w (pile i z r) := by
  funext a; by_cases ha : a=i <;> by_cases hb : a=j <;> subst_vars <;> simp_all [ne_eq]

/-- Can use conditional simplification (or explicitly rewrite with just pile_comm) -/
theorem pile_comm_lt (i z r j w) (h : i<j) :
    pile i z (pile j w r) = pile j w (pile i z r) := pile_comm _ _ _ _ _ (by omega)

theorem pile_far (i j : ℕ) (h : i ≠ j) (z : Tree) (r : Deck) :
    letters (pile i z r) j = letters r j := by rw [letters_pile, Function.update_of_ne (Ne.symm h)]

@[simp]
theorem letters_here (i z r) : letters (pile i z r) i = Tree.spell z ++ letters r i := by
  rw [letters_pile, Function.update_self]

/-- Budget relation on tree states. n is an upper bound on the successful run cost;
`env` is a static control scope from the low-level language. -/
def Fits (env : Env) (c : Cmd) (r s : Deck) (n : ℕ) : Prop :=
  ∃ t ≤ n, Prog.Run env c (letters r) t (letters s)

namespace Fits

theorem mono {env c r s n} {m : ℕ} (h : Fits env c r s n) (e : n ≤ m) : Fits env c r s m := by
  obtain ⟨t,h,h'⟩ := h
  exact ⟨t,h.trans e,h'⟩

theorem pass {env} (r : Deck) : Fits env .pass r r 1 := ⟨1,le_rfl,.pass⟩

theorem join {env c r s n d u t} (h : Fits env c r s n) (g : Fits env d s u t) :
    Fits env (.join c d) r u (n+t+2) := by
  obtain ⟨w,hw,h'⟩ := h
  obtain ⟨v,hv,g'⟩ := g
  exact ⟨1+w+1+v, by omega, h'.join g'⟩

theorem tie {env c r s n} (h : Fits (c::env) c r s n) :
    Fits env (.tie c) r s (n+1) := by
  obtain ⟨w,hw,h'⟩ := h
  exact ⟨1+w, by omega, h'.tie⟩

theorem again {env i b c r s n} (e : env[i]? = some b) (d : c=Prog.again i)
    (h : Fits (List.drop i env) b r s n) : Fits env c r s (n+1) := by
  obtain ⟨w,hw,h'⟩ := h
  exact ⟨1+w, by omega, d ▸ (.again e h')⟩

theorem again0 {env b r s n} (h : Fits (b::env) b r s n) :
    Fits (b::env) (.again 0) r s (n+1) :=
  again (i := 0) (by simp) rfl h

/-- If the relation is parametric in r, this shares arbitrary parked data without a visit. -/
def value (env : Env) (c : Cmd) (i : ℕ) (z w : Tree) (n : ℕ) :=
  ∀ r, Fits env c (pile i z r) (pile i w r) n

end Fits

/-- Root-level instructions. -/
def give (i : ℕ) (b : Bool) : Cmd := .push i (.bit b)

def pack (i : ℕ) : Cmd := .push i .node

/-- Inspect and remove one constructor from a nonempty stack. The two arms handle
atoms by value, or pairs exposing both subtrees in order. A production of .pass in
the default arm is arbitrary. -/
def splitRoot (i : ℕ) (leaf : Bool → Cmd) (pair : Cmd) : Cmd :=
  .look i (fun top => .join (.pop i) (match top with
    | some (.bit x) => leaf x
    | some .node => pair
    | _ => .pass))

theorem fits_give (b : Bool) (r : Deck) (i : ℕ) (env : Env) :
    Fits env (give i b) r (pile i (.atom b) r) 1 := by
  refine ⟨1,le_rfl,?_⟩
  rw [letters_pile]
  exact .push

theorem fits_pack (x y : Tree) (r : Deck) (i) (env : Env) :
    Fits env (pack i) (pile i x (pile i y r)) (pile i (.fork x y) r) 1 := by
  refine ⟨1,le_rfl,?_⟩
  have h : Function.update (letters (pile i x (pile i y r))) i
      (.node :: (letters (pile i x (pile i y r))) i) = letters (pile i (.fork x y) r) := by
    funext j
    by_cases hj : j=i
    · subst j; simp [Tree.spell, List.append_assoc]
    · simp [pile_far _ _ (Ne.symm hj), Function.update_of_ne hj]
  rw [← h]
  exact .push

private theorem lowSplit {r s t : Reg Ltr} {e : Ltr} {i} {l : List Ltr}
    {env : Env} {f : Option Ltr → Cmd} {n}
    (he : r i=e::l)
    (hr : Function.update r i l = s)
    (h : Prog.Run env (f (some e)) s n t) :
    Prog.Run env (.look i fun o => .join (.pop i) (f o)) r (1+(1+1+1+n)) t := by
  rw [← hr] at h
  apply Prog.Run.look
  rw [he, List.head?_cons]
  have hpop : Prog.Run env (Prog.pop i) r 1 (Function.update r i l) := by
    convert Prog.Run.pop (Γ := env) (r := r) (i := i) using 1
    simp [he]
  exact hpop.join h

theorem fits_bit {b : Bool} {r s : Deck} {i : ℕ} {c : Bool → Cmd} {d : Cmd} {n env}
    (h : Fits env (c b) r s n) :
    Fits env (splitRoot i c d) (pile i (.atom b) r) s (n+4) := by
  obtain ⟨t,e,g⟩ := h
  unfold Fits splitRoot
  refine ⟨1+(1+1+1+t), by omega, lowSplit (e := .bit b) (l := letters r i) ?_ ?_ g⟩
  · rw [letters_here]; rfl
  · funext j
    by_cases hj : j=i
    · subst j; simp
    · simp [Function.update_of_ne hj, pile_far _ _ (Ne.symm hj)]

theorem fits_pair {x y : Tree} {r s : Deck} {i : ℕ} {c : Bool → Cmd} {d : Cmd} {n env}
    (h : Fits env d (pile i x (pile i y r)) s n) :
    Fits env (splitRoot i c d) (pile i (.fork x y) r) s (n+4) := by
  obtain ⟨t,e,g⟩ := h
  unfold Fits splitRoot
  refine ⟨1+(1+1+1+t), by omega,
    lowSplit (e := .node) (l := letters (pile i x (pile i y r)) i) ?_ ?_ g⟩
  · simp [Tree.spell, List.append_assoc]
  · funext j
    by_cases hj : j=i
    · subst j; simp
    · simp [Function.update_of_ne hj, pile_far _ _ (Ne.symm hj)]

end Code

end IntegerMultiplication
end Computability
end OAI
