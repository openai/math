import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

namespace OAI
/-! # The rooted complete binary tree of a prescribed height -/

namespace Hierarchy.BinaryTree

/-- A nonroot vertex records its side and its position in that subtree. -/
def V : ℕ → Type
  | 0 => Unit
  | h+1 => Option (Bool × V h)

/-- An edge either leaves the root or belongs to one of the two child trees. -/
def E : ℕ → Type
  | 0 => Empty
  | h+1 => Bool ⊕ (Bool × E h)

instance vertexFintype : (h : ℕ) → Fintype (V h)
  | 0 => inferInstanceAs (Fintype Unit)
  | h+1 => by
    letI := vertexFintype h
    exact inferInstanceAs (Fintype (Option (Bool × V h)))

instance edgeFintype : (h : ℕ) → Fintype (E h)
  | 0 => inferInstanceAs (Fintype Empty)
  | h+1 => by
    letI := edgeFintype h
    exact inferInstanceAs (Fintype (Bool ⊕ (Bool × E h)))

def root : (h : ℕ) → V h
  | 0 => ()
  | _+1 => none

def child {h : ℕ} (c : Bool) (v : V h) : V (h+1) := some (c,v)

def rootEdge {h : ℕ} (c : Bool) : E (h+1) := Sum.inl c

def childEdge {h : ℕ} (c : Bool) (e : E h) : E (h+1) := Sum.inr (c,e)

def left : (h : ℕ) → E h → V h
  | 0, e => nomatch e
  | _+1, .inl _ => none
  | h+1, .inr (c,e) => child c (left h e)

def right : (h : ℕ) → E h → V h
  | 0, e => nomatch e
  | h+1, .inl c => child c (root h)
  | h+1, .inr (c,e) => child c (right h e)

def side : (h : ℕ) → E h → Bool
  | 0, e => nomatch e
  | _+1, .inl c => c
  | h+1, .inr (_,e) => side h e

def level : (h : ℕ) → V h → ℕ
  | 0, _ => 0
  | _+1, none => 0
  | h+1, some (_,v) => level h v+1

noncomputable def parent : (h : ℕ) → V h → V h
  | 0, v => v
  | _+1, none => none
  | h+1, some (c,v) => by
    classical
    exact if v=root h then none else child c (parent h v)

@[simp] theorem parent_root (h : ℕ) : parent h (root h)=root h := by cases h <;> rfl

@[simp] theorem level_root (h : ℕ) : level h (root h)=0 := by cases h <;> rfl

theorem parent_lt : ∀ h (v : V h), v≠root h → level h (parent h v)<level h v := by
  intro h
  induction h with
  | zero => intro v ne; cases v; exact (ne rfl).elim
  | succ h ih =>
    intro v ne
    rcases v with _|⟨c,v⟩
    · exact (ne rfl).elim
    · by_cases hv : v=root h
      · simp [parent,hv,level]
      · simpa [parent,hv,level,child] using ih v hv

@[simp] theorem right_ne_root : ∀ h (e : E h), right h e≠root h
  | 0,e => nomatch e
  | _+1,.inl _ => by intro eqn; cases eqn
  | _+1,.inr (_,_) => by intro eqn; cases eqn

@[simp] theorem parent_right : ∀ h (e : E h), parent h (right h e)=left h e
  | 0,e => nomatch e
  | h+1,.inl c => by simp [right,left,child,parent]; rfl
  | h+1,.inr (c,e) => by simp [right,left,child,parent,parent_right h e]; rfl

theorem left_ne_right (h : ℕ) (e : E h) : left h e≠right h e := by
  have lt := parent_lt h (right h e) (right_ne_root h e)
  rw [parent_right] at lt
  exact fun eqn => (Nat.ne_of_lt lt) (congrArg (level h) eqn)

theorem child_inj {h : ℕ} {a b : Bool} {v w : V h} (eqn : child a v=child b w) : a=b ∧ v=w := by
  have ep : (a,v)=(b,w) := Option.some.inj eqn
  exact ⟨congrArg Prod.fst ep,congrArg Prod.snd ep⟩

theorem right_injective : ∀ h, Function.Injective (right h) := by
  intro h
  induction h with
  | zero => intro e; exact nomatch e
  | succ h ih =>
    rintro (a|⟨a,e⟩) (b|⟨b,f⟩) eqn
    · exact congrArg Sum.inl (child_inj (h:=h) eqn).1
    · exact ((right_ne_root h f) (child_inj (h:=h) eqn).2.symm).elim
    · exact ((right_ne_root h e) (child_inj (h:=h) eqn).2).elim
    · obtain ⟨rfl,he⟩ := child_inj (h:=h) eqn
      cases ih he
      rfl

theorem left_side_injective : ∀ h (e f : E h),
    left h e=left h f → side h e=side h f → e=f := by
  intro h
  induction h with
  | zero => intro e; exact nomatch e
  | succ h ih =>
    rintro (a|⟨a,e⟩) (b|⟨b,f⟩) eqn hs
    · exact congrArg Sum.inl hs
    · cases eqn
    · cases eqn
    · have both : a=b ∧ left h e=left h f := child_inj eqn
      obtain ⟨rfl,he⟩ := both
      cases ih e f he hs
      rfl

theorem card_succ (h : ℕ) : Fintype.card (V (h+1)) = 2*Fintype.card (V h)+1 := by
  change Fintype.card (Option (Bool × V h))=_
  simp

theorem card_vertices (h : ℕ) : Fintype.card (V h)+1 = 2^(h+1) := by
  induction h with
  | zero => decide
  | succ h ih =>
    rw [card_succ,pow_succ,←ih]
    omega

theorem card_edges_add_one : ∀ h, Fintype.card (E h)+1=Fintype.card (V h) := by
  intro h
  induction h with
  | zero => decide
  | succ h ih =>
    rw [card_succ]
    change Fintype.card (Bool ⊕ (Bool × E h))+1=_
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool]
    omega

end Hierarchy.BinaryTree

end OAI
