import OAI.Computability.VPVNP.ParseHistogram
import Mathlib.Data.List.Nodup

/-!
# Preorder choices for the coefficient counter

A terminal choice names its input position. The terminal bit comes from that
position in the assembled word. A binary choice gives the ordered child states
and their split. Its legal range depends on the pending subtree's degree.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter

open ParseGrammar

variable {n m : ℕ} {H : Type*}

/-- Branch data at one pending node. The stack determines the required constructor. -/
inductive Token (m : ℕ) (H : Type*) where
  | terminal (position : Fin m)
  | binary (split : ℕ) (leftState rightState : H)
  deriving DecidableEq

/-- Serialize an ordered parse by visiting the parent before either child. -/
def preorder {d : ℕ} : OrderedParse (Fin m × Bool) H d → List (Token m H)
  | .leaf v => [.terminal v.1]
  | .node b i j left right => .binary b.val i j :: (preorder left ++ preorder right)

@[simp] theorem length_preorder {d : ℕ} (p : OrderedParse (Fin m × Bool) H d) :
    (preorder p).length = 2 * d + 1 := by
  induction p with
  | leaf => rfl
  | node b _ _ _ _ hl hr =>
    simp [preorder, hl, hr]
    have := b.isLt
    omega

/-- Every terminal of the parse reads the bit in its specified position. -/
def Agrees (x : Fin m → Bool) {d : ℕ} (p : OrderedParse (Fin m × Bool) H d) : Prop :=
  ∀ v ∈ p.leaves, v.2 = x v.1

@[simp] theorem agrees_leaf (x : Fin m → Bool) (v : Fin m × Bool) :
    Agrees x (OrderedParse.leaf (H := H) v) ↔ v.2 = x v.1 := by
  simp [Agrees, OrderedParse.leaves]

@[simp] theorem agrees_node (x : Fin m → Bool) {d : ℕ} (b : Fin (d + 1)) (i j : H)
    (left : OrderedParse (Fin m × Bool) H b.val) (right : OrderedParse (Fin m × Bool) H (d - b.val)) :
    Agrees x (.node b i j left right) ↔ Agrees x left ∧ Agrees x right := by
  simp [Agrees, OrderedParse.leaves, or_imp, forall_and]

/-- Decode one tree and return the unconsumed choices. -/
def readTree (x : Fin m → Bool) : (d : ℕ) → List (Token m H) →
    Option (OrderedParse (Fin m × Bool) H d × List (Token m H))
  | 0, .terminal j :: more => some (.leaf (j, x j), more)
  | k + 1, .binary b i j :: more => do
    if hb : b < k + 1 then
      let (left, rest) ← readTree x b more
      let (right, tail) ← readTree x (k - b) rest
      return (.node ⟨b, hb⟩ i j left right, tail)
    else none
  | _, _ => none
termination_by d _ => d
decreasing_by all_goals omega

theorem readTree_preorder (x : Fin m → Bool) {d : ℕ} (p : OrderedParse (Fin m × Bool) H d)
    (hp : Agrees x p) (tail : List (Token m H)) :
    readTree x d (preorder p ++ tail) = some (p, tail) := by
  induction p generalizing tail with
  | leaf v =>
    rw [agrees_leaf] at hp
    obtain ⟨j, v⟩ := v
    change v = x j at hp
    subst v
    simp [preorder, readTree]
  | node b i j left right hl hr =>
    obtain ⟨hl', hr'⟩ := (agrees_node ..).mp hp
    simp [preorder, List.append_assoc, readTree, b.isLt, hl hl', hr hr']

theorem readTree_sound (x : Fin m → Bool) (d : ℕ) (ts : List (Token m H))
    (p : OrderedParse (Fin m × Bool) H d) (tail : List (Token m H))
    (hr : readTree x d ts = some (p, tail)) :
    Agrees x p ∧ ts = preorder p ++ tail := by
  induction d using Nat.strong_induction_on generalizing ts tail with
  | h d ih =>
    cases d with
    | zero =>
      cases ts with
      | nil => simp [readTree] at hr
      | cons t more =>
        cases t with
        | binary => simp [readTree] at hr
        | terminal j =>
          simp [readTree] at hr
          obtain ⟨rfl, rfl⟩ := hr
          simp [preorder]
    | succ k =>
      cases ts with
      | nil => simp [readTree] at hr
      | cons t more =>
        cases t with
        | terminal => simp [readTree] at hr
        | binary b i j =>
          by_cases hb : b < k + 1
          · cases hl : readTree x b more with
            | none => simp [readTree, hb, hl] at hr
            | some l =>
              obtain ⟨left, rest⟩ := l
              cases hright : readTree x (k - b) rest with
              | none => simp [readTree, hb, hl, hright] at hr
              | some r =>
                obtain ⟨right, endBits⟩ := r
                simp [readTree, hb, hl, hright] at hr
                obtain ⟨rfl, rfl⟩ := hr
                obtain ⟨h₁, e₁⟩ := ih b hb more left rest hl
                obtain ⟨h₂, e₂⟩ := ih (k - b) (by omega) rest right endBits hright
                simp [h₁, h₂, preorder, e₁, e₂, List.append_assoc]
          · simp [readTree, hb] at hr

/-- Leaf locations encountered by the mark array, in visitation order. -/
def positions (ts : List (Token m H)) : List (Fin m) :=
  ts.filterMap fun
    | .terminal j => some j
    | .binary .. => none

@[simp] theorem positions_preorder {d : ℕ} (p : OrderedParse (Fin m × Bool) H d) :
    positions (preorder p) = p.leaves.map Prod.fst := by
  induction p with
  | leaf => rfl
  | node b i j l r hl hr =>
    simpa [positions, preorder, OrderedParse.leaves, List.filterMap_append] using
      congrArg₂ List.append hl hr

private theorem agrees_of_bijection (x : Fin m → Bool) {d : ℕ} (p : OrderedParse (Fin m × Bool) H d)
    (e : LeafBijection p.leaves (fun j => (j, x j))) : Agrees x p := by
  intro v hv
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hv
  rw [e.property i]

private theorem marks_of_bijection {d : ℕ} (p : OrderedParse (Fin m × Bool) H d)
    (x : Fin m → Bool) (e : LeafBijection p.leaves (fun j => (j, x j))) :
    (positions (preorder p)).Nodup := by
  rw [positions_preorder, List.nodup_iff_injective_getElem]
  intro i j he
  let i' : Fin p.leaves.length := ⟨i.val, by simpa using i.isLt⟩
  let j' : Fin p.leaves.length := ⟨j.val, by simpa using j.isLt⟩
  have he' : e.val i' = e.val j' := by
    have hx := congrArg Prod.fst (e.property i')
    have hy := congrArg Prod.fst (e.property j')
    refine hx.symm.trans ((Eq.trans ?_ hy))
    simpa [i', j', List.get_eq_getElem] using he
  exact Fin.ext (congrArg (fun a : Fin p.leaves.length => a.val) (e.val.injective he'))

private noncomputable def bijectionOfMarks {d : ℕ} (hsize : d + 1 = m)
    (p : OrderedParse (Fin m × Bool) H d) (x : Fin m → Bool) (ha : Agrees x p)
    (hn : (positions (preorder p)).Nodup) : LeafBijection p.leaves (fun j => (j, x j)) := by
  let loc (i : Fin p.leaves.length) := (p.leaves.get i).1
  have hb : Function.Bijective loc := by
    apply (Fintype.bijective_iff_injective_and_card loc).2
    refine ⟨?_, by simp [hsize]⟩
    rw [positions_preorder, List.nodup_iff_injective_getElem] at hn
    intro i j hij
    apply Fin.ext
    let i' : Fin (p.leaves.map Prod.fst).length := ⟨i.val, by simpa using i.isLt⟩
    let j' : Fin (p.leaves.map Prod.fst).length := ⟨j.val, by simpa using j.isLt⟩
    exact congrArg (fun a : Fin (p.leaves.map Prod.fst).length => a.val) (@hn i' j' (by simpa [loc, i', j', List.get_eq_getElem] using hij))
  refine ⟨Equiv.ofBijective loc hb, fun i => Prod.ext rfl ?_⟩
  exact ha _ (List.get_mem ..)

/-- Complete decoder with the distinct-position check used by the counter.
The computation returns the unique decoded parse and rejects trailing tokens. -/
def checkedTree (x : Fin m → Bool) (d : ℕ) (ts : List (Token m H)) :
    Option (OrderedParse (Fin m × Bool) H d) := do
  let (p, tail) ← readTree x d ts
  if tail.isEmpty && decide (positions ts).Nodup then return p else none

theorem checkedTree_eq_some_iff (x : Fin m → Bool) {d : ℕ} (ts : List (Token m H))
    (p : OrderedParse (Fin m × Bool) H d) :
    checkedTree x d ts = some p ↔
      Agrees x p ∧ ts = preorder p ∧ (positions ts).Nodup := by
  constructor
  · intro h
    cases hr : readTree x d ts with
    | none => simp [checkedTree, hr] at h
    | some v =>
      obtain ⟨q, tail⟩ := v
      simp [checkedTree, hr] at h
      obtain ⟨⟨rfl, hn⟩, rfl⟩ := h
      obtain ⟨ha, he⟩ := readTree_sound x d ts q [] hr
      exact ⟨ha, by simpa using he, hn⟩
  · rintro ⟨ha, rfl, hn⟩
    have hr := readTree_preorder x p ha []
    rw [List.append_nil] at hr
    simp [positions_preorder] at hn
    simp [checkedTree, hr, hn]

/-- Accepting token lists retain every ordered parse and its unique matching
leaf bijection. The two domain sizes agree since the parse has exactly one
leaf per bit of the input. -/
noncomputable def choiceEquiv (d : Fin n) (hsize : d.val + 1 = m) (x : Fin m → Bool) :
    {ts : List (Token m H) // (checkedTree x d.val ts).isSome} ≃ ParseChoice H d x where
  toFun t := by
    let p := (checkedTree x d.val t.val).get t.property
    have he : checkedTree x d.val t.val = some p := (Option.some_get _).symm
    have hs := (checkedTree_eq_some_iff ..).1 he
    exact ⟨p, bijectionOfMarks hsize p x hs.1 (hs.2.1 ▸ hs.2.2)⟩
  invFun a := ⟨preorder a.1, by
    rw [(checkedTree_eq_some_iff x _ a.1).2
      ⟨agrees_of_bijection x a.1 a.2, rfl, marks_of_bijection a.1 x a.2⟩]
    rfl⟩
  left_inv t := by
    apply Subtype.ext
    exact ((checkedTree_eq_some_iff ..).1 (Option.some_get t.property).symm).2.1.symm
  right_inv a := by
    have hs := (checkedTree_eq_some_iff x _ a.1).2
      ⟨agrees_of_bijection x a.1 a.2, rfl, marks_of_bijection a.1 x a.2⟩
    have he : (checkedTree x d.val (preorder a.1)).get (by simp [hs]) = a.1 :=
      Option.some.inj ((Option.some_get _).trans hs)
    apply Sigma.ext he
    have := LeafBijection.subsingleton_of_injective a.1.leaves
      (q := fun j : Fin m => (j, x j)) (fun _ _ h => congrArg Prod.fst h)
    exact heq_of_eqRec_eq (congrArg (fun t => LeafBijection t.leaves (fun j => (j, x j))) he)
      (Subsingleton.elim _ _)

end PrimedCounter

end VPVNP
end Computability
end OAI
