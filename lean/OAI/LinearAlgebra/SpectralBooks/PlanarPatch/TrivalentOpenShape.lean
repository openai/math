import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.TrivalentPortTree
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementEncoder
import Mathlib.Data.List.Basic

/-! # The actual three incident ports at every vertex of a pruned tensor tree

Paths follow the ordered children. The root output and the leaf inputs are
stubs; every other output is an internal wire to the parent. At a branch the
three incident positions are the output, left input and right input.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace PlanarPatch.TrivalentTree

open PortGraph
open scoped Classical

variable {K V : Type*} {d : V → ℕ} {q : ℕ}

/-- The leaf addresses in left-to-right order, including repeated labels at distinct addresses. -/
def leafPaths : {a : ℕ} → TrivalentTree K d a → List (List Bool)
  | _, .port _ => [[]]
  | _, .branch _ l r => l.leafPaths.map (false :: ·) ++ r.leafPaths.map (true :: ·)

@[simp] theorem leafPaths_length (t : TrivalentTree K d q) : t.leafPaths.length = t.labels.length := by
  induction t <;> simp [leafPaths, labels, *]

theorem leafPaths_nodup (t : TrivalentTree K d q) : t.leafPaths.Nodup := by
  induction t with
  | port => simp [leafPaths]
  | branch B l r hl hr =>
    rw [leafPaths, List.nodup_append]
    exact ⟨hl.map List.cons_injective, hr.map List.cons_injective, by simp⟩

private theorem cons_mem_leaves {a i j : ℕ} (B : TriTable K a i j)
    (l : TrivalentTree K d i) (r : TrivalentTree K d j) (b : Bool) (p : List Bool) :
    b :: p ∈ (branch B l r).leafPaths ↔ if b then p ∈ r.leafPaths else p ∈ l.leafPaths := by
  cases b <;> simp [leafPaths]

private theorem nil_not_mem_leaves {a i j : ℕ} (B : TriTable K a i j)
    (l : TrivalentTree K d i) (r : TrivalentTree K d j) : [] ∉ (branch B l r).leafPaths := by
  simp [leafPaths]

theorem leaf_not_branch (t : TrivalentTree K d q) {p : List Bool}
    (hp : p ∈ t.leafPaths) : p ∉ t.branchAddresses := by
  induction t generalizing p with
  | port => simp [branchAddresses]
  | branch B l r hl hr =>
    cases p with
    | nil => exact False.elim (nil_not_mem_leaves B l r hp)
    | cons b p => cases b <;> simp_all [cons_mem_leaves]

theorem leaf_parent (t : TrivalentTree K d q) {p : List Bool}
    (hp : p ∈ t.leafPaths) (hn : p ≠ []) : p.dropLast ∈ t.branchAddresses := by
  induction t generalizing p with
  | port => simp [leafPaths, hn] at hp
  | branch B l r hl hr =>
    cases p with
    | nil => contradiction
    | cons b p =>
      by_cases h : p = []
      · subst p; simp
      rw [List.dropLast_cons_of_ne_nil h]
      cases b <;> simp_all [cons_mem_leaves]

/-- Both child paths exist at a branch. Branch addresses and leaf addresses are disjoint. -/
theorem child_mem (t : TrivalentTree K d q) {p : List Bool} (hp : p ∈ t.branchAddresses)
    (b : Bool) : p ++ [b] ∈ t.branchAddresses ∨ p ++ [b] ∈ t.leafPaths := by
  induction t generalizing p with
  | port => simp [branchAddresses] at hp
  | branch B l r hl hr =>
    cases p with
    | nil =>
      cases b
      · cases l <;> simp [branchAddresses, leafPaths]
      · cases r <;> simp [branchAddresses, leafPaths]
    | cons a p =>
      cases a <;> simp_all [cons_mem_leaves]

abbrev Leaf (t : TrivalentTree K d q) := {p : List Bool // p ∈ t.leafPaths}
abbrev Stub (t : TrivalentTree K d q) := Option t.Leaf

private theorem leaf_nonempty (t : TrivalentTree K d q) (h : [] ∈ t.branchAddresses) (p : t.Leaf) :
    p.val ≠ [] := fun he => t.leaf_not_branch p.property (he ▸ h)

/-- The root output touches the root and each leaf input touches its parent. -/
def attach (t : TrivalentTree K d q) (h : [] ∈ t.branchAddresses) : t.Stub → t.Role
  | none => ⟨[],h⟩
  | some p => ⟨p.val.dropLast, t.leaf_parent p.property (t.leaf_nonempty h p)⟩

/-- The open port graph retains the literal branch roles and child wires. -/
def openPiece (t : TrivalentTree K d q) (h : [] ∈ t.branchAddresses) : OpenPiece t.Stub where
  Vertex := t.Role
  Edge := t.InternalWire
  graph := t.internalGraph
  attach := t.attach h

/-- A tree template with specified ambient directions on its boundary stubs. -/
def template (t : TrivalentTree K d q) (h : [] ∈ t.branchAddresses) (direction : t.Stub → Bool) :
    ReplacementTemplate.{0,0,0} where
  Role := t.Role
  Wire := t.InternalWire
  Stub := t.Stub
  graph := t.internalGraph
  root := ⟨[],h⟩
  tree := t.rootedTreeData h
  attach := t.attach h
  direction := direction

abbrev TreeEnd (t : TrivalentTree K d q) := (t.InternalWire × Bool) ⊕ t.Stub

/-- Owner of an interior or boundary dart. -/
def endOwner (t : TrivalentTree K d q) (h : [] ∈ t.branchAddresses) : t.TreeEnd → t.Role
  | .inl (w,b) => t.internalGraph.vertex w b
  | .inr s => t.attach h s

/-- The output has index `none`, followed by indices `some false` and `some true`. -/
def endPosition (t : TrivalentTree K d q) (h : [] ∈ t.branchAddresses) : t.TreeEnd → Option Bool
  | .inl (_,false) => none
  | .inl (w,true) => some (w.val.val.getLast w.property)
  | .inr none => none
  | .inr (some p) => some (p.val.getLast (t.leaf_nonempty h p))

/-- A branch's output belongs to the parent wire unless it is the root. -/
def openOutputEnd (t : TrivalentTree K d q) (v : t.Role) : t.TreeEnd :=
  if h : v.val = [] then .inr none else .inl (⟨v,h⟩,false)

/-- The left/right port connects either to the corresponding child branch or to the child stub. -/
def openChildEnd (t : TrivalentTree K d q) (v : t.Role) (b : Bool) : t.TreeEnd :=
  if h : v.val ++ [b] ∈ t.branchAddresses then
    .inl (⟨⟨v.val ++ [b],h⟩, by simp⟩,true)
  else .inr (some ⟨v.val ++ [b], (t.child_mem v.property b).resolve_left h⟩)

@[simp] theorem owner_openOutputEnd (t : TrivalentTree K d q) (h : [] ∈ t.branchAddresses)
    (v : t.Role) : t.endOwner h (t.openOutputEnd v) = v := by
  unfold openOutputEnd
  split
  · apply Subtype.ext; exact ‹_ = []›.symm
  · rfl

@[simp] theorem owner_openChildEnd (t : TrivalentTree K d q) (h : [] ∈ t.branchAddresses)
    (v : t.Role) (b : Bool) : t.endOwner h (t.openChildEnd v b) = v := by
  unfold openChildEnd
  split <;> apply Subtype.ext <;> exact List.dropLast_concat

@[simp] theorem position_openOutputEnd (t : TrivalentTree K d q) (h : [] ∈ t.branchAddresses)
    (v : t.Role) : t.endPosition h (t.openOutputEnd v) = none := by
  unfold openOutputEnd
  split <;> rfl

@[simp] theorem position_openChildEnd (t : TrivalentTree K d q) (h : [] ∈ t.branchAddresses)
    (v : t.Role) (b : Bool) : t.endPosition h (t.openChildEnd v b) = some b := by
  unfold openChildEnd
  split <;> apply congrArg some <;> exact List.getLast_append_singleton _

/-- Exactly one dart of every position occurs at each branch, including the root. -/
def treeEndEquiv (t : TrivalentTree K d q) (h : [] ∈ t.branchAddresses) :
    t.TreeEnd ≃ t.Role × Option Bool where
  toFun e := (t.endOwner h e, t.endPosition h e)
  invFun x := match x.2 with
    | none => t.openOutputEnd x.1
    | some b => t.openChildEnd x.1 b
  right_inv := by rintro ⟨v, _ | b⟩ <;> simp
  left_inv := by
    rintro (⟨w,_|_⟩ | (_ | p))
    · simp [endPosition, endOwner, internalGraph, PortGraph.vertex, openOutputEnd, w.property]
    · have he := List.dropLast_concat_getLast w.property
      simp only [endPosition, endOwner, internalGraph, PortGraph.vertex, openChildEnd, he, w.val.property, ↓reduceDIte]
    · simp [endPosition, endOwner, attach, openOutputEnd]
    · have he := List.dropLast_concat_getLast (t.leaf_nonempty h p)
      simp only [endPosition, endOwner, attach, openChildEnd, he, t.leaf_not_branch p.property, ↓reduceDIte]

/-- The same darts, indexed locally at a fixed table. -/
def openDartEquiv (t : TrivalentTree K d q) (h : [] ∈ t.branchAddresses) (v : t.Role) :
    t.internalGraph.Port v ⊕ {s : t.Stub // t.attach h s = v} ≃
      {e : t.TreeEnd // t.endOwner h e = v} where
  toFun := Sum.elim (fun p => ⟨.inl p.val,p.property⟩) (fun s => ⟨.inr s.val,s.property⟩)
  invFun
    | ⟨.inl p,hp⟩ => .inl ⟨p,hp⟩
    | ⟨.inr s,hs⟩ => .inr ⟨s,hs⟩
  left_inv := by rintro (p | s) <;> rfl
  right_inv := by rintro ⟨(p | s),hp⟩ <;> rfl

/-- Linear port numbers at a branch: 0 is the output, 1 is the left input
and 2 is the right input. This fixes the cyclic order used in the disk. -/
def slotOfPosition : Option Bool ≃ Fin 3 where
  toFun
    | none => 0
    | some false => 1
    | some true => 2
  invFun i := if i = 0 then none else some (i != 1)
  left_inv := by rintro (_ | (_ | _)) <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- The local table has exactly the three ordered positions at every role. -/
def openSlotEquiv (t : TrivalentTree K d q) (h : [] ∈ t.branchAddresses) (v : t.Role) :
    t.internalGraph.Port v ⊕ {s : t.Stub // t.attach h s = v} ≃ Fin 3 :=
  (t.openDartEquiv h v).trans <| (Equiv.ofBijective (fun e => t.endPosition h e.val) (by
    constructor
    · rintro ⟨a,ha⟩ ⟨b,hb⟩ hab
      exact Subtype.ext ((t.treeEndEquiv h).injective (Prod.ext (ha.trans hb.symm) hab))
    · intro pos
      let e := (t.treeEndEquiv h).symm (v, pos)
      have he : (t.endOwner h e, t.endPosition h e) = (v,pos) := (t.treeEndEquiv h).apply_symm_apply _
      exact ⟨⟨e,congrArg Prod.fst he⟩,congrArg Prod.snd he⟩)).trans slotOfPosition

theorem openSlotEquiv_apply (t : TrivalentTree K d q) (h : [] ∈ t.branchAddresses)
    (v : t.Role) (p : t.internalGraph.Port v ⊕ {s : t.Stub // t.attach h s = v}) :
    t.openSlotEquiv h v p = slotOfPosition (t.endPosition h ((t.openDartEquiv h v) p).val) := rfl

end PlanarPatch.TrivalentTree

end

end SpectralBooks
end LinearAlgebra
end OAI
