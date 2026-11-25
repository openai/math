import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchPrune
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PortTreeCover

/-! # Internal port graph of a pruned trivalent tensor tree

A role is the address of a trivalent table in the ordered tree. Left and
right children are encoded by appending `false` and `true`, respectively.
Each nonroot role supplies one wire directed to its parent. Boundary stubs
have no role, including the free output at the root.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarPatch.TrivalentTree

variable {K V : Type*} {d : V → ℕ} {q i j : ℕ}

/-- The addresses of all branch constructors of the pruned tree. -/
def branchAddresses : {q : ℕ} → TrivalentTree K d q → Finset (List Bool)
  | _, .port _ => ∅
  | _, .branch _ l r =>
    insert [] ((l.branchAddresses.image (List.cons false)) ∪
      (r.branchAddresses.image (List.cons true)))

@[simp] theorem nil_mem_branchAddresses (B : TriTable K q i j)
    (l : TrivalentTree K d i) (r : TrivalentTree K d j) :
    [] ∈ (branch B l r).branchAddresses := Finset.mem_insert_self ..

@[simp] theorem left_mem_branchAddresses (B : TriTable K q i j)
    (l : TrivalentTree K d i) (r : TrivalentTree K d j) (p : List Bool) :
    false :: p ∈ (branch B l r).branchAddresses ↔ p ∈ l.branchAddresses := by
  simp [branchAddresses]

@[simp] theorem right_mem_branchAddresses (B : TriTable K q i j)
    (l : TrivalentTree K d i) (r : TrivalentTree K d j) (p : List Bool) :
    true :: p ∈ (branch B l r).branchAddresses ↔ p ∈ r.branchAddresses := by
  simp [branchAddresses]

theorem card_branchAddresses (t : TrivalentTree K d q) : t.branchAddresses.card = t.vertices := by
  induction t with
  | port => rfl
  | branch B l r hl hr =>
    have hd : Disjoint (l.branchAddresses.image (List.cons false))
        (r.branchAddresses.image (List.cons true)) := by
      refine Finset.disjoint_left.mpr ?_
      rintro _ h h'
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp h
      simp at h'
    simp [branchAddresses, Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective _ List.cons_injective, hl, hr, vertices]

/-- Deleting the last step of an internal address stays in the internal tree. -/
theorem dropLast_mem_branchAddresses (t : TrivalentTree K d q) {p : List Bool}
    (hp : p ∈ t.branchAddresses) : p.dropLast ∈ t.branchAddresses := by
  induction t generalizing p with
  | port => simp [branchAddresses] at hp
  | branch B l r hl hr =>
    cases p with
    | nil => simp
    | cons b p =>
      by_cases h : p = []
      · subst p
        simp
      · rw [List.dropLast_cons_of_ne_nil h]
        cases b
        · exact (left_mem_branchAddresses ..).mpr (hl ((left_mem_branchAddresses ..).mp hp))
        · exact (right_mem_branchAddresses ..).mpr (hr ((right_mem_branchAddresses ..).mp hp))

/-- Each role carries one ternary table of the given tree. -/
abbrev Role (t : TrivalentTree K d q) := {p // p ∈ t.branchAddresses}

/-- Each internal wire is indexed by its child role, which differs from the root. -/
abbrev InternalWire (t : TrivalentTree K d q) := {v : t.Role // v.val ≠ []}

theorem card_role (t : TrivalentTree K d q) : Fintype.card t.Role = t.vertices :=
  (Fintype.card_coe _).trans t.card_branchAddresses

/-- The output and the labeled input stubs are external. The remaining wires
join each table to the table reached by dropping its last left/right step. -/
def internalGraph (t : TrivalentTree K d q) : PortGraph t.Role t.InternalWire where
  tail e := e.val
  head e := ⟨e.val.val.dropLast, t.dropLast_mem_branchAddresses e.val.property⟩

/-- The role at the root exists whenever pruning retains two or more input stubs. -/
theorem root_mem_of_two_labels (t : TrivalentTree K d q) (h : 2 ≤ t.labels.length) :
    [] ∈ t.branchAddresses := by
  cases t with
  | port => simp [labels] at h
  | branch => exact nil_mem_branchAddresses ..

/-- Parent wires and address lengths give the internal graph its rooted tree structure. -/
def rootedTreeData (t : TrivalentTree K d q) (h : [] ∈ t.branchAddresses) :
    PortGraph.RootedTreeData t.internalGraph (⟨[], h⟩ : t.Role) where
  edge :=
    { toFun := fun v => ⟨v.val, fun e => v.property (Subtype.ext e)⟩
      invFun := fun e => ⟨e.val, fun v => e.property (congrArg Subtype.val v)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  side _ := false
  at_child _ := rfl
  depth v := v.val.length
  toward_root v := by
    change v.val.val.dropLast.length < v.val.val.length
    have hn : v.val.val ≠ [] := fun e => v.property (Subtype.ext e)
    have hp := List.length_pos_iff.mpr hn
    rw [List.length_dropLast]
    omega

end PlanarPatch.TrivalentTree

end SpectralBooks
end LinearAlgebra
end OAI
