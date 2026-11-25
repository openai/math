import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.TrivalentPortTree

/-! # Local tables at the internal addresses of a trivalent tree -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarPatch.TrivalentTree

variable {K V : Type*} {d : V → ℕ} {q i j : ℕ}

/-- The local tensor with its output, ordered input dimensions, and subtrees. -/
structure BranchData (K : Type*) {V : Type*} (d : V → ℕ) where
  q : ℕ
  i : ℕ
  j : ℕ
  coeff : TriTable K q i j
  left : TrivalentTree K d i
  right : TrivalentTree K d j

section
variable (B : TriTable K q i j) (l : TrivalentTree K d i) (r : TrivalentTree K d j)

def rootRole : (branch B l r).Role :=
  ⟨[], nil_mem_branchAddresses ..⟩

def leftRole (v : l.Role) : (branch B l r).Role :=
  ⟨false :: v.val, (left_mem_branchAddresses ..).mpr v.property⟩

def rightRole (v : r.Role) : (branch B l r).Role :=
  ⟨true :: v.val, (right_mem_branchAddresses ..).mpr v.property⟩

@[simp] theorem rootRole_val : (rootRole B l r).val = [] := rfl

@[simp] theorem leftRole_val (v : l.Role) : (leftRole B l r v).val = false :: v.val := rfl

@[simp] theorem rightRole_val (v : r.Role) : (rightRole B l r v).val = true :: v.val := rfl

/-- An internal address is the root or an internal address in exactly one child. -/
def branchRoleEquiv : (branch B l r).Role ≃ Unit ⊕ (l.Role ⊕ r.Role) where
  toFun
    | ⟨[], _⟩ => .inl ()
    | ⟨false :: p, h⟩ => .inr (.inl ⟨p, (left_mem_branchAddresses ..).mp h⟩)
    | ⟨true :: p, h⟩ => .inr (.inr ⟨p, (right_mem_branchAddresses ..).mp h⟩)
  invFun
    | .inl _ => rootRole B l r
    | .inr (.inl v) => leftRole B l r v
    | .inr (.inr v) => rightRole B l r v
  left_inv := by
    rintro ⟨_ | ⟨b,p⟩, _⟩
    · rfl
    · cases b <;> rfl
  right_inv := by
    rintro (⟨⟩ | (v | v)) <;> rfl

@[simp] theorem branchRoleEquiv_rootRole :
    branchRoleEquiv B l r (rootRole B l r) = .inl () := rfl

@[simp] theorem branchRoleEquiv_leftRole (v : l.Role) :
    branchRoleEquiv B l r (leftRole B l r v) = .inr (.inl v) := rfl

@[simp] theorem branchRoleEquiv_rightRole (v : r.Role) :
    branchRoleEquiv B l r (rightRole B l r v) = .inr (.inr v) := rfl

@[simp] theorem branchRoleEquiv_symm_root :
    (branchRoleEquiv B l r).symm (.inl ()) = rootRole B l r := rfl

@[simp] theorem branchRoleEquiv_symm_left (v : l.Role) :
    (branchRoleEquiv B l r).symm (.inr (.inl v)) = leftRole B l r v := rfl

@[simp] theorem branchRoleEquiv_symm_right (v : r.Role) :
    (branchRoleEquiv B l r).symm (.inr (.inr v)) = rightRole B l r v := rfl

end

/-- Recover the actual ordered coefficient tensor at an internal address. -/
def branchAt : {q : ℕ} → (t : TrivalentTree K d q) → t.Role → BranchData K d
  | _, .port _, ⟨_, h⟩ => False.elim (Finset.notMem_empty _ h)
  | _, .branch B l r, ⟨[], _⟩ => ⟨_, _, _, B, l, r⟩
  | _, .branch _ l _, ⟨false :: p, h⟩ =>
    l.branchAt ⟨p, (left_mem_branchAddresses ..).mp h⟩
  | _, .branch _ _ r, ⟨true :: p, h⟩ =>
    r.branchAt ⟨p, (right_mem_branchAddresses ..).mp h⟩

section
variable (B : TriTable K q i j) (l : TrivalentTree K d i) (r : TrivalentTree K d j)

@[simp] theorem branchAt_rootRole :
    (branch B l r).branchAt (rootRole B l r) = ⟨q, i, j, B, l, r⟩ := rfl

@[simp] theorem branchAt_leftRole (v : l.Role) :
    (branch B l r).branchAt (leftRole B l r v) = l.branchAt v := rfl

@[simp] theorem branchAt_rightRole (v : r.Role) :
    (branch B l r).branchAt (rightRole B l r v) = r.branchAt v := rfl

end

/-- A uniform bound on the tree dimensions applies to the output at every role. -/
theorem branchAt_q_le (t : TrivalentTree K d q) {m : ℕ} (h : t.Bounded m)
    (v : t.Role) : (t.branchAt v).q ≤ m := by
  induction t with
  | port => exact False.elim (Finset.notMem_empty _ v.property)
  | branch B l r hl hr =>
    obtain ⟨v | (v | v), rfl⟩ := (branchRoleEquiv B l r).symm.surjective v
    · cases v
      exact h.1
    · exact hl h.2.1 v
    · exact hr h.2.2 v

end PlanarPatch.TrivalentTree

end SpectralBooks
end LinearAlgebra
end OAI
