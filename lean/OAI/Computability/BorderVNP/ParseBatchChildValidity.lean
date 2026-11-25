import OAI.Computability.BorderVNP.ParseBatchRecordsCheck

/-! # Finite-index interface for the batched child lookups -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseRecords

open VPVNP

variable {V H : Type*} {n J : ℕ}

/-- An addressed read of a finite table succeeds precisely when a physical row with the
given index and label exists. This includes rejection beyond the last row. -/
theorem rootAt_ofFn_iff (rs : Fin J → GrammarLabel V H n) (u k : ℕ) (h : H) :
    RootAt (List.ofFn rs) u k h ↔
      ∃ t : Fin J, t.val = u ∧ depth (rs t) = k ∧ state (rs t) = h := by
  constructor
  · rintro ⟨a, ha, hd, hs⟩
    obtain ⟨hu, he⟩ := List.getElem?_eq_some_iff.mp ha
    let t : Fin J := ⟨u, by simpa using hu⟩
    have he' : rs t = a := by simpa only [List.getElem_ofFn] using he
    exact ⟨t, rfl, he' ▸ hd, he' ▸ hs⟩
  · rintro ⟨t, rfl, hd, hs⟩
    refine ⟨rs t, ?_, hd, hs⟩
    exact List.getElem?_eq_some_iff.mpr ⟨by simp, by simp⟩

private theorem local_ofFn_iff (rs : Fin J → GrammarLabel V H n) (u : Fin J) :
    Local (List.ofFn rs) u.val (rs u) ↔ u.val+2*depth (rs u) < J ∧
      ∀ q ∈ childRequests u.val (rs u),
        ∃ t : Fin J, t.val = q.address ∧ depth (rs t) = q.layer ∧ state (rs t) = q.parent := by
  rcases hr : rs u with v | ⟨d,h,b,i,j⟩ <;>
    simp only [Local, List.length_ofFn, childRequests, List.mem_cons, List.not_mem_nil, or_false,
      false_implies, and_true, forall_eq_or_imp, forall_eq, rootAt_ofFn_iff]
  simp

/-- The abstract preorder verifier on a fixed-length physical block is equivalent to the
pointwise format/interval/root checks and the batched lookup relation. -/
theorem valid_ofFn_iff (d : Fin n) (h : H) (rs : Fin (2*d.val+1) → GrammarLabel V H n) :
    Valid d h (List.ofFn rs) ↔
      (∀ u : Fin (2*d.val+1), u.val + 2*depth (rs u) < 2*d.val+1 ∧
        (u.val = 0 → depth (rs u) = d.val ∧ state (rs u) = h)) ∧
      ∀ u : Fin (2*d.val+1), ∀ q ∈ childRequests u.val (rs u),
        ∃ t : Fin (2*d.val+1), t.val = q.address ∧ depth (rs t) = q.layer ∧ state (rs t) = q.parent := by
  have hlocal : (∀ u r, (List.ofFn rs)[u]? = some r → Local (List.ofFn rs) u r) ↔
      ∀ u : Fin (2*d.val+1), Local (List.ofFn rs) u.val (rs u) := by
    constructor
    · intro all u
      exact all _ _ (List.getElem?_eq_some_iff.mpr
        ⟨by simpa only [List.length_ofFn] using u.isLt, by simp only [List.getElem_ofFn]⟩)
    · intro all u r hr
      obtain ⟨hu, he⟩ := List.getElem?_eq_some_iff.mp hr
      let i : Fin (2*d.val+1) := ⟨u, by simpa using hu⟩
      have hi : rs i = r := by simpa only [List.getElem_ofFn] using he
      exact hi ▸ all i
  simp only [Valid, List.length_ofFn, true_and, hlocal, rootAt_ofFn_iff, local_ofFn_iff]
  constructor
  · rintro ⟨⟨root, hroot, hd, hs⟩, all⟩
    refine ⟨fun u => ⟨(all u).1, fun hu => ?_⟩, fun u => (all u).2⟩
    have he : u = root := Fin.ext (hu.trans hroot.symm)
    exact he ▸ ⟨hd, hs⟩
  · rintro ⟨rows, children⟩
    let z : Fin (2*d.val+1) := ⟨0, Nat.succ_pos _⟩
    exact ⟨⟨z, rfl, (rows z).2 rfl⟩, fun u => ⟨(rows u).1, children u⟩⟩

end ParseRecords

end BorderVNP
end Computability
end OAI
