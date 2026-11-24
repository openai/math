import OAI.Computability.VPVNP.CursorNetwork

/-!
# Reindexing cursor fields by physical RAM sends

Each internal successor boundary has exactly one active mask. After clamping
all other successor fields to zero, the independent source settings in the
cursor contraction are in bijection with the original RAM send arrays.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CursorNetwork

open CursorRouting RAMLayout NetworkKernel

variable {D H w : ℕ}

/-- A site can send a nonzero successor field only in the class of its own
nonwrapping successor. Every sorting-system send is active. -/
def ActiveSends (x : Site D) (out : Payload (ramFieldBits H w : RAMSystem D → ℕ)) : Prop :=
  ∀ k : Fin D, ¬ (x.val + 1 < 2 ^ D ∧ x.val ^^^ (x.val + 1) = (systemMask (.inl k)).val) →
    out (.inl k) = fun _ ↦ false

theorem activeSends_ramSend (a : SendArrays D H w) (x : Site D) :
    ActiveSends x (fun s ↦ ramSend a s x) :=
  fun k h ↦ funext (ramSend_successor_unused a k x h)

/-- Restrict a site's expanded payload to the physical successor and sorting sends. -/
private def physicalSends (out : Site D → Payload (ramFieldBits H w : RAMSystem D → ℕ)) :
    SendArrays D H w :=
  (fun u ↦ out ⟨u.val, by have := u.isLt; omega⟩
    (.inl (successorClass (x := u.val) (by have := u.isLt; omega))),
   fun l x ↦ out x (.inr l))

private theorem ramSend_physicalSends {out : Site D → Payload (ramFieldBits H w : RAMSystem D → ℕ)}
    (h : ∀ x, ActiveSends x (out x)) (x : Site D) (s : RAMSystem D) :
    ramSend (physicalSends out) s x = out x s := by
  cases s with
  | inl k =>
    funext j
    by_cases hs : x.val + 1 < 2 ^ D ∧ x.val ^^^ (x.val + 1) = (systemMask (.inl k)).val
    · have hk : successorClass hs.1 = k := (successorClass_eq_iff hs.1 k).mpr hs.2
      simp only [ramSend, dite_eq_left hs, physicalSends]
      exact congrArg (fun l : Fin D ↦ out x (.inl l) j) hk
    · exact (ramSend_successor_unused (physicalSends out) k x hs j).trans
        (congrFun (h x k hs) j).symm
  | inr l => rfl

/-- Exactly the expanded source assignments satisfying the local clamps
survive, once for each setting of the physical send arrays. -/
def activeSendsEquiv (D H w : ℕ) : SendArrays D H w ≃
    {out : Site D → Payload (ramFieldBits H w : RAMSystem D → ℕ) //
      ∀ x, ActiveSends x (out x)} where
  toFun a := ⟨fun x s ↦ ramSend a s x, activeSends_ramSend a⟩
  invFun out := physicalSends out.val
  left_inv a := by
    apply ramSend_injective
    funext s x
    exact ramSend_physicalSends (activeSends_ramSend a) x s
  right_inv out := Subtype.ext (funext fun x ↦ funext fun s ↦ ramSend_physicalSends out.prop x s)

variable {k : Type*} [CommSemiring k] [NeZero D]

open scoped Classical in
/-- For any local validator the cursor contraction with inactive sends clamped
is exactly the RAM contraction indexed by the original send arrays. -/
theorem contract_ram
    (validator : Site D → Payload (ramFieldBits H w : RAMSystem D → ℕ) →
      Payload (ramFieldBits H w : RAMSystem D → ℕ) → k) :
    contract (network D (ramFieldBits H w : RAMSystem D → ℕ))
      (factors systemMask (fun x out inc ↦ if ActiveSends x out then validator x out inc else 0)) =
      ∑ a : SendArrays D H w, ∏ x : Site D,
        validator x (fun s ↦ ramSend a s x) (fun s ↦ ramReceive a s x) := by
  rw [contract_eq]
  simp_rw [Fintype.prod_ite_zero]
  let good (a : Site D → Payload (ramFieldBits H w : RAMSystem D → ℕ)) := ∀ x, ActiveSends x (a x)
  let wt (a : Site D → Payload (ramFieldBits H w : RAMSystem D → ℕ)) :=
    ∏ x, validator x (a x) (returned systemMask a x)
  trans ∑ a ∈ Finset.univ.filter good, wt a
  · rw [Finset.sum_filter]
    refine Finset.sum_congr ?_ fun a _ ↦ ?_
    · ext a
      simp
    · exact ite_congr rfl (fun _ ↦ rfl) (fun _ ↦ rfl)
  · rw [Finset.sum_subtype (p := good) _ (fun _ ↦ by simp) wt]
    exact (Fintype.sum_equiv (activeSendsEquiv D H w) _ (fun a ↦ wt a.val) fun _ ↦ rfl).symm

end CursorNetwork

end VPVNP
end Computability
end OAI
