import OAI.Computability.VPVNP.RAMLayout
import Mathlib.Data.Fintype.Pi

/-!
# Indexing shared assignments by physical sends

A shared assignment in Lemma 10.1 consists of one successor message for each
of the first `S-1` sites and one sorting send per layer and site. The final
successor send and the initial successor receive are clamped. The following
equivalences retain exactly the bits of those actual messages.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMLayout

instance (d : ℕ) : Fintype (Layer d) :=
  Fintype.ofEquiv (Fin (layerCount d)) (layerEquiv d).symm

instance (d H w : ℕ) : DecidableEq (SharedBit d H w) :=
  fun x y ↦ decidable_of_iff (x.val = y.val) Subtype.ext_iff.symm

/-- Index of one transmitted bit, either on an internal successor wire or in a specified site’s
outgoing block for a sorting layer. -/
abbrev SendIndex (d H w : ℕ) :=
  (Fin (2 ^ d - 1) × Fin (8 * w)) ⊕ (Layer d × (Fin (2 ^ d) × Fin (blockBits H w)))

variable {d H w : ℕ}

/-- The physical source endpoint of each indexed send. -/
def sendBit : SendIndex d H w → SharedBit d H w
  | .inl (u, j) =>
    let v : Fin (2 ^ d) := ⟨u.val, by have := u.isLt; omega⟩
    ⟨(v, .inl (0, j)), rfl, by
      have hv : v.val + 1 < 2 ^ d := by have := u.isLt; dsimp [v]; omega
      simp [peer, hv]⟩
  | .inr (s, v, j) => ⟨(v, .inr (s, 0, j)), rfl, by simp [peer]⟩

private theorem existing_successor {v : Fin (2 ^ d)} {j : Fin (8 * w)}
    (h : (peer (H := H) v (.inl (0, j))).isSome) : v.val < 2 ^ d - 1 := by
  by_contra hn
  have hh : ¬ v.val + 1 < 2 ^ d := by omega
  simp [peer, hh] at h

/-- Recover the array indices of an actual sender from its endpoint. -/
def indexOfSend (x : SharedBit d H w) : SendIndex d H w :=
  match h : x.val.2 with
  | .inl (dir, j) =>
    .inl (⟨x.val.1.val, existing_successor (H := H) (j := j) (by
      have hd := x.property.1
      have hp := x.property.2
      rw [h] at hd hp
      change dir = 0 at hd
      simpa [hd] using hp)⟩, j)
  | .inr (s, _, j) => .inr (s, x.val.1, j)

/-- Bijection between successor-or-sorting array indices and their physical shared sender
endpoints. -/
def sendIndexEquiv (d H w : ℕ) : SendIndex d H w ≃ SharedBit d H w where
  toFun := sendBit
  invFun := indexOfSend
  left_inv i := by
    rcases i with ⟨⟨v, hv⟩, j⟩ | ⟨s, v, j⟩ <;> rfl
  right_inv x := by
    rcases x with ⟨⟨v, ⟨dir, j⟩ | ⟨s, dir, j⟩⟩, hd, _⟩ <;>
      change dir = 0 at hd <;> subst dir <;> rfl

/-- One successor vector for each internal boundary and one block vector for
each sorting exchange. Each array entry is the vector sent by the named site. -/
abbrev SendArrays (d H w : ℕ) :=
  (Fin (2 ^ d - 1) → Fin (8 * w) → Bool) ×
    (Layer d → Fin (2 ^ d) → Fin (blockBits H w) → Bool)

/-- Reindex an assignment on shared bits as the array of successor messages and the
layer-by-site array of sorting blocks. -/
def sendArraysEquiv (d H w : ℕ) : (SharedBit d H w → Bool) ≃ SendArrays d H w where
  toFun b := (fun v j ↦ b (sendBit (.inl (v, j))),
    fun s v j ↦ b (sendBit (.inr (s, v, j))))
  invFun a x :=
    match indexOfSend x with
    | .inl (v, j) => a.1 v j
    | .inr (s, v, j) => a.2 s v j
  left_inv b := by
    funext x
    obtain ⟨i, rfl⟩ := (sendIndexEquiv d H w).surjective x
    rcases i with ⟨⟨v, hv⟩, j⟩ | ⟨s, v, j⟩ <;> rfl
  right_inv a := by
    apply Prod.ext
    · funext ⟨v, hv⟩ j
      rfl
    · rfl

/-- Reconstruct compatible incident fields from sender-indexed message arrays. -/
def incidentEquiv (d H w : ℕ) :
    SendArrays d H w ≃ {b : Endpoint d H w → Bool // Compatible b} :=
  (sendArraysEquiv d H w).symm.trans (assignmentEquiv d H w)

/-- Linear local bit address for a site's physical sender arrays. -/
def incidentBits (a : SendArrays d H w) (v : Fin (2 ^ d)) : Fin (width d H w) → Bool :=
  fun i ↦ (incidentEquiv d H w a).val (v, (offset d H w).symm i)

@[simp] theorem incidentBits_offset (a : SendArrays d H w) (v : Fin (2 ^ d)) (p : Slot d H w) :
    incidentBits a v (offset d H w p) = (incidentEquiv d H w a).val (v, p) := by
  simp [incidentBits]

theorem incident_send (a : SendArrays d H w) (i : SendIndex d H w) :
    (incidentEquiv d H w a).val (sendBit i).val =
      match i with
      | .inl (v, j) => a.1 v j
      | .inr (s, v, j) => a.2 s v j := by
  have hinv := (assignmentEquiv d H w).symm_apply_apply ((sendArraysEquiv d H w).symm a)
  have he := congrFun hinv (sendBit i)
  rcases i with ⟨⟨v, hv⟩, j⟩ | ⟨s, v, j⟩ <;> exact he

theorem incident_receive_sort (a : SendArrays d H w) (s : Layer d) (v : Fin (2 ^ d))
    (j : Fin (blockBits H w)) :
    (incidentEquiv d H w a).val (v, .inr (s, 1, j)) = a.2 s (s.partner v) j := by
  have h : peer v (.inr (s, 1, j)) = some (sendBit (.inr (s, s.partner v, j))).val := rfl
  exact ((incidentEquiv d H w a).property.2 _ _ h).trans (incident_send a (.inr (s, s.partner v, j)))

theorem incident_receive_successor (a : SendArrays d H w) (v : Fin (2 ^ d)) (hv : 0 < v.val)
    (j : Fin (8 * w)) :
    (incidentEquiv d H w a).val (v, .inl (1, j)) =
      a.1 ⟨v.val - 1, by have := v.isLt; omega⟩ j := by
  let u : Fin (2 ^ d - 1) := ⟨v.val - 1, by have := v.isLt; omega⟩
  have h : peer (H := H) v (.inl (1, j)) = some (sendBit (.inl (u, j))).val := by
    simp [peer, hv, sendBit, u]
  exact ((incidentEquiv d H w a).property.2 _ _ h).trans (incident_send a (.inl (u, j)))

theorem incident_clamp (a : SendArrays d H w) (x : Endpoint d H w) (h : peer x.1 x.2 = none) :
    (incidentEquiv d H w a).val x = false := (incidentEquiv d H w a).property.1 x h

end RAMLayout

end VPVNP
end Computability
end OAI
