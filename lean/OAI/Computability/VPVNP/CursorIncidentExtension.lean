import OAI.Computability.VPVNP.CursorValidatorContraction

/-!
# Extending arbitrary local cursor fields to physical RAM sends

At a single cursor-zero site its two endpoints of each cross-site sorting
layer are distinct. Its successor predecessor and successor sender are also
distinct, with a zero clamp at each missing endpoint. Consequently every
local payload vector decoded at cursor zero can be supplied to the compiled
RAM processor by a genuine assignment of its physical shared bits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CursorNetwork

open CursorRouting RAMLayout BurstRAM

variable {D H w : ℕ}

/-- A sender array realizing the selected site's local fields. Other sites
can take arbitrary values beyond the two relevant endpoints of each layer. -/
def localExtension (v : Site D) (outgoing incoming : RAMPayload D H w) : SendArrays D H w :=
  (fun u j =>
    if h : u.val = v.val then
      outgoing (.inl (successorClass (x := v.val) (by have := u.isLt; omega))) j
    else
      incoming (.inl (successorClass (x := u.val) (by have := u.isLt; omega))) j,
   fun l u j => if u = v then outgoing (.inr l) j else incoming (.inr l) j)

theorem localExtension_incident (v : Site D) (outgoing incoming : RAMPayload D H w) :
    incidentBits (localExtension v outgoing incoming) v = decodeIncident v outgoing incoming := by
  let a := localExtension v outgoing incoming
  funext i
  obtain ⟨slot,rfl⟩ := (offset D H w).surjective i
  change incidentBits a v (offset D H w slot) = _
  rw [incidentBits_offset]
  simp only [decodeIncident, Function.comp_apply, Equiv.symm_apply_apply]
  rcases slot with ⟨dir,j⟩ | ⟨l,dir,j⟩ <;> fin_cases dir
  · by_cases hv : v.val+1 < 2^D
    · let u : Fin (2^D-1) := ⟨v.val,by omega⟩
      have h := incident_send a (.inl (u,j))
      change (incidentEquiv D H w a).val (v, .inl (0,j)) = a.1 u j at h
      refine h.trans ?_
      simp [decodeSlot,a,localExtension,u,hv]
    · have hend : v.val+1 = 2^D := by have := v.isLt; omega
      rw [incident_clamp a _ (peer_send_end v hend j)]
      simp [decodeSlot,hv]
  · by_cases hv : 0 < v.val
    · refine (incident_receive_successor a v hv j).trans ?_
      simp [decodeSlot,hv,a,localExtension,show v.val-1 ≠ v.val by omega]
    · have hz : v.val = 0 := by omega
      rw [incident_clamp a _ (peer_receive_start v hz j)]
      simp [decodeSlot,hv]
  · refine (incident_send a (.inr (l,v,j))).trans ?_
    simp [decodeSlot,localExtension,a]
  · refine (incident_receive_sort a l v j).trans ?_
    simp [decodeSlot,localExtension,a,l.partner_ne v]

end CursorNetwork

end VPVNP
end Computability
end OAI
