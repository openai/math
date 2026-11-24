import OAI.Computability.VPVNP.CursorRAMFields
import OAI.Computability.VPVNP.CursorPadding
import OAI.Computability.VPVNP.IncidentPathFiniteness
import OAI.Computability.VPVNP.NetworkMonomials

/-!
# Local path counts at cursor zero

In Section 12 of *VP and VNP differ over every field* the selected outgoing and
returning fields at cursor zero supply the incident bits of the local RAM
validator. Successor fields use their unique active mask class, and a missing
successor at either endpoint supplies zero. Sorting layers have a field in
each direction. We identify this local decoder with the physical bit layout.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CursorNetwork

open CursorRouting RAMLayout BurstRAM BurstRAM.PrivateRAM

variable {D H w : ℕ}

/-- All mask-system fields on one selected side of a cursor site. -/
abbrev RAMPayload (D H w : ℕ) := (s : RAMSystem D) → Fin (ramFieldBits H w s) → Bool

/-- Decode one incident slot using only the two sets of fields delivered to
this site's validator. -/
def decodeSlot (v : Site D) (outgoing incoming : RAMPayload D H w) : Slot D H w → Bool
  | .inl (dir, j) =>
    if dir = 0 then
      if h : v.val + 1 < 2 ^ D then outgoing (.inl (successorClass h)) j else false
    else
      if h : 0 < v.val then
        incoming (.inl (successorClass (x := v.val - 1) (by have := v.isLt; omega))) j
      else false
  | .inr (s, dir, j) => if dir = 0 then outgoing (.inr s) j else incoming (.inr s) j

/-- Serialize the decoded slots in the order expected by the RAM validator. -/
def decodeIncident (v : Site D) (outgoing incoming : RAMPayload D H w) :
    Fin (width D H w) → Bool :=
  decodeSlot v outgoing incoming ∘ (offset D H w).symm

/-- For a routed assignment, the local decoder reads exactly the bit vector
at the corresponding site of the original transcript. -/
theorem decodeIncident_ram (a : SendArrays D H w) (v : Site D) :
    decodeIncident v (fun s ↦ ramSend a s v) (fun s ↦ ramReceive a s v) =
      RAMLayout.incidentBits a v := by
  funext i
  obtain ⟨p, rfl⟩ := (offset D H w).surjective i
  simp only [decodeIncident, Function.comp_apply, Equiv.symm_apply_apply, incidentBits_offset]
  rcases p with ⟨dir, j⟩ | ⟨s, dir, j⟩ <;> fin_cases dir
  · by_cases h : v.val + 1 < 2 ^ D
    · simpa [decodeSlot, h] using ramSend_successor a v h j
    · have hend : v.val + 1 = 2 ^ D := by have := v.isLt; omega
      simpa [decodeSlot, h] using
        (incident_clamp a (v, .inl (0, j)) (peer_send_end v hend j)).symm
  · by_cases h : 0 < v.val
    · simpa [decodeSlot, h] using ramReceive_successor a v h j
    · have hstart : v.val = 0 := by omega
      simpa [decodeSlot, h] using
        (incident_clamp a (v, .inl (1, j)) (peer_receive_start v hstart j)).symm
  · simpa [decodeSlot] using ramSend_sort a s v j
  · simpa [decodeSlot] using ramReceive_sort a s v j

variable {p r k e : ℕ}

/-- The genuine accepting private strings for the supplied local cursor bits. -/
abbrev validatorPaths (M : Machine w p r k) (fuel : ℕ) (initial : Word w) (header : ℕ → Word w)
    (hw : 2 ≤ w) (hc : 2 ^ D * 2 ^ e < 2 ^ w) (v : Site D)
    (outgoing incoming : RAMPayload D (2 ^ e) w) :=
  M.IncidentPaths fuel initial (header v) hw hc v (decodeIncident v outgoing incoming)

/-- Summing the zero-cursor local counts against the physical sender arrays
gives the capped path count, with every private choice retaining its own
multiplicity. -/
theorem validatorPaths_sum [NeZero D] (M : Machine w p r k) (fuel : ℕ) (initial : Word w)
    (header : ℕ → Word w) (hw : 2 ≤ w) (hc : 2 ^ D * 2 ^ e < 2 ^ w) :
    (∑ a : SendArrays D (2 ^ e) w, ∏ v : Site D, Nat.card
      (validatorPaths M fuel initial header hw hc v (fun s ↦ ramSend a s v)
        (fun s ↦ ramReceive a s v))) =
      Nat.card (ActualPaths M.program fuel initial (RAMMemory.initialMemory (2 ^ D) header)
        (withinCaps (2 ^ D) (2 ^ e))) := by
  rw [← ramContraction_pathCount M.program fuel initial header hw hc, ramContraction_eq]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro v _
  simp only [validatorPaths, decodeIncident_ram]
  have he : BurstRAM.incidentBits ((sendArraysEquiv D (2 ^ e) w).symm a) v =
      RAMLayout.incidentBits a v := by
    simp [BurstRAM.incidentBits]
  exact he ▸ Nat.card_congr (M.incidentPathEquiv fuel initial header hw hc
    ((sendArraysEquiv D (2 ^ e) w).symm a) v)

open NetworkKernel

variable [NeZero D]

/-- The initial network of Section 12 has a bit field for every RAM mask
system on each of the two arcs leaving each cursor position. -/
noncomputable abbrev validatorNetwork (D e w : ℕ) :=
  network D (ramFieldBits (2 ^ e) w : RAMSystem D → ℕ)

open scoped Classical in
/-- A valid transit vertex contributes its unique empty choice. At cursor
zero the local choices are the private binary paths of the site validator. -/
noncomputable def initialChoices (M : Machine w p r k) (fuel : ℕ) (initial : Word w)
    (header : ℕ → Word w) (hw : 2 ≤ w) (hc : 2 ^ D * 2 ^ e < 2 ^ w)
    (v : Position D) (z : (validatorNetwork D e w).Half v) : Type :=
  if Checks systemMask v z then
    if v.1 = 0 then
      if ActiveSends v.2 (sent systemMask v z) then
        validatorPaths M fuel initial header hw hc v.2
          (sent systemMask v z) (received systemMask v z)
      else Empty
    else Unit
  else Empty

instance (M : Machine w p r k) (fuel : ℕ) (initial : Word w) (header : ℕ → Word w)
    (hw : 2 ≤ w) (hc : 2 ^ D * 2 ^ e < 2 ^ w) (v : Position D)
    (z : (validatorNetwork D e w).Half v) :
    Finite (initialChoices M fuel initial header hw hc v z) := by
  unfold initialChoices
  split_ifs <;> infer_instance

noncomputable instance initialChoicesFintype (M : Machine w p r k) (fuel : ℕ)
    (initial : Word w) (header : ℕ → Word w)
    (hw : 2 ≤ w) (hc : 2 ^ D * 2 ^ e < 2 ^ w) (v : Position D)
    (z : (validatorNetwork D e w).Half v) :
    Fintype (initialChoices M fuel initial header hw hc v z) := Fintype.ofFinite _

open scoped Classical in
/-- The actual finite cursor network contracts to the capped RAM path count.
The local factor is defined for every half-wire input, even those that never
occur in a globally tied assignment. -/
theorem initialChoices_contract (M : Machine w p r k) (fuel : ℕ) (initial : Word w)
    (header : ℕ → Word w) (hw : 2 ≤ w) (hc : 2 ^ D * 2 ^ e < 2 ^ w) :
    contract (validatorNetwork D e w)
        (fun v z ↦ @Fintype.card _ (initialChoicesFintype M fuel initial header hw hc v z)) =
      Nat.card (ActualPaths M.program fuel initial (RAMMemory.initialMemory (2 ^ D) header)
        (withinCaps (2 ^ D) (2 ^ e))) := by
  let val := fun v out inc ↦ Nat.card (validatorPaths M fuel initial header hw hc v out inc)
  have hf : (fun v z ↦ Fintype.card (initialChoices M fuel initial header hw hc v z)) =
      factors systemMask (fun v out inc ↦ if ActiveSends v out then val v out inc else 0) := by
    funext v z
    rw [← Nat.card_eq_fintype_card]
    unfold initialChoices factors
    split_ifs <;> simp_all [val]
  exact (congrArg (contract (validatorNetwork D e w)) hf).trans
    ((contract_ram val).trans (validatorPaths_sum M fuel initial header hw hc))

/-- Equation (12.2) for the paper's cursor graph, including any required
parallel zero-width slots. Given an exact finite compression history, the sum
of the monomials on its expanded paths equals the capped machine count. -/
noncomputable def expandedRAMCount {A : Type*} [CommRing A] {Label : Type} [Fintype Label]
    {κ : Label → A} (M : Machine w p r k) (fuel : ℕ) (initial : Word w) (header : ℕ → Word w)
    (hw : 2 ≤ w) (hc : 2 ^ D * 2 ^ e < 2 ^ w) (padding : ℕ)
    (T : History A (paddedNetwork D padding (ramFieldBits (2 ^ e) w : RAMSystem D → ℕ)))
    (K : T.KernelWitnesses κ) :
    MonomialWitness κ (Nat.card (ActualPaths M.program fuel initial
      (RAMMemory.initialMemory (2 ^ D) header)
      (withinCaps (2 ^ D) (2 ^ e))) : A) :=
  let P := initialChoices M fuel initial header hw hc
  let counts := fun v z ↦ @Fintype.card _ (initialChoicesFintype M fuel initial header hw hc v z)
  let count_eq := (contract_padded padding counts).trans
    (initialChoices_contract M fuel initial header hw hc)
  let fin : ∀ (v : Position D)
      (z : (paddedNetwork D padding (ramFieldBits (2 ^ e) w : RAMSystem D → ℕ)).Half v),
      Fintype (P v (unpadHalf padding v z)) :=
    fun v z ↦ initialChoicesFintype M fuel initial header hw hc v (unpadHalf padding v z)
  (@History.expandedCount A _ Label _ κ _ T K
      (fun v z ↦ P v (unpadHalf padding v z)) fin).changeValue
    (congrArg (fun n : ℕ ↦ (n : A)) count_eq)

end CursorNetwork

end VPVNP
end Computability
end OAI
