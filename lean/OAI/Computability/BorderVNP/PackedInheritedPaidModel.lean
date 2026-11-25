import OAI.Computability.BorderVNP.PackedInheritedPaidState
import OAI.Computability.BorderVNP.PackedInheritedFieldWeight
import OAI.Computability.BorderVNP.PackedInheritedRoundValue
import OAI.Computability.BorderVNP.PackedBankBoxTags

/-! # Paid-site birth on the sewn combining-step layout

The private fragment uses actual cable ordinals in the site's intrinsic input bank.
Its unique accepting staging word produces the genuine paid entry at each copy,
including zero-valued entries. Consequently the site can be saved, rebinned and
sewn again using the persistent local-table invariant.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Crossing.CellBox Shortening Shortening.CombiningStep PaidBox
open scoped Classical

namespace PaidSite

open private cable_width orderedLane readLane from OAI.Computability.BorderVNP.PackedBankBoxPhysical
open private bits_right from OAI.Computability.BorderVNP.PackedInheritedStaging
open private extendWires extendPorts from OAI.Computability.BorderVNP.PackedInheritedRoundValue
open private observed_ids from OAI.Computability.BorderVNP.PackedBankBoxTags

variable {D m ne np : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
    {P : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
    {A : Type} [Fintype A] (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
    (s : A) (a : Fin e.count) (v : (e.net a).Site)
    (edgeID : (output e p bin perm positive first q).layout.Edge ↪ Fin ne) (portID : P ↪ Fin np)

local notation3 "G₀" => (output e p bin perm positive first q).layout
local notation3 "here₀" => PaidPhysical.site e p bin perm positive first q s a v
local notation3 "ws" => PaidBox.widths (e.net a) v
local notation3 "cp₀" => Subtype.val (q s) a
local notation3 "inc₀" => incoming G₀ here₀

/-- Intrinsic incoming base of each physical term cable or feeder, in stable public edge order. -/
noncomputable def starts (r : Fin (Fintype.card (PaidBox.Bundle (e.net a) v))) : ℕ :=
  wireStart G₀ edgeID portID here₀
    (PaidPhysical.cable e p bin perm positive first q s a v ((Fintype.equivFin _).symm r))

local notation3 "start₀" => starts e p bin perm positive first q s a v edgeID portID
local notation3 "source₀" => source ws cp₀ start₀

/-- The true copied bundle occupies its full intrinsic interval, even when the width is zero. -/
theorem physical_room : Room ws cp₀ inc₀ start₀ := by
  intro r
  let b := (Fintype.equivFin (PaidBox.Bundle (e.net a) v)).symm r
  have h := wireEnd_le G₀ edgeID portID here₀ (PaidPhysical.cable e p bin perm positive first q s a v b)
  rw [cable_width] at h
  exact h

variable (position : e.Entry → ℕ)

/-- The persistent intrinsic birth program of an actual newly inserted paid site. -/
noncomputable def physical : Site := born ws cp₀ inc₀ start₀ (tableFactor e position a v)

local notation3 "state₀" => physical e p bin perm positive first q s a v edgeID portID position

/-- The birth program reads only its declared work and physical incident words. -/
theorem physical_local : (state₀).Local :=
  local_born cp₀ inc₀ e position a v start₀ (physical_room e p bin perm positive first q s a v edgeID portID)

variable (y : (output e p bin perm positive first q).layout.Assignment) (x : Ports bits)

local notation3 "input₀" => inputWords G₀ edgeID portID here₀ (fun u => y u.val) (fun u => x u.val)
local notation3 "bank₀" => Inherited.bits (fun _ : Fin (work ws cp₀) => false) input₀
local notation3 "profile₀" => PaidPhysical.profileWires e p bin perm positive first q s y

/-- Each intrinsic cable lane is the bit selected by the original bank's exact copy order. -/
theorem physical_data (i : Fin cp₀) (k : Fin (arity e a v)) :
    PaidBinding.data ws cp₀ source₀ bank₀ i k = PaidBox.data e a v (q s).val profile₀ i k := by
  obtain ⟨⟨r,k⟩,rfl⟩ := (finSigmaFinEquiv (n := ws)).surjective k
  let b := (Fintype.equivFin (PaidBox.Bundle (e.net a) v)).symm r
  let z := PaidPhysical.cable e p bin perm positive first q s a v b
  let lane := Fin.cast (cable_width e p bin perm positive first q s a v b).symm (finProdFinEquiv (i,k))
  let t := sourceOrder G₀ edgeID portID here₀ (.inl ⟨z,lane⟩)
  have pos : lane.val = i.val*ws r+k.val := by simp [lane,b,PaidBox.widths,Nat.mul_comm,Nat.add_comm]
  have hpos : t.val = start₀ r + (i.val*ws r+k.val) :=
    (wireOrdinal G₀ edgeID portID here₀ z lane).trans (congrArg (start₀ r + ·) pos)
  have h := (bits_right (fun _ : Fin (work ws cp₀) => false) input₀ t).trans
    (inputWords_wire G₀ edgeID portID here₀ _ _ z lane)
  change PaidBinding.data ws cp₀ source₀ bank₀ i (finSigmaFinEquiv ⟨r,k⟩) = _
  rw [PaidBinding.data,(finSigmaFinEquiv (n := ws)).symm_apply_apply ⟨r,k⟩,PaidBox.data,orderedLane]
  exact (by simpa only [hpos,source,Nat.add_assoc] using h :
    bank₀ (source₀ r + i.val*ws r+k.val) = y z.val lane).trans
    (readLane e p bin perm positive first q s a v y i b k)

/-- Intrinsic and physical observations address the same paid entry, before specialization. -/
theorem physical_entry (i : Fin cp₀) :
    PaidBinding.entryAt cp₀ e a v source₀ bank₀ i = selectedEntry e a v (q s).val profile₀ i := by
  let encode (b : Lane (e.net a) v → Bool) : e.Entry :=
    ⟨a,v,(fun u k => b (.inl ⟨u,k⟩)),(fun u k => b (.inr ⟨u,k⟩))⟩
  let localBits := fun l => PaidBinding.data ws cp₀ source₀ bank₀ i (laneOrder (e.net a) v l)
  let exactBits := bankLanes e.net antipodalPosition (fun u => by obtain ⟨j,b⟩ := u; cases b <;> simp [antipodalPosition])
    (q s).val profile₀ a v i
  change encode localBits = encode exactBits
  apply congrArg encode
  funext l
  have h := physical_data e p bin perm positive first q s a v edgeID portID y x i (laneOrder (e.net a) v l)
  exact h.trans (congrArg exactBits ((laneOrder (e.net a) v).symm_apply_apply l))

/-- The exact list of original paid-entry identifiers appears for precisely one
complete work vector. All other choices fail, regardless of the specialized scalars. -/
theorem physical_observe (g : Fin (work ws cp₀) → Bool) :
    (state₀).observe (Inherited.bits g input₀) =
      if g = canonicalWork cp₀ inc₀ e a v start₀ input₀ then
        some (List.ofFn fun i => (false,some (position (selectedEntry e a v (q s).val profile₀ i)))) else none := by
  change (born ws cp₀ inc₀ start₀ (tableFactor e position a v)).observe (Inherited.bits g input₀) = _
  rw [observe_work cp₀ inc₀ e position a v start₀ (physical_room e p bin perm positive first q s a v edgeID portID)]
  simp_rw [physical_entry e p bin perm positive first q s a v edgeID portID y x]

/-- Equality to any requested sequence identifies both the unique work and every
pre-specialization event. This form is convenient for composing observation fibers. -/
theorem physical_work_iff (g : Fin (work ws cp₀) → Bool) (obs : List (Bool × Option ℕ)) :
    (state₀).observe (Inherited.bits g input₀) = some obs ↔
      g = canonicalWork cp₀ inc₀ e a v start₀ input₀ ∧
        obs = List.ofFn fun i => (false,some (position (selectedEntry e a v (q s).val profile₀ i))) := by
  rw [physical_observe]
  by_cases h : g = canonicalWork cp₀ inc₀ e a v start₀ input₀
  · simp only [h,ite_true,Option.some.injEq,true_and,eq_comm]
  · simp [h]

/-- Summing the birth site's work gives exactly the physical list of selected paid-entry IDs,
for every additive interpretation of the sparse observation rows. -/
theorem physical_value {R : Type*} [AddCommMonoid R] (weight : List (Bool × Option ℕ) → R) :
    (state₀).value weight input₀ =
      weight (List.ofFn fun i => (false,some (position (selectedEntry e a v (q s).val profile₀ i)))) := by
  change (born ws cp₀ inc₀ start₀ (tableFactor e position a v)).value weight input₀ = _
  rw [value_born cp₀ inc₀ e position a v start₀ (physical_room e p bin perm positive first q s a v edgeID portID)]
  simp_rw [physical_entry e p bin perm positive first q s a v edgeID portID y x]

variable (values : ℕ → K) (hvals : ∀ i, values (position i) = e.entry i)

include hvals in
/-- The actual field-valued table at the inserted term site equals the full sparse-site contraction. -/
theorem physical_read : (state₀).value (fieldWeight values) input₀ =
    (G₀).read (output e p bin perm positive first q).table y x here₀ := by
  rw [physical_value,PaidPhysical.site_read]
  unfold fieldWeight
  rw [PaidPhysical.observed_sign,observed_ids,List.map_ofFn,List.prod_ofFn]
  simpa only [Bool.false_eq_true,ite_false,one_mul,Function.comp_apply] using
    Finset.prod_congr rfl fun i _ => hvals (selectedEntry e a v (q s).val profile₀ i)

include hvals in
/-- Universal persistent-table invariant at birth, suitable for the next dense save and combining round. -/
theorem models_birth : (state₀).Models G₀ edgeID portID here₀ rfl (fieldWeight values)
    (output e p bin perm positive first q).table := by
  intro z x
  let y := extendWires G₀ here₀ z
  let ports := extendPorts G₀ here₀ x
  have hz : (fun u : Incident G₀ here₀ => y u.val) = z := by
    funext u k
    simp only [y,extendWires,dite_eq_left u.property]
  have hx : (fun u : Attached G₀ here₀ => ports u.val) = x := by
    funext u k
    simp only [ports,extendPorts,dite_eq_left u.property]
  have h := physical_read e p bin perm positive first q s a v edgeID portID position y ports values hvals
  change (state₀).value (fieldWeight values)
    (inputWords G₀ edgeID portID here₀ (fun u => y u.val) (fun u => ports u.val)) =
    (output e p bin perm positive first q).table here₀ (fun u => y u.val) (fun u => ports u.val) at h
  rw [hz,hx] at h
  exact h

/-- With any injective address numbering the canonical scalar lookup realizes the
paid table directly. Addresses outside the paid table may be supplied by other gadget families. -/
theorem models_numbered (number : e.Entry ↪ ℕ) (other : ℕ → K) :
    (physical e p bin perm positive first q s a v edgeID portID number).Models G₀ edgeID portID here₀ rfl
      (fieldWeight (Function.extend number e.entry other)) (output e p bin perm positive first q).table :=
  models_birth e p bin perm positive first q s a v edgeID portID number _ (number.injective.extend_apply _ _)

end PaidSite
end Packing.Inherited

end BorderVNP
end Computability
end OAI
