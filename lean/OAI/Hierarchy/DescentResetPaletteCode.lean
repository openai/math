import OAI.Hierarchy.DescentResetCableSlots

namespace OAI
/-! # Fixed local palette ROM for both private reset device families -/

namespace Hierarchy.DescentResetPaletteCode
open DescentContactTree DescentRotor DescentCommonHost DescentResetWireTags DescentResetHostSize
open DescentDenseHostOrder DescentContacts DescentHostDirectory
open scoped BigOperators Classical
noncomputable section

/-- Heap numbering is independent of the maximum depth declared for the local tree. -/
def heap {h : ℕ} (v : Physical.Site h) := 2^v.1.val-1+(bitWord v.1.val v.2).val

theorem heap_bounds {h : ℕ} (v : Physical.Site h) : 2^v.1.val-1≤heap v ∧ heap v<2^(v.1.val+1)-1 := by
  have fits:=(bitWord v.1.val v.2).isLt
  have pos:=Nat.two_pow_pos v.1.val
  simp only [heap,pow_succ]
  omega

def treeCell (height : ℕ) : Physical.Site height↪Fin (2^(height+1)) where
  toFun x:=⟨heap x,by
    have bound:=Nat.pow_le_pow_right (by decide : 0<2) (Nat.succ_le_succ (Nat.le_of_lt_succ x.1.isLt))
    have interval:=(heap_bounds x).2
    omega⟩
  inj':=by
    rintro ⟨i,a⟩ ⟨j,b⟩ hit
    have num : heap (⟨i,a⟩ : Physical.Site height)=heap (⟨j,b⟩ : Physical.Site height) := congrArg Fin.val hit
    have ai:=heap_bounds (⟨i,a⟩ : Physical.Site height)
    have bj:=heap_bounds (⟨j,b⟩ : Physical.Site height)
    change 2^i.val-1≤_ ∧ _<2^(i.val+1)-1 at ai
    change 2^j.val-1≤_ ∧ _<2^(j.val+1)-1 at bj
    have same : i=j := by
      apply Fin.ext
      rcases lt_trichotomy i.val j.val with h|h|h
      · have bound:=Nat.pow_le_pow_right (by decide : 0<2) h
        omega
      · exact h
      · have bound:=Nat.pow_le_pow_right (by decide : 0<2) h
        omega
    subst j
    apply congrArg (Sigma.mk i)
    apply (bitWord _).injective
    apply Fin.ext
    exact Nat.add_left_cancel num

@[simp] theorem raised_heap {h H : ℕ} (cap : h≤H) (x : Physical.Site h) :
    (treeCell H (raiseTree cap x)).val=heap x := rfl

variable {n h : ℕ} (G : NonlinearExpanders.Graph n h)
local notation "Q" => DescentCommonPalette.rotor G
local notation "Y" => (2^n:ℕ)
def rotorCell : (Q).Site↪Fin (Fintype.card (Q).Site) :=
  DescentRosterOrder.compact (dependent digit (fun _=>tagged
    (finTwoEquiv.symm.toEmbedding.trans digit) digit))

abbrev Local (r H : ℕ) := Bool × Code r × ((Q).Site ⊕ Option (Fin Y) × Physical.Site H)
local notation "bc" => Fintype.card (Computability.BorderVNP.Crossing.Network.Site (DescentCommonPalette.rotor G))
local notation "tc" => (fun H=>2^(H+1))
local notation "labels" => (fun r=>2^(r+1))
local notation "width" => (fun H=>bc+(Y+1)*tc H)

def ordinal (r H : ℕ) : Local G r H↪Fin (2*(labels r*width H)) :=
  DescentResetCableSlots.prod finTwoEquiv.symm.toEmbedding
    (DescentResetCableSlots.prod (DescentResetCableSlots.interval r)
      (DescentResetCableSlots.sum (rotorCell G) (DescentResetCableSlots.prod DescentResetCableSlots.optional (treeCell H))))

def member (r H : ℕ) (q : Local G r H) : ↥(roster G r H) :=
  ⟨render G r H (q.1,(),q.2.1,.inr q.2.2),Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩⟩

/-- Every renderable shape has a measured local rank. Padding in the static ROM reads zero. -/
def rom (r H : ℕ) (address : ℕ) : ℕ :=
  if found : ∃q : Local G r H,(ordinal G r H q).val=address
  then (localRank G r H (member G r H found.choose)).val else 0

theorem rom_read (r H : ℕ) (q : Local G r H) :
    rom G r H (ordinal G r H q).val=(localRank G r H (member G r H q)).val := by
  unfold rom
  have found : ∃q' : Local G r H,(ordinal G r H q').val=(ordinal G r H q).val:=⟨q,rfl⟩
  rw [dite_eq_left found]
  exact congrArg (fun x : Local G r H => (localRank G r H (member G r H x)).val)
    ((ordinal G r H).injective (Fin.ext found.choose_spec))

def encoder (r H : ℕ) (side label kindCell : ℕ) := kindCell+width H*(label+labels r*side)

theorem rotor_address (r H : ℕ) (s : Bool) (label : Code r) (v : (Q).Site) :
    (ordinal G r H (s,label,.inl v)).val=encoder G r H (finTwoEquiv.symm s).val
      (DescentResetCableSlots.interval r label).val (rotorCell G v).val := by
  change (rotorCell G v).val+width H*(DescentResetCableSlots.interval r label).val+
    (labels r*width H)*(finTwoEquiv.symm s).val = _
  unfold encoder
  ring

theorem tree_address {d H : ℕ} (r : ℕ) (deep : d≤H) (s : Bool) (label : Code r)
    (tag : Option (Fin Y)) (v : Physical.Site d) :
    (ordinal G r H (s,label,.inr (tag,raiseTree deep v))).val=encoder G r H (finTwoEquiv.symm s).val
      (DescentResetCableSlots.interval r label).val (bc+(heap v+tc H*(DescentResetCableSlots.optional tag).val)) := by
  change (bc+(heap v+tc H*(DescentResetCableSlots.optional tag).val))+
    width H*(DescentResetCableSlots.interval r label).val+
    (labels r*width H)*(finTwoEquiv.symm s).val = _
  unfold encoder
  ring

end
end Hierarchy.DescentResetPaletteCode

end OAI
