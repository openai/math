import OAI.Hierarchy.DescentTerminalCandidateType
import OAI.Hierarchy.DescentTerminalTraceSum

namespace OAI
/-! # A finite pool for actual active terminal bits across all graph branches -/

namespace Hierarchy.DescentTerminalPorts
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {geo : ℕ} {P : Type} {bits : P→ℕ} (N : Network geo P bits)

abbrev CableBit := (e : N.Edge) × Fin (N.width e)
theorem cableBit_card : Fintype.card (CableBit N)=∑e,N.width e := by
  simp [CableBit,Fintype.card_sigma]

/-- Prefix-address every genuinely present bit across all cables, including
narrow cables; distinct physical rows can share their last and first words. -/
def denseBits (code : N.Edge ↪ ℕ) {rows word : ℕ} (room : (∑e,N.width e)≤rows*word) :
    CableBit N ↪ RowBit rows word :=
  ((ProtocolRAMPortRanks.enumerate N.width code code.injective).toEmbedding.trans (Fin.castLEEmb room)).trans
    finProdFinEquiv.symm.toEmbedding

theorem denseBits_address (code : N.Edge ↪ ℕ) {rows word : ℕ} (room : (∑e,N.width e)≤rows*word)
    (e : N.Edge) (j : Fin (N.width e)) :
    (finProdFinEquiv (denseBits N code room ⟨e,j⟩)).val=ProtocolRAMPortRanks.prefix N.width code e+j.val := by
  simp [denseBits,ProtocolRAMPortRanks.enumerate,ProtocolRAMPortRanks.address,Nat.mod_add_div]

variable {J : Type} [Fintype J] (place : CableBit N ↪ J)

def usedBits (a : N.Assignment) : J→Bool :=
  Function.extend place (fun i : CableBit N=>a i.1 i.2) (fun _=>false)

def takeBits (pay : J→Bool) : N.Assignment := fun e j=>pay (place ⟨e,j⟩)

def ZeroUnused (pay : J→Bool) := ∀j,j∉Set.range place→pay j=false

def zeroMask (j : J) : Bool := decide (j∉Set.range place)

omit [Fintype J] in
theorem recover_used (a : N.Assignment) : takeBits N place (usedBits N place a)=a := by
  funext e j
  exact place.injective.extend_apply (fun i : CableBit N=>a i.1 i.2) (fun _=>false) ⟨e,j⟩

omit [Fintype J] in
theorem used_zero (a : N.Assignment) : ZeroUnused N place (usedBits N place a) := by
  intro j hj
  exact Function.extend_apply' _ _ _ hj

omit [Fintype J] in
theorem restore_padded (pay : J→Bool) (ok : ZeroUnused N place pay) :
    usedBits N place (takeBits N place pay)=pay := by
  funext j
  by_cases h : j∈Set.range place
  · obtain ⟨i,rfl⟩ := h
    exact place.injective.extend_apply _ _ i
  · exact (used_zero N place _ j h).trans (ok j h).symm

def poolAssignments : N.Assignment ≃ {pay : J→Bool // ZeroUnused N place pay} where
  toFun a := ⟨usedBits N place a,used_zero N place a⟩
  invFun pay := takeBits N place pay.val
  left_inv := recover_used N place
  right_inv pay := Subtype.ext (restore_padded N place pay.val pay.property)

theorem value_pool {F : Type*} [CommSemiring F] (table : N.Tables F) (x : Ports bits) :
    (∑pay:J→Bool,if ZeroUnused N place pay then ∏v,N.read table (takeBits N place pay) x v else 0)=N.value table x := by
  let f (pay : J→Bool) := ∏v,N.read table (takeBits N place pay) x v
  change (∑pay,if ZeroUnused N place pay then f pay else 0)=∑a : N.Assignment,∏v,N.read table a x v
  symm
  calc
    _ = ∑a : N.Assignment,f (usedBits N place a) := by
      simp only [f,recover_used]
    _ = ∑ pay : {pay : J→Bool // ZeroUnused N place pay}, f pay.val :=
      (poolAssignments N place).sum_comp (fun pay : {pay : J→Bool // ZeroUnused N place pay}=>f pay.val)
    _ = _ := by
      rw [←Finset.sum_subtype (Finset.univ.filter (ZeroUnused N place)) (by simp) f,Finset.sum_filter]

omit [Fintype J] in
theorem mask_ok (pay : J→Bool) :
    (∀j,zeroMask N place j=true→pay j=false) ↔ ZeroUnused N place pay := by simp [zeroMask,ZeroUnused]

end
end Hierarchy.DescentTerminalPorts

end OAI
