import OAI.Hierarchy.DescentPackedProfileWindow
import OAI.Hierarchy.DescentTerminalEpochBits
import OAI.Computability.VPVNP.RAMMemory

namespace OAI
/-! # A packed immutable dense profile tape with a final zero guard word -/
namespace Hierarchy.DescentPackedProfileTape
open DescentSIMDLookup DescentTerminalEpochBits Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory
open scoped Classical Fin.CommRing
noncomputable section
variable {A : Type} {C seats : ℕ} (pin : Pins C seats→A) (z : A→Bool)

def cell (q : ℕ) : Cell (width C) :=
  if h : q < seats then (DescentTerminalEpochBits.wordBits (width C)).symm (fun b=>z (pin (⟨q,h⟩,b))) else 0

theorem active (q : Fin seats) : (cell pin z q.val).val=raw (z∘pin) q := by
  simp only [cell,dite_eq_left q.isLt,raw,Function.comp_apply]

theorem inactive {q : ℕ} (off : seats ≤ q) : cell pin z q=0 := by simp [cell,not_lt.mpr off]

def packed (grain row : ℕ) := DescentPackedProfileWindow.word (width C) grain (cell pin z) row

def bitPin (grain row j : ℕ) : A⊕Bool :=
  if h : j < width C*grain then
    if slot : row*grain+j/width C < seats then
      .inl (pin (⟨_,slot⟩,⟨j%width C,Nat.mod_lt _ (by by_contra! no;rw [show width C=0 by omega] at h;simp at h)⟩))
    else .inr false
  else .inr false

theorem select_bit {u : ℕ} (x : Word u) (j : Fin u) :
    DescentTerminalEpochBits.wordBits u x j=x.val.testBit j.val := rfl

/-- Every bit, including high word bits, comes from one original selector pin or is false. -/
theorem bits (grain row j : ℕ) :
    (bitPin pin grain row j).elim z id=(packed pin z grain row).val.testBit j := by
  by_cases inside : j < width C*grain
  · have pos : 0 < width C := by by_contra! no;rw [show width C=0 by omega] at inside;simp at inside
    let lane : Fin grain:=⟨j/width C,(Nat.div_lt_iff_lt_mul pos).mpr (by simpa [Nat.mul_comm] using inside)⟩
    let bit : Fin (width C):=⟨j%width C,Nat.mod_lt _ pos⟩
    have address : bit.val+width C*lane.val=j := Nat.mod_add_div ..
    have sub : bit.val+width C*lane.val < width C*(lane.val+1) := by
      rw [Nat.mul_add,Nat.mul_one]
      have hb:=bit.isLt
      omega
    have h:=congrArg (fun n : ℕ=>n.testBit bit.val)
      (digit_encode (fun a : Fin grain=>cell pin z (row*grain+a.val)) lane)
    change (digit (width C) lane.val (packed pin z grain row).val).testBit bit.val=_ at h
    simp only [digit,Nat.testBit_div_two_pow,Nat.testBit_mod_two_pow,address] at h
    have under : j < width C*(lane.val+1) := address ▸ sub
    simp only [under,decide_true,Bool.true_and] at h
    rw [h]
    by_cases live : row*grain+lane.val < seats
    · change (bitPin pin grain row j).elim z id=(cell pin z _).val.testBit bit.val
      have r:=congrFun ((DescentTerminalEpochBits.wordBits (width C)).apply_symm_apply
        (fun b=>z (pin (⟨row*grain+lane.val,live⟩,b)))) bit
      change row*grain+j/width C < seats at live
      simpa only [bitPin,dite_eq_left inside,cell,lane,dite_eq_left live,Sum.elim_inl,bit,select_bit] using r.symm
    · change (bitPin pin grain row j).elim z id=(cell pin z (row*grain+lane.val)).val.testBit bit.val
      change ¬row*grain+j/width C < seats at live
      simp only [bitPin,dite_eq_left inside,cell,lane,dite_eq_right live,Sum.elim_inr,id_eq,Fin.val_zero,Nat.zero_testBit]
  · have hi : (packed pin z grain row).val < 2^j :=
      (packed pin z grain row).isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    simp [bitPin,inside,Nat.testBit_lt_two_pow hi]

def slots (seats grain : ℕ) := seats/grain+2

def memory (w base grain : ℕ) (old : Memory w) : Memory w :=
  initialMemory (base+slots seats grain) fun a=>
    if a < base then old a else ((packed pin z grain (a-base)).val:Word w)

theorem low (w base grain : ℕ) (old : Memory w) {a : ℕ} (h : a < base) :
    memory pin z w base grain old a=old a := by simp [memory,initialMemory,h,show a < base+slots seats grain by omega]

theorem at_word (w base grain : ℕ) (old : Memory w) {r : ℕ} (here : r < slots seats grain) :
    memory pin z w base grain old (base+r)=((packed pin z grain r).val:Word w) := by
  simp [memory,initialMemory,show base+r < base+slots seats grain by omega,show ¬base+r < base by omega]

/-- Padding the bank to a power of two does not introduce new selector pins. -/
theorem word_zero (grain r : ℕ) (beyond : seats ≤ r*grain) : packed pin z grain r=0 := by
  apply (encode (width C) grain).symm.injective
  funext i
  change (encode (width C) grain).symm ((encode (width C) grain) _) i=_
  rw [Equiv.symm_apply_apply,inactive pin z (by omega)]
  apply Fin.ext
  have digit_:=digit_encode ((encode (width C) grain).symm 0) i
  simpa [digit] using digit_

theorem at_any_word (w base grain r : ℕ) (old : Memory w) (pos : 0 < grain) :
    memory pin z w base grain old (base+r)=((packed pin z grain r).val:Word w) := by
  by_cases hit : r < slots seats grain
  · exact at_word pin z w base grain old hit
  · have high : seats/grain < r := by unfold slots at hit;omega
    have beyond : seats < r*grain:=(Nat.div_lt_iff_lt_mul pos).mp high
    rw [word_zero pin z grain r beyond.le]
    simp [memory,initialMemory,show ¬base+r < base+slots seats grain by omega]


theorem word_pin (w base grain : ℕ) (old : Memory w) (fits : width C*grain ≤ w)
    {r : ℕ} (here : r < slots seats grain) (j : ℕ) :
    (bitPin pin grain r j).elim z id=(memory pin z w base grain old (base+r)).val.testBit j := by
  rw [at_word pin z w base grain old here,Fin.val_cast_of_lt
    ((packed pin z grain r).isLt.trans_le (Nat.pow_le_pow_right (by decide) fits))]
  exact bits pin z grain r j

private theorem two_room (grain : ℕ) {start : ℕ} (reached : start ≤ seats) :
    start/grain+1 < slots seats grain := by
  have h:=Nat.div_le_div_right (c:=grain) reached
  unfold slots
  omega

/-- The exact two physical words read by the chunk gather, including the last
all-zero guard when the active input finishes at a word boundary. -/
theorem adjacent (w base grain start : ℕ) (old : Memory w) (reached : start ≤ seats) :
    let m:=memory pin z w base grain old
    let r:=start/grain
    m (base+r)=((packed pin z grain r).val:Word w) ∧
      m (base+(r+1))=((packed pin z grain (r+1)).val:Word w) := by
  have second:=two_room grain reached
  exact ⟨at_word pin z w base grain old (by omega),at_word pin z w base grain old second⟩

theorem slots_bound (seats grain : ℕ) : slots seats grain*grain ≤ seats+2*grain := by
  rw [slots,Nat.add_mul]
  exact Nat.add_le_add_right (Nat.div_mul_le_self ..) _

/-- Stored words yield exactly the dense selector code for each active local
row and zero for every inactive row in the physical panel. -/
theorem local_read (w base grain start U M : ℕ) (old : Memory w) (counts : Fin M→Fin (U+1))
    (reached : start ≤ seats) (fits : width C*grain ≤ w) (pos : 0 < grain) (cap : M*U ≤ grain)
    (i : Fin M) (j : Fin U) :
    let m:=memory pin z w base grain old
    let r:=start/grain
    let off : Fin grain:=⟨start%grain,Nat.mod_lt _ pos⟩
    digit (width C) (finProdFinEquiv (i,j)).val
      (DescentPackedProfileWindow.localProfile (width C) U M grain counts off
        ((m (base+r)).val:Cell (width C*grain))
        ((m (base+(r+1))).val:Cell (width C*grain))).val=
      if j.val < (counts i).val then (cell pin z (start+DescentPackedProfileWindow.localPrefix counts i+j.val)).val else 0 := by
  have words:=adjacent pin z w base grain start old reached
  have read (r : ℕ) : ((((packed pin z grain r).val:Word w)).val:Cell (width C*grain))=packed pin z grain r := by
    rw [Fin.val_cast_of_lt ((packed pin z grain r).isLt.trans_le (Nat.pow_le_pow_right (by decide) fits))]
    exact Fin.ext (Fin.val_cast_of_lt (packed pin z grain r).isLt)
  dsimp only
  rw [words.1,words.2,read,read]
  exact DescentPackedProfileWindow.window _ _ _ _ counts (cell pin z) start pos cap i j

end
end Hierarchy.DescentPackedProfileTape

end OAI
