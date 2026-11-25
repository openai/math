import OAI.ThreeFlat.Diagonal.MotifBinaryPacking
import OAI.ThreeFlat.Diagonal.MotifDemandPadding
import OAI.ThreeFlat.Diagonal.SlotRefinement
import OAI.ThreeFlat.Diagonal.ShrinkDemands

namespace OAI
/-! # Actual bit addresses of selector fields, balanced slices and bundled demands -/

namespace ThreeFlat.Diagonal.MotifBinaryPacking

open scoped BigOperators

@[simp] theorem word_bit {n : ℕ} (x : Fin (2^n)) (i : Fin n) : (word n).symm x i = x.val.testBit i.val := rfl

/-- The `Fin 2` convention in the physical packer agrees with the Boolean
word convention in the trivalent cells, including an empty word. -/
theorem finDigit {n : ℕ} (x : Fin (2^n)) (i : Fin n) :
    (word n).symm x i = decide ((finFunctionFinEquiv.symm x i).val = 1) := by
  rw [word_bit,Nat.testBit_eq_decide_div_mod_eq]
  rfl

private theorem packed_digit {n s : ℕ} (x : Fin n → Fin (2^s)) (i : Fin n) (j : Fin s) :
    (finFunctionFinEquiv x).val.testBit (s*i.val+j.val) = (x i).val.testBit j.val := by
  have hi := congrFun (finFunctionFinEquiv.symm_apply_apply x) i
  have dig : (finFunctionFinEquiv x).val / (2^s)^i.val % (2^s) = (x i).val := congrArg Fin.val hi
  let value := (finFunctionFinEquiv x).val
  have bit : value.testBit (s*i.val+j.val) = (value / (2^s)^i.val % 2^s).testBit j.val := by
    rw [←Nat.pow_mul,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
    simp [j.isLt,Nat.add_comm]
  exact bit.trans (congrArg (fun t : ℕ => t.testBit j.val) dig)

theorem selector_payload {r s v : ℕ} (x : (Fin r → Fin (2^s)) × Fin (2^v)) (j : Fin v) :
    ((SlotRefinement.selectorWord r s v x).val).testBit j.val = (x.2.val).testBit j.val := by
  change (x.2.val + (2^v)*(finFunctionFinEquiv x.1).val).testBit j.val = _
  rw [Nat.add_comm,Nat.testBit_two_pow_mul_add _ x.2.isLt,ite_eq_left j.isLt]

theorem selector_field {r s v : ℕ} (x : (Fin r → Fin (2^s)) × Fin (2^v)) (i : Fin r) (j : Fin s) :
    ((SlotRefinement.selectorWord r s v x).val).testBit (v+(s*i.val+j.val)) = (x.1 i).val.testBit j.val := by
  change (x.2.val + (2^v)*(finFunctionFinEquiv x.1).val).testBit (v+(s*i.val+j.val)) = _
  rw [Nat.add_comm x.2.val,Nat.testBit_two_pow_mul_add _ x.2.isLt,ite_eq_right (by omega),Nat.add_sub_cancel_left,packed_digit]

/-- An old digit used as a base tile's header is either the stated old bit
or the canonical zero outside the true width. -/
theorem demand_digit {w base r : ℕ} (fit : w ≤ base*r) (x : Fin (2^w)) (i : Fin r) (j : Fin base) :
    (word base).symm (MotifDemandPadding.digits w base r fit x i) j = x.val.testBit (base*i.val+j.val) := by
  rw [word_bit,MotifDemandPadding.digits_val,←Nat.pow_mul,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
  simp [j.isLt,Nat.add_comm]

theorem split_piece {b m : ℕ} (hm : 0 < m) (w : Fin (2^b)) (i : Fin m) (j : Fin (SlotEnergy.piece b m i)) :
    (word _).symm (SlotRefinement.splitWord b m hm w i) j = (word _).symm w (SlotEnergy.pieceIndex b m hm ⟨i,j⟩) := by
  rw [finDigit,finDigit]
  apply congrArg (fun q : Fin 2 => decide (q.val=1))
  unfold SlotRefinement.splitWord
  simp only [Equiv.trans_apply,Equiv.piCongrRight_apply,Equiv.symm_apply_apply,Equiv.piCurry_apply,
    Pi.map_apply]; rfl

end ThreeFlat.Diagonal.MotifBinaryPacking

namespace ThreeFlat.Diagonal.CompressorPacking

open MotifBinaryPacking Computability.VPVNP.Compression

variable {V H Tag L : Type} {d c Q : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
  [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] (P : PackingData V H Tag L d c)
  (code : Arc V H Tag L d c ↪ ℕ) (w : Arc V H Tag L d c → ℕ)

/-- Every old AB demand bit reads one specific original arc word and bit at
its compressed owner, using the piece and bundle ordinals. -/
theorem abWord_bit (hQ : 0<Q) (v : Site V Tag L × Fin d) (i : Fin Q) (x : OldWords w)
    (j : Fin (SlotEnergy.piece (thickWidth P w v) Q i)) :
    (word _).symm (abWord P code w hQ v i x) j =
      let a := (oldBit P code w v).symm (SlotEnergy.pieceIndex _ _ hQ ⟨i,j⟩)
      (word _).symm (x a.1.val) a.2 := by
  dsimp only
  rw [finDigit,finDigit]
  unfold abWord
  rw [Equiv.symm_apply_apply]

omit [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] in
theorem cdWord_bit (m : P.Motif) (x y : OldWords w) (j : Fin (w m.val)) :
    (word _).symm (cdWord P w m x y) j =
      if P.thick (sourcePosition m.val) then (word _).symm (y m.val) j else (word _).symm (x m.val) j := by
  unfold cdWord
  split <;> rfl

end ThreeFlat.Diagonal.CompressorPacking

end OAI
