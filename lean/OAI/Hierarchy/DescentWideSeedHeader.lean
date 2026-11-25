import OAI.Hierarchy.DescentPackedBallotHeader

namespace OAI
/-! # The machine address width and the packed seed's data width -/
namespace Hierarchy.DescentPackedSeed
open DescentSeedRoot DescentInitialHost
open ThreeFlat Routing Catalyst Diagonal TraceBanks
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory Computability.VPVNP.RAMSerialization
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p) {R s : ℕ}

def widePackedWord (h bw : ℕ) (sel : Select X R s→Bool) (i : Fin (rows X R s h)) : Word bw :=
  ((DescentSIMDLookup.data (cells X sel) ((DescentSIMDLookup.row _ _ _).symm i)).val:ℕ)

def wideBase (h bw : ℕ) (sel : Select X R s→Bool) : ℕ→Word bw :=
  joinWords (publicWord X R s bw) (widePackedWord X h bw sel)

theorem wide_public_at (h bw : ℕ) (sel : Select X R s→Bool) (i : Fin (publicWords X)) :
    initialMemory (headerWords X R s h) (wideBase X h bw sel) i.val=publicWord X R s bw i :=
  join_left _ _ i

theorem wide_shape_at (h bw : ℕ) (sel : Select X R s→Bool) (v : Shape X) (q : Fin 8) :
    initialMemory (headerWords X R s h) (wideBase X h bw sel) (shapeCell X v q).val=(shapeWords X s v q:ℕ) := by
  rw [wide_public_at]
  simp [shapeCell,publicWord]

theorem wide_site_count (h bw : ℕ) (sel : Select X R s→Bool) :
    initialMemory (headerWords X R s h) (wideBase X h bw sel) 0=(R*Fintype.card (Vertex X):ℕ) := by
  let i : Fin (publicWords X) := finSumFinEquiv
    (Sum.inl (0:Fin 6) : Fin 6 ⊕ Fin ((Fintype.card (Vertex X)+Fintype.card (Cable X))*8))
  exact (wide_public_at X h bw sel i).trans (by simp only [i,publicWord,Equiv.symm_apply_apply]; rfl)

theorem wide_data_at (h bw : ℕ) (sel : Select X R s→Bool) (a : PackedRow X R s h) :
    initialMemory (headerWords X R s h) (wideBase X h bw sel)
      (publicWords X+(DescentSIMDLookup.row _ _ _ a).val)=
      ((DescentSIMDLookup.data (cells X sel) a).val:ℕ) := by
  unfold headerWords wideBase
  exact (join_right (publicWord X R s bw) (widePackedWord X h bw sel) (DescentSIMDLookup.row _ _ _ a)).trans
    (by simp only [widePackedWord,Equiv.symm_apply_apply])

theorem wide_slot_read (h bw : ℕ) (hw : h≤bw) (sel : Select X R s→Bool) (active : 0< multiplicity h s)
    (j : Fin R) (v : Old X) (q : LocalPattern X v) :
    let rank:=finProdFinEquiv (j,code X q)
    let a:=DescentSIMDLookup.position ((Fintype.equivFin (Old X)) v) rank active
    DescentSIMDLookup.digit (digitsNeeded s) (DescentSIMDLookup.lane rank active).val
      (initialMemory (headerWords X R s h) (wideBase X h bw sel)
        (publicWords X+(DescentSIMDLookup.row _ _ _ a).val)).val=(rawCount X sel (j,⟨v,q⟩)).val := by
  intro rank a
  have small := (DescentSIMDLookup.data (cells X sel) a).isLt.trans_le
    (Nat.pow_le_pow_right (by decide) (lane_fit h s))
  have narrow:=slot_read X h sel active j v q
  change DescentSIMDLookup.digit (digitsNeeded s) (DescentSIMDLookup.lane rank active).val
    (initialMemory (headerWords X R s h) (base X h sel)
      (publicWords X+(DescentSIMDLookup.row _ _ _ a).val)).val=(rawCount X sel (j,⟨v,q⟩)).val at narrow
  rw [data_at,Fin.val_cast_of_lt small] at narrow
  rw [wide_data_at,Fin.val_cast_of_lt (small.trans_le (Nat.pow_le_pow_right (by decide) hw))]
  exact narrow

def wideShortPin (h bw : ℕ) (a : PackedRow X R s h) (i : Fin bw) : Select X R s ⊕ Bool :=
  if i.val<digitsNeeded s*multiplicity h s then
    if nz : a.2.val*multiplicity h s+i.val/digitsNeeded s<R*8 then
      cellPin X a.1 ⟨_,nz⟩ ⟨i.val%digitsNeeded s,Nat.mod_lt _ (Nat.zero_lt_succ _)⟩
    else .inr false
  else .inr false

theorem wide_short_pin (h bw : ℕ) (sel : Select X R s→Bool) (a : PackedRow X R s h) (i : Fin bw) :
    Sum.elim sel id (wideShortPin X h bw a i)=DescentSIMDLookup.sourcePin (cells X sel) a i := by
  unfold wideShortPin DescentSIMDLookup.sourcePin
  split_ifs <;> first | exact cellPin_at X sel _ _ _ | rfl

def wideDataPin (h bw : ℕ) (t : Fin (rows X R s h)×Fin (bw+1)) : Select X R s ⊕ Bool :=
  if lo : t.2.val<bw then wideShortPin X h bw ((DescentSIMDLookup.row _ _ _).symm t.1) ⟨_,lo⟩ else .inr false

theorem wide_data_pin (h bw : ℕ) (hw : h≤bw) (sel : Select X R s→Bool)
    (t : Fin (rows X R s h)×Fin (bw+1)) :
    Sum.elim sel id (wideDataPin X h bw t)=TraceWords.bits (wide (widePackedWord X h bw sel t.1)) t.2 := by
  by_cases lo : t.2.val<bw
  · rw [wideDataPin,dite_eq_left lo,wide_short_pin,←DescentSIMDLookup.source_pin (fit:=(lane_fit h s).trans hw),
      ←Computability.VPVNP.LiveHeader.testBit_wordBits]
    rfl
  · have high : (widePackedWord X h bw sel t.1).val<2^t.2.val :=
      (widePackedWord X h bw sel t.1).isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    simp [wideDataPin,lo,TraceWords.bits,wide,Nat.testBit_lt_two_pow high]

def wideHeaderPin (R s h bw : ℕ) : Fin (headerWords X R s h)×Fin (bw+1)→Select X R s ⊕ Bool :=
  joinPins (fun t : Fin (publicWords X)×Fin (bw+1)=>.inr (TraceWords.bits (wide (publicWord X R s bw t.1)) t.2))
    (wideDataPin X h bw)

theorem wide_headerPin_at (h bw : ℕ) (hw : h≤bw) (sel : Select X R s→Bool)
    (t : Fin (headerWords X R s h)×Fin (bw+1)) :
    Sum.elim sel id (wideHeaderPin X R s h bw t)=TraceWords.bits (wide (wideBase X h bw sel t.1.val)) t.2 :=
  join_agrees (Sum.elim sel id) (publicWord X R s bw) (widePackedWord X h bw sel) _ _ (fun _=>rfl) (wide_data_pin X h bw hw sel) t

theorem wide_base_self (h : ℕ) (sel : Select X R s→Bool) : wideBase X h h sel=base X h sel:=rfl
theorem wide_pin_self (h : ℕ) : wideHeaderPin X R s h h=headerPin X R s h:=rfl

/-- Bit charge when the machine words are a constant multiple of the payload budget. -/
theorem wide_startup_bits (R s h bw K : ℕ) (wide : 2*digitsNeeded s≤h) (size : bw≤K*h) :
    headerWords X R s h*bw≤K*((6+90*(X.size+1))*h+320*(X.size+1)*R*digitsNeeded s) := by
  calc
    _ ≤headerWords X R s h*(K*h):=Nat.mul_le_mul_left _ size
    _ =K*(headerWords X R s h*h):=by ring
    _ ≤_:=Nat.mul_le_mul_left K (startup_bits X R s h wide)

end
end Hierarchy.DescentPackedSeed

end OAI
