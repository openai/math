import OAI.ThreeFlat.Diagonal.TraceStaticSourceOwner
import OAI.ThreeFlat.Diagonal.TraceBucketReverse
import OAI.ThreeFlat.Diagonal.LaneBucketAddresses
import OAI.ThreeFlat.BitNetwork.RectangularHidden

namespace OAI
/-! # Physical hidden reservations and pin ordinals of the compressed bit-header trace -/

namespace ThreeFlat.Diagonal.TraceSourceOwner

open Computability.VPVNP BurstRAM LaneCursor
variable {F : Type*} [CommRing F] [Fintype F] {w p S f lane low : ℕ}
variable (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k : ℕ)
    (fit : S+f ≤ 2^(1+(lane+low)))

set_option quotPrecheck false
local notation "dsc" => shape w p r k S f (lane+low) (TraceStaticRow.gateTable hF hw hp base f st r k (lane+low)).internal
local notation "site" => TraceBitHeader.layout hF hw hp base st hs hf r k fit
local notation "net" => TraceBitHeader.network hF hw hp base st hs hf r k (lane+low)

theorem bitHidden_eq (i : Fin (net).internal) : ((site).hiddenRow i).val = (locate dsc i.val).1 :=
  layout_hidden hF hw hp base st hs hf r k fit i

theorem bitSource (v : Row lane low) (z : BitSource (net).internal S) :
    (sourceRow (site).hiddenRow (site).pinRow v z).val = ownerAt dsc 1 v.val (RAM.BitLayout.sourceAddress z) := by
  cases z with
  | constant b => cases b <;> simp [sourceRow,RAM.BitLayout.sourceAddress,ownerAt,appendAt]
  | pin j =>
    rw [sourceRow,TraceBitHeader.layout_pin]
    simp [ownerAt,shape,RAM.BitLayout.sourceAddress]
  | hidden i =>
    rw [sourceRow,bitHidden_eq]
    simp [ownerAt,shape,RAM.BitLayout.sourceAddress,RAM.BitLayout.hiddenBase,Nat.add_assoc]

theorem bitPin_lane (L : Lane lane) (j : Fin S) :
    (splitRow _ _ ((site).pinRow j)).1=L ↔ j.val/pinSpan 1 low=(finFunctionFinEquiv L).val := by
  rw [lane_eq_iff,TraceBitHeader.layout_pin]
  simp [pinSpan,Nat.div_div_eq_div_mul]

noncomputable def bitExt (L : Lane lane) : Fin (pinCount S 1 low (finFunctionFinEquiv L).val) ≃
    {j : Fin S // (splitRow _ _ ((site).pinRow j)).1=L} :=
  (pinFiber S 1 low _).trans {
    toFun := fun j => ⟨j.val.cast (Nat.mul_one S),
      (bitPin_lane hF hw hp base st hs hf r k fit L _).2 j.property⟩
    invFun := fun j => ⟨j.val.cast (Nat.mul_one S).symm,
      (bitPin_lane hF hw hp base st hs hf r k fit L _).1 j.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem bitExt_apply_val (L : Lane lane) (i : Fin (pinCount S 1 low (finFunctionFinEquiv L).val)) :
    ((bitExt hF hw hp base st hs hf r k fit L i).val).val =
      (finFunctionFinEquiv L).val*pinSpan 1 low+i.val := rfl

theorem bitExt_symm_val (L : Lane lane) (j : {i : Fin S // (splitRow _ _ ((site).pinRow i)).1=L}) :
    ((bitExt hF hw hp base st hs hf r k fit L).symm j).val =
      j.val.val-(finFunctionFinEquiv L).val*pinSpan 1 low := by
  change j.val.val%pinSpan 1 low=_
  have h := Nat.div_add_mod j.val.val (pinSpan 1 low)
  rw [(bitPin_lane hF hw hp base st hs hf r k fit L j.val).1 j.property,Nat.mul_comm] at h
  omega

theorem bitHidden_lane (L : Lane lane) (i : Fin (net).internal) :
    (splitRow _ _ ((site).hiddenRow i)).1=L ↔ (locate dsc i.val).1/2^low=(finFunctionFinEquiv L).val := by
  rw [lane_eq_iff,bitHidden_eq]

/-- The compact ordinal only appears inside proofs. Its public physical address
is the arithmetic value in the containing lane's rectangular bank. -/
noncomputable def bitHidden (L : Lane lane) :
    {i : Fin (net).internal // (splitRow _ _ ((site).hiddenRow i)).1=L} ↪ Fin (2^low*(dsc).stride) :=
  staticHidden hF hw hp base st hs hf r k fit L

theorem bitHidden_val (L : Lane lane) (x : {i : Fin (net).internal // (splitRow _ _ ((site).hiddenRow i)).1=L}) :
    (bitHidden hF hw hp base st hs hf r k fit L x).val = laneHiddenSlot dsc low x.val.val := rfl

private noncomputable def addressOf {u V : ℕ} (e : Fin u ↪ Fin V) : BitNetwork.Rectangular.Address u V where
  put := e
  get := fun j => if hit : ∃ x,e x=j then some hit.choose else none
  get_put x := by
    split
    · rename_i hit
      exact congrArg some (e.injective hit.choose_spec)
    · rename_i miss
      exact (miss ⟨x,rfl⟩).elim
  put_get j x h := by
    split at h
    · rename_i hit
      obtain rfl := Option.some.inj h
      exact hit.choose_spec
    · cases h

private theorem addressOf_get_none {u V : ℕ} (e : Fin u ↪ Fin V) (j : Fin V) :
    (addressOf e).get j = none ↔ ¬∃ x,e x=j := by
  classical
  simp [addressOf]

section Buckets

variable {q : ℕ} (fitB : S+f ≤ 2^(1+((q+1)+low)))
local notation "D" => shape w p r k S f ((q+1)+low) (TraceStaticRow.gateTable hF hw hp base f st r k ((q+1)+low)).internal
local notation "P" => TraceBitHeader.layout hF hw hp base st hs hf r k fitB
local notation "N" => TraceBitHeader.network hF hw hp base st hs hf r k ((q+1)+low)

noncomputable def bitIndex (L : Lane (q+1)) : (P).BucketIndex L :=
  (P).initialIndex (TraceBitHeader.rectangular hF hw hp base st hs hf r k fitB) L
    (Fintype.equivFin _).symm (bitExt hF hw hp base st hs hf r k fitB L)

noncomputable def bitAddress (L : Lane (q+1)) (I : (P).BucketIndex L) :
    BitNetwork.Rectangular.Address I.h (2^low*(D).stride) :=
  addressOf (I.hidden.toEmbedding.trans (bitHidden hF hw hp base st hs hf r k fitB L))

theorem bitAddress_put (L : Lane (q+1)) (I : (P).BucketIndex L) (x : Fin I.h) :
    ((bitAddress hF hw hp base st hs hf r k fitB L I).put x).val =
      laneHiddenSlot D low (I.hidden x).val.val := rfl

theorem bitHiddenCount_le (L : Lane (q+1)) (I : (P).BucketIndex L) : I.h ≤ 2^low*(D).stride := by
  let e := I.hidden.toEmbedding.trans (bitHidden hF hw hp base st hs hf r k fitB L)
  simpa using Fintype.card_le_of_injective e e.injective

theorem bitIndex_pinCount (L : Lane (q+1)) :
    (bitIndex hF hw hp base st hs hf r k fitB L).x=pinCount S 1 low (finFunctionFinEquiv L).val := rfl

theorem bitAddress_get_none (L : Lane (q+1)) (I : (P).BucketIndex L) (j : Fin (2^low*(D).stride)) :
    (bitAddress hF hw hp base st hs hf r k fitB L I).get j=none ↔
      decodeLane D low (finFunctionFinEquiv L).val j.val=none := by
  let ln := (finFunctionFinEquiv L).val
  have grid : (D).header+(D).ticks ≤ 2*(D).rows := by simpa [shape,pow_add] using fitB
  have count : (N).internal = (D).count := hidden_count hF hw hp base st hs hf r k
  rw [bitAddress,addressOf_get_none]
  constructor
  · intro miss
    cases hit : decodeLane D low ln j.val with
    | none => first | rfl
    | some h =>
      obtain ⟨hi,own,pos⟩ := (decodeLane_some_iff D grid low ln j.val h j.isLt).1 hit
      let x : Fin (N).internal := ⟨h,by omega⟩
      let y : {i : Fin (N).internal // (splitRow _ _ ((P).hiddenRow i)).1=L} :=
        ⟨x,(bitHidden_lane hF hw hp base st hs hf r k fitB L x).2 own⟩
      apply False.elim (miss ?_)
      refine ⟨I.hidden.symm y,Fin.ext ?_⟩
      change laneHiddenSlot D low (I.hidden (I.hidden.symm y)).val.val = j.val
      rw [I.hidden.apply_symm_apply]
      exact pos
  · rintro miss ⟨x,hx⟩
    have pos := congrArg Fin.val hx
    change laneHiddenSlot D low (I.hidden x).val.val=j.val at pos
    have own := (bitHidden_lane hF hw hp base st hs hf r k fitB L (I.hidden x).val).1 (I.hidden x).property
    have hi := (I.hidden x).val.isLt.trans_le count.le
    have hit := (decodeLane_some_iff D grid low ln j.val _ j.isLt).2 ⟨hi,own,pos⟩
    rw [miss] at hit
    cases hit

end Buckets
end ThreeFlat.Diagonal.TraceSourceOwner

end OAI
