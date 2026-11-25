import OAI.ThreeFlat.RAM.TraceBucketAtomValue
import OAI.ThreeFlat.RAM.TraceBucketCapacity

namespace OAI
/-! # First-stage bounds for the relay, original cells and rectangle padding -/

namespace ThreeFlat.RAM.TraceBucketAtom
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TraceSourceOwner
open scoped Fin.CommRing
variable {W b : ℕ} {s : Layout} {m : Memory W} (h : ImageCapacity s m b)
  {v : Fin 4→Word W}

theorem interval_bound {l : ℕ} (lane : (l+1)*s.lowRows≤ s.shape.rows) :
    s.pinLow l+2*s.lowRows≤2*s.shape.rows := by
  unfold Layout.pinLow
  rw [Nat.add_mul,Nat.one_mul] at lane
  omega

include h in
theorem ImageCapacity.relayBound (lane : ((v 2).val+1)*s.lowRows≤ s.shape.rows)
    (hf : (v 1).val<4) (stage : (v 3).val ≤ s.depth) (hr : (v 0).val<s.relays) :
    Diagonal.TraceBucketRelay.Bounds W (s.relayInputs (v 2).val (v 0).val (v 1).val (v 3).val) := by
  have z := h.size.trans_le h.two_power
  unfold Layout.footprint at z
  have pos : 0<s.per := Nat.mul_pos (Nat.two_pow_pos _) (Nat.mul_pos h.slots (by decide))
  have off : 0<1+(s.depth+s.depth) := by omega
  have pt := Nat.le_mul_of_pos_left s.per off
  have ext : s.pinCount (v 2).val≤2*s.lowRows := Nat.min_le_right _ _
  apply Diagonal.TraceBucketRelay.bounds_arguments
  · unfold Layout.arcs; omega
  · exact Nat.mul_pos off pos
  · exact pt
  · exact hr
  · exact hf
  · omega
  · change 2 + (if (v 3).val=0 then s.pinCount (v 2).val else 0) + 2*s.bank ≤ 2^W
    split <;> omega
  · omega
  · omega
  · omega

include h in
/-- Every source, including the table's first scalar on fourth field
selection, lies in the physical image. -/
theorem ImageCapacity.originalBound (lane : ((v 2).val+1)*s.lowRows≤ s.shape.rows) (hf : (v 1).val<4)
    (hlo : s.relays≤(v 0).val) (hhi : (v 0).val<s.relays+s.gates) :
    let i := (v 0).val-s.relays
    let a := (v 2).val*s.lowRows+i/s.slots
    let j := i%s.slots
    let n := (m (s.readAt a j (v 1).val)).val
    let u := originalInputs s (fun t => (m t).val) (v 2).val (v 0).val (v 1).val
    s.slots<2^W ∧ s.readAt a j (v 1).val<2^W ∧ (∀ l,TraceOwnerFormula.vars s.shape 1 n a l<2^b) ∧
      (∀ l, u l<2^W) ∧ u 11+(u 2 ^^^ u 3)<2^W ∧ u 12+u 5<2^W := by
  intro i a j n u
  have z := h.size
  unfold Layout.footprint at z
  have zw := h.two_power
  have x : i<s.lowRows*s.slots := by change i<s.gates; dsimp [i]; omega
  have ix := (Nat.div_lt_iff_lt_mul h.slots).2 x
  have sj : j<s.slots := Nat.mod_lt _ h.slots
  have lb : (v 2).val*s.lowRows+s.lowRows≤ s.shape.rows := by simpa [Nat.add_mul] using lane
  have site : a<s.shape.rows := by dsimp [a]; omega
  have addr := h.records site sj hf
  have small := h.smallSource site sj hf
  have home := owner_small s.shape h.ticks h.hidden site (h.sources _ _ _ site sj hf)
  have sparse := h.dictionaryEnd
  have labels := h.tableEnd
  have hmask : ownerAt s.shape 1 a n ^^^ a<s.shape.rows := by
    rw [h.rows] at site home ⊢
    exact Nat.xor_lt_two_pow home site
  have ext : s.pinCount (v 2).val≤2*s.lowRows := Nat.min_le_right _ _
  have power : 2^(s.depth-1)≤ s.shape.rows := by
    rw [h.rows]; exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have owner : ownerAt s.shape 1 a n<s.shape.rows := home
  have sn : n<2^b := small
  refine ⟨by omega,by omega,vars_small _ _ _ _ h.publicShape small (by omega),?_,?_,?_⟩
  · intro e
    fin_cases e <;>
      first
      | exact sn.trans_le zw
      | exact owner.trans (by omega)
      | exact site.trans (by omega)
      | exact sj.trans (by omega)
      | exact hf.trans (by omega)
      | exact ext.trans_lt (by omega)
      | exact power.trans_lt (by omega)
      | dsimp [u,originalInputs]; omega
  · change s.dictionary+(ownerAt s.shape 1 a n ^^^ a)<2^W
    omega
  · change s.tableIds+j<2^W
    omega

include h in
theorem ImageCapacity.holeBound (lane : ((v 2).val+1)*s.lowRows≤ s.shape.rows) (hf : (v 1).val<4)
    (hlo : s.relays+s.gates+s.tags≤(v 0).val)
    (hhi : (v 0).val<s.relays+s.gates+s.tags+s.lowRows*s.shape.stride) :
    let q := (v 0).val-(s.relays+s.gates+s.tags)
    let a := (v 2).val*s.lowRows+q/s.shape.stride
    let j := q%s.shape.stride
    s.shape.stride<2^W ∧ a<s.shape.rows ∧ j<s.shape.stride ∧
      (∀ i,TraceOwnerFormula.vars s.shape 1 a j i<2^b) ∧ s.shape.count+s.shape.rows*s.shape.stride+1≤2^b ∧
      (∀ i,holeInputs s (v 2).val (v 0).val (v 1).val i<2^W) := by
  intro q a j
  have z := h.size
  unfold Layout.footprint at z
  have zw := h.two_power
  have x : q<s.lowRows*s.shape.stride := by dsimp [q]; omega
  have ix := (Nat.div_lt_iff_lt_mul h.stride).2 x
  have hj : j<s.shape.stride := Nat.mod_lt _ h.stride
  have lb : (v 2).val*s.lowRows+s.lowRows≤ s.shape.rows := by simpa [Nat.add_mul] using lane
  have ha : a<s.shape.rows := by dsimp [a]; omega
  have ext : s.pinCount (v 2).val≤2*s.lowRows := Nat.min_le_right _ _
  refine ⟨by omega,ha,hj,vars_small _ _ _ _ h.publicShape (by omega) (by omega),h.capacity,?_⟩
  intro e
  fin_cases e <;> first
    | exact hf.trans (by omega)
    | exact ext.trans_lt (by omega)
    | exact x.trans (by omega)
    | (dsimp [holeInputs]; done)
    | dsimp [holeInputs]; omega
    | apply (Bool.toNat_le _).trans_lt; omega


end ThreeFlat.RAM.TraceBucketAtom

end OAI
