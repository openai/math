import OAI.ThreeFlat.RAM.TraceBucketOriginalFits

namespace OAI
/-! # Every arithmetic operation of the first-stage generator fits its native word -/

namespace ThreeFlat.RAM.TraceBucketAtom
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TraceSourceOwner
open scoped Fin.CommRing
variable {W b : ℕ} {s : Layout} {m : Memory W} (h : ImageCapacity s m b)
  {v : Fin 4→Word W}

include h in
theorem ImageCapacity.compareBound (lane : ((v 2).val+1)*s.lowRows≤ s.shape.rows) (hf : (v 1).val<4)
    (hlo : s.relays+s.gates≤(v 0).val) (hhi : (v 0).val<s.relays+s.gates+s.tags) :
    CompareFits W b s v m := by
  let c := candidate s (fun n => (m n).val) (v 2).val (v 0).val
  have z := h.size
  unfold Layout.footprint at z
  have zw := h.two_power
  have loPos : 0<s.lowRows := Nat.two_pow_pos _
  have perPos : 0<s.per := Nat.mul_pos loPos (Nat.mul_pos h.slots (by decide))
  have xt : c.tag<s.tags := by change (v 0).val-(s.relays+s.gates)<s.tags; omega
  have xo : c.offset<1+2*s.depth := by
    have hh := (Nat.div_lt_iff_lt_mul perPos).2 xt
    change _<1+(s.depth+s.depth) at hh
    change c.tag/s.per < 1+2*s.depth
    rw [two_mul]
    exact hh
  have xs : c.slot<s.slots := Nat.mod_lt _ h.slots
  have xj : c.leg<3 := Nat.mod_lt _ (by decide)
  have xl : c.lo<s.lowRows := Nat.mod_lt _ loPos
  have lb : (v 2).val*s.lowRows+s.lowRows≤ s.shape.rows := by simpa [Nat.add_mul] using lane
  have own : c.own<s.shape.rows := by change (v 2).val*s.lowRows+c.lo<_; omega
  have mask : c.mask<s.shape.rows := h.masks _ xo
  have dest : c.dest<s.shape.rows := by
    change c.own ^^^ c.mask<s.shape.rows
    rw [h.rows] at own mask ⊢
    exact Nat.xor_lt_two_pow own mask
  have absolute := h.maskEnd
  have record := h.records dest xs (show c.leg<4 by omega)
  have value : c.source<2+s.shape.header+s.shape.count := h.sources _ _ _ dest xs (by omega)
  have home : c.home<s.shape.rows := owner_small _ h.ticks h.hidden dest value
  have hidden : c.source-(2+s.shape.header)<s.shape.count := by have := h.hidden; omega
  have located := locate_spec _ h.ticks hidden
  have klt : c.localSlot<s.lowRows*s.shape.stride :=
    pack_lt located.2.1 (Nat.mod_lt _ loPos)
  have ext : s.pinCount (v 2).val≤2*s.lowRows := Nat.min_le_right _ _
  have span := interval_bound lane
  have bit : c.mask/s.lowRows%2<2 := Nat.mod_lt _ (by decide)
  have ownerArgs := vars_small s.shape b c.source c.dest h.publicShape
    (value.trans_le (by omega)) (dest.trans_le (by omega))
  have slotArgs := vars_small s.shape b (c.source-(2+s.shape.header)) 0 h.publicShape
    (hidden.trans_le (by omega)) (Nat.two_pow_pos _)
  refine ⟨hlo,⟨by omega,by omega,by omega⟩,by omega,by omega,by change s.masks+c.offset<_; omega,
    own.trans (by omega),record,ownerArgs,slotArgs,located.1.trans (by omega),h.margin,?_⟩
  intro e
  fin_cases e <;> first
    | exact value.trans (by omega)
    | exact hf.trans (by omega)
    | exact home.trans (by omega)
    | exact own.trans (by omega)
    | exact xo.trans (by omega)
    | exact klt.trans (by omega)
    | exact ext.trans_lt (by omega)
    | exact bit.trans (by omega)
    | exact xt.trans (by omega)
    | change s.pinLow (v 2).val<_; omega
    | dsimp [cmpInputs]; omega

include h in
theorem ImageCapacity.widths (lane : ((v 2).val+1)*s.lowRows≤ s.shape.rows)
    (hf : (v 1).val<4) (stage : (v 3).val≤ s.depth)
    (row : (v 0).val<s.relays+s.gates+s.tags+s.lowRows*s.shape.stride) : Widths s v m b := by
  have hs := h.size.trans_le h.two_power
  unfold Layout.footprint at hs
  have span := interval_bound lane
  refine ⟨by omega,by omega,by omega,by omega,h.margin,h.relayBound lane hf stage,h.originalBound lane hf,
    fun a b => ⟨h.compareBound lane hf a b,by omega⟩,fun a => h.holeBound lane hf a row⟩


end ThreeFlat.RAM.TraceBucketAtom

end OAI
