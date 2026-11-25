import OAI.ThreeFlat.Diagonal.FoldTraceFuel
import OAI.ThreeFlat.RAM.PhysicalPreparedMachine

namespace OAI
/-! # Physical addresses for the complete approximation -/

namespace ThreeFlat.Diagonal.FoldTrace

open RAM RAM.PhysicalPinsExpr RAM.PhysicalPinsExpr.Program RAM.BitLayout
variable {F : Type} [Field F] [Fintype F]

def total (u : ℕ) := 2^(u^3)*2^(u^10)*2^(u^6)

theorem blocks_charge {u A L t : ℕ} (hu : 1≤u) (save : 142≤A) (ht : (t+1)*L≤2^(u^6)) :
    (t+1)*(entryFuel u A L*u^142)≤total u := calc
  _ ≤ (t+1)*(entryFuel u A L*u^A) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hu save))
  _ ≤ (t+1)*(2^(u^3)*2^(u^10)*L) := Nat.mul_le_mul_left _ (Nat.div_mul_le_self ..)
  _ = (2^(u^3)*2^(u^10))*((t+1)*L) := by ring
  _ ≤ _ := Nat.mul_le_mul_left _ ht

/-- Each quantity is bounded in units of qVT before the public coordinate
width is chosen. The footprint includes the full finite-field product table. -/
structure SpaceBounds (u : ℕ) (s : Shape) [NeZero s.period]
    (X : BitNetwork F (s.area+2*s.halfBits)) (params : Fin s.parameterBits→Bool) : Prop where
  one : 1≤total u
  half : s.halfBits≤total u
  advice : s.advice≤total u
  parameters : s.parameterBits≤total u
  entry : X.internal+X.cells≤total u
  data : (H s X params).internal≤5*total u
  rows : (H s X params).cells≤2*total u
  footprint : BitLayout.footprint (H s X params)≤37*total u

theorem space_bounds {u A L : ℕ} (s : Shape) [NeZero s.period]
    (X : BitNetwork F (s.area+2*s.halfBits)) (params : Fin s.parameterBits→Bool)
    (hu : 200000≤u) (ha : A+8≤u) (save : 146≤A) (hl : 1≤L)
    (hn : s.inside≤L) (ht : (s.last+1)*L≤2^(u^6))
    (hb : s.halfBits≤2^(u^3)*2^(u^10)*L/u^(A+2))
    (bits : s.bits=2^(u^10-u^4)) (adv : s.advice≤2^(u^3))
    (parameters : s.parameterBits≤2^(u^3)) (card : Fintype.card F≤u)
    (trace : X.internal+X.cells≤entryFuel u A L*u^142) : SpaceBounds u s X params := by
  let cap := entryFuel u A L
  let all := total u
  have wp : 1≤u := by omega
  obtain ⟨bcap,lcap,acap,one⟩ := block_data_le_collapse_cap ha hl
  have full := blocks_charge wp (by omega : 142≤A) ht
  have cp : cap≤cap*u^142 := Nat.le_mul_of_pos_right _ (Nat.pow_pos wp)
  have bare : cap*u^142≤all := (Nat.le_mul_of_pos_left _ (Nat.succ_pos s.last)).trans full
  have ctot := cp.trans bare
  have charge (x : ℕ) (h : x≤cap*u^142) : (s.last+1)*x≤all := (Nat.mul_le_mul_left _ h).trans full
  have half : s.halfBits≤cap := hb.trans bcap
  have aux : s.bits≤cap := bits ▸ acap
  have step : s.inside*s.bits≤cap := by rw [bits]; exact (Nat.mul_le_mul_right _ hn).trans lcap
  have q : 2^(u^3)≤cap := (Nat.pow_le_pow_right (by decide : 0<2) (Nat.pow_le_pow_right wp
    (by decide : 3≤10))).trans (volume_le_entryFuel wp (by omega) hl)
  have adv' := (adv.trans q).trans ctot
  have params' := (parameters.trans q).trans ctot
  have square : Fintype.card F*Fintype.card F≤all := calc
    _ ≤ u*u := Nat.mul_le_mul card card
    _ = u^2 := by ring
    _ ≤ 2^(u^2) := width_pow_le_two_pow_sq (by omega)
    _ ≤ 2^(u^3) := Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right wp (by decide))
    _ ≤ _ := q.trans ctot
  have three : s.last*((s.halfBits+s.halfBits)+s.bits)≤3*all := calc
    _ ≤ (s.last+1)*(3*(cap*u^142)) := Nat.mul_le_mul (by omega) (by omega)
    _ = 3*((s.last+1)*(cap*u^142)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ full
  have mid := charge _ (step.trans cp)
  have xid := charge X.internal ((Nat.le_add_right X.internal X.cells).trans trace)
  have xc := charge X.cells ((Nat.le_add_left X.cells X.internal).trans trace)
  have hc := charge _ (half.trans cp)
  have ints : (H s X params).internal≤5*all := by
    change s.last*((s.halfBits+s.halfBits)+s.bits)+(s.last+1)*(s.inside*s.bits)+(s.last+1)*X.internal≤_
    omega
  have cells : (H s X params).cells≤2*all := by
    change (s.last+1)*(X.cells+s.halfBits)≤_
    rw [Nat.mul_add]
    omega
  have one' := one.trans ctot
  have half' := half.trans ctot
  have aux' := aux.trans ctot
  refine ⟨one',half',adv',params',trace.trans bare,ints,cells,?_⟩
  change 2+(s.advice+(((s.halfBits+s.halfBits)+s.bits)+((s.halfBits+s.halfBits)+s.bits)))+
    (H s X params).internal+11*(H s X params).cells+Fintype.card F*Fintype.card F≤_
  omega

theorem SpaceBounds.fits {u : ℕ} {s : Shape} [NeZero s.period]
    {X : BitNetwork F (s.area+2*s.halfBits)} {params : Fin s.parameterBits→Bool}
    (bounds : SpaceBounds u s X params) (hu : 4≤u) : Contraction.Fits (H s X params) (16*u^10) := by
  have foot := bounds.footprint
  have c := evaluator_coordinate_bits (x:=BitLayout.footprint (H s X params)) hu (by unfold total at foot; omega)
  change BitLayout.footprint (H s X params)≤_
  exact c.1.le.trans (Nat.pow_le_pow_right (by decide) (by omega))

end ThreeFlat.Diagonal.FoldTrace

end OAI
