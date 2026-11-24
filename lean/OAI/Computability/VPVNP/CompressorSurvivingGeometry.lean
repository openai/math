import OAI.Computability.VPVNP.CompressorSurvivingNative

/-!
# Address decoding for a surviving-subdivision visit

The quotient and remainder of the call's ordinal locate the dense motif and
its subdivision. The motif's absolute arc identifier addresses the width
table, while its dense number addresses the interval frame.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSliceSweep.SurvivingNative

open BurstRAM BurstRAM.PrivateRAM Allocation
open scoped Fin.CommRing

variable {w n A : ℕ}

/-- The three inputs needed by the surviving-row visits at one level. -/
structure Inputs (T : Allocation w n A) (abs layout : Word w) (width : Id n → ℕ)
    (mem : Memory w) : Prop where
  absolute : ∀ i : Fin n, (mem (abs.val+i.val)).val = (T.absolute i).val
  side : (mem layout.val).val = T.layout.toNat
  width : ∀ (i : Fin n) (t : Fin 4),
    (mem (T.termStart i+1)*T.selectors + mem (T.termStart i+2+(T.layout.toNat*4+t.val))).val = width (i,t)

theorem Inputs.keep {T : Allocation w n A} {abs layout : Word w} {width : Id n → ℕ}
    {mem out : Memory w} (h : Inputs T abs layout width mem) (fit : T.Fits) (visited : Id n)
    (habs : ∀ i : Fin n, (T.row visited).Outside (abs.val+i.val))
    (hlayout : (T.row visited).Outside layout.val)
    (frame : ∀ x, (T.row visited).Outside x → out x = mem x) : Inputs T abs layout width out := by
  constructor
  · intro i
    rw [frame _ (habs i)]; exact h.absolute i
  · rw [frame _ hlayout]; exact h.side
  · intro i t
    have side : T.layout.toNat ≤ 1 := by cases T.layout <;> decide
    rw [frame _ (T.termOutside fit visited i _ (by omega)),
      frame _ (T.termOutside fit visited i _ (by have := t.isLt; omega))]
    exact h.width i t

/-- The ordinal at the end of a role's rectangular scan fits the state word. -/
theorem count_fit (T : Allocation w n A) (fit : T.Fits) (t : Fin 4) :
    n*T.subdiv t < 2^w := by
  have hs : T.subdiv t ≤ T.stride :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (T.subdiv j)) (Finset.mem_univ t)
  have hr : T.stride ≤ T.recordStride := by dsimp [recordStride]; omega
  have hn : n ≤ n*4 := by omega
  calc
    n*T.subdiv t ≤ (n*4)*T.recordStride := Nat.mul_le_mul hn (hs.trans hr)
    _ ≤ T.last := Nat.le_add_left ..
    _ < _ := fit.room

variable (T : Allocation w n A) (fit : T.Fits) (abs layout : Word w)
    (width : Id n → ℕ) (mem : Memory w) (absFit : abs.val+n ≤ 2^w)
    (inputs : Inputs T abs layout width mem) (i : Fin n) (t : Fin 4) (j : Fin (T.subdiv t))

include fit absFit inputs

private theorem geometry :
    read (params T t abs layout) (↑(i.val*T.subdiv t+j.val)) mem =
      ⟨↑j.val,(T.row (i,t)).count,↑(width (i,t)),(T.row (i,t)).total,(T.row (i,t)).dst⟩ ∧
    (fun f => (readAddresses (params T t abs layout) (↑(i.val*T.subdiv t+j.val)) mem f).val) =
      ![abs.val+i.val,layout.val,T.termStart i+1,T.termStart i+2+(T.layout.toNat*4+t.val)] := by
  let q := T.subdiv t
  let p := params T t abs layout
  let c : Word w := ↑(i.val*q+j.val)
  let ix := BinaryOp.div.eval c (p 0)
  let rank := BinaryOp.mod.eval c (p 0)
  let term := p 2 + ix * p 3
  let four : Word w := 2+2
  have qpos := fit.positive t
  have fitRows := count_fit T fit t
  have hbound : i.val*q+j.val < n*q := calc
    _ < i.val*q+q := Nat.add_lt_add_left j.isLt _
    _ = (i.val+1)*q := (Nat.succ_mul ..).symm
    _ ≤ _ := Nat.mul_le_mul_right q i.isLt
  have cc : c.val = i.val*q+j.val := Nat.mod_eq_of_lt (hbound.trans fitRows)
  have qc : (p 0).val = q := (T.row_vals fit (i,t)).2.2.2.2
  have ixv : ix.val = i.val := by
    change (c.val / (p 0).val) % 2^w = _
    rw [Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt c.isLt),cc,qc,
      Nat.mul_comm i.val,Nat.mul_add_div qpos,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  have rankv : rank.val = j.val := by
    change (c.val % (p 0).val) % 2^w = _
    rw [Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt c.isLt),cc,qc,
      Nat.mul_add_mod_of_lt j.isLt]
  have ofVal (x : Word w) {v : ℕ} (hx : x.val = v) : x = ↑v := hx ▸ (Fin.cast_val_eq_self x).symm
  have ixe := ofVal ix ixv
  have rke := ofVal rank rankv
  have fourEq : four = ↑(4 : ℕ) := by norm_num [four]
  have termEq : term = ↑(T.termStart i) := by
    change (↑T.termBase : Word w) + ix * ↑T.termStride = _
    simp only [ixe,termStart,Nat.cast_add,Nat.cast_mul]
  have absRead : (p 4 + ix).val = abs.val+i.val := by
    rw [Fin.val_add,ixv,show p 4 = abs from rfl,Nat.mod_eq_of_lt (by have := i.isLt; omega)]
  have absEq := ofVal _ (inputs.absolute i)
  have layoutEq := ofVal _ inputs.side
  have roleEq : mem (p 5).val*four + p 1 = ↑(T.layout.toNat*4+t.val) := by
    rw [show p 5 = layout from rfl,layoutEq,fourEq]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    rfl
  have termFit : T.termStart i + 10 ≤ 2^w := by
    have hle : T.widthBase ≤ T.widthEnd := Nat.le_add_right ..
    have hle' : T.widthEnd ≤ T.last := Nat.le_add_right ..
    exact (T.term_stop fit i).trans (hle.trans (hle'.trans fit.room.le))
  have rep : (term+1).val = T.termStart i+1 := by
    rw [termEq,← Nat.cast_add_one,Fin.val_natCast,Nat.mod_eq_of_lt (by omega)]
  have payload : (term+2+(mem (p 5).val*four+p 1)).val = T.termStart i+2+(T.layout.toNat*4+t.val) := by
    have hs : T.layout.toNat ≤ 1 := by cases T.layout <;> decide
    have eq : term+2+(mem (p 5).val*four+p 1) = ↑(T.termStart i+2+(T.layout.toNat*4+t.val)) := by
      simp only [roleEq,termEq,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    rw [eq,Fin.val_natCast,Nat.mod_eq_of_lt (by have := t.isLt; omega)]
  have absKey : (T.absoluteKey (i,t)).val = (T.absolute i).val*4+t.val := by
    change t.val+4*(T.absolute i).val = _; omega
  have denseKey : (Allocation.denseKey (i,t)).val = i.val*4+t.val := by
    change t.val+4*i.val = _; omega
  constructor
  · change Data.mk rank (p 0) (mem (term+1).val*(p 6) + mem (term+2+(mem (p 5).val*four+p 1)).val)
      (p 9+(ix*four+p 1)*p 10) (p 7+(mem (p 4+ix).val*four+p 1)*p 8) = _
    rw [rke,rep,payload,show p 6 = T.selectors from rfl,ofVal _ (inputs.width i t),absRead,absEq,ixe,fourEq]
    congr 1
    · change (↑T.widthEnd : Word w) + (↑i.val*↑(4 : ℕ)+↑t.val)*↑T.recordStride = ↑(T.recordStart (i,t))
      simp only [recordStart,denseKey,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    · change (↑T.widthBase : Word w) + (↑(T.absolute i).val*↑(4 : ℕ)+↑t.val)*↑T.stride = ↑(T.widthStart (i,t))
      simp only [widthStart,absKey,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  · funext f
    fin_cases f
    · exact absRead
    · rfl
    · exact rep
    · exact payload

/-- Decoding one native call gives the chosen width and the two physical row
heads used in the interval representation. -/
theorem read_geometry :
    read (params T t abs layout) (↑(i.val*T.subdiv t+j.val)) mem =
      ⟨↑j.val,(T.row (i,t)).count,↑(width (i,t)),(T.row (i,t)).total,(T.row (i,t)).dst⟩ :=
  (geometry T fit abs layout width mem absFit inputs i t j).1

/-- The reads use the absolute-directory, layout, repetition and payload
addresses of the selected dense motif. -/
theorem read_addresses :
    (fun f => (readAddresses (params T t abs layout) (↑(i.val*T.subdiv t+j.val)) mem f).val) =
      ![abs.val+i.val,layout.val,T.termStart i+1,T.termStart i+2+(T.layout.toNat*4+t.val)] :=
  (geometry T fit abs layout width mem absFit inputs i t j).2

end CompressorRecords.ShrinkSliceSweep.SurvivingNative

end VPVNP
end Computability
end OAI
