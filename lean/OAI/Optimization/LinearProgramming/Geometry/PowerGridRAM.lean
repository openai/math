import OAI.Optimization.LinearProgramming.RAM.Loops
import OAI.Optimization.LinearProgramming.Compression.PowerBits
import Mathlib.Algebra.Order.Floor.Ring

/-! A fixed comparison RAM program for quantizing a clipped rational on a dyadic grid. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace PowerGridRAM
open RAM

/-- Scalar 14 is the argument and address 3 is the precision. Scalar 15 is
the running lower endpoint, 16 is the interval width, 17 is one half and 18
is the most recently tested midpoint. -/
def block : Block :=
  let init := Block.seq (.op (.const 15 0)) (.seq (.op (.const 16 1)) (.op (.const 17 (1/2))))
  let step := Block.seq (.op (.mul 16 16 17)) <| .seq (.op (.add 18 15 16))
    (.branch (.scalarLT 14 18) .skip (.op (.copy 15 18)))
  let scan := Block.forRange 4 3 step
  .seq init (.branch (.scalarLT 14 15) .skip
    (.branch (.scalarLT 14 16) scan (.op (.const 15 1))))

def value (x : ℚ) (k : ℕ) : ℚ :=
  (⌊(2 : ℚ)^k * max 0 (min x 1)⌋₊ : ℚ) / 2^k

structure Frame (entry m : Memory ℚ) : Prop where
  data : ∀ i, i < 15 ∨ 18 < i → m.data i = entry.data i
  index : ∀ i, i ≠ 4 → m.index i = entry.index i

def width (H k : ℕ) : ℕ := H + 5*k + 8

private def Safe (entry : Memory ℚ) (W : ℕ) (m : Memory ℚ) : Prop :=
  (∀ i, ratBits (m.data i) ≤ W) ∧ Frame entry m

private theorem data_safe {entry m : Memory ℚ} {W i : ℕ} {q : ℚ} (hm : Safe entry W m)
    (hl : 15 ≤ i) (hu : i ≤ 18) (hq : ratBits q ≤ W) : Safe entry W (m.putData i q) := by
  constructor
  · intro j
    by_cases h : j = i
    · subst j; simpa using hq
    · simpa [Memory.putData_ne _ h] using hm.1 j
  · refine ⟨?_, hm.2.index⟩
    intro j hj
    have h : j ≠ i := by omega
    simpa [Memory.putData_ne _ h] using hm.2.data j hj

private theorem index_safe {entry m : Memory ℚ} {W : ℕ} (hm : Safe entry W m) (v : ℕ) :
    Safe entry W (m.putIndex 4 v) := by
  refine ⟨hm.1, ⟨hm.2.data, ?_⟩⟩
  intro j hj
  simpa [Memory.putIndex_ne _ hj] using hm.2.index j hj

private theorem const_eval {entry m : Memory ℚ} {W : ℕ} (hm : Safe entry W m)
    (i : ℕ) (q : ℚ) (hl : 15 ≤ i) (hu : i ≤ 18) (hq : ratBits q ≤ W) :
    Block.Eval (Safe entry W) (.op (.const i q)) m 1 (m.putData i q) :=
  .op hm (data_safe hm hl hu hq) (fun _ => rfl)

private theorem half_bits : ratBits (1/2 : ℚ) = 4 := by
  rw [one_div, Compression.ratBits_inv_eq]
  rfl

private theorem step_bits (i : ℕ) : ratBits ((1/2 : ℚ)^i) ≤ 3 + 4*i := by
  simpa only [half_bits, Nat.mul_comm i] using Compression.ratBits_natPow_le (1/2) i

private theorem dyad_bits {v i : ℕ} (hv : v < 2^i) :
    ratBits ((v : ℚ)*(1/2 : ℚ)^i) ≤ 6+5*i := by
  have hlog : v.log2 ≤ i := by
    rcases Nat.eq_zero_or_pos v with rfl | h
    · change 0 ≤ i; omega
    · exact ((Nat.log2_lt h.ne').2 hv).le
  have hnum : ratBits (v : ℚ) = 3+v.log2 := by
    simp only [ratBits, Rat.num_natCast, Int.natAbs_natCast, Rat.den_natCast,
      show Nat.log2 1 = 0 from rfl, Nat.add_zero]
  have h := Compression.ratBits_mul_le_add (v : ℚ) ((1/2 : ℚ)^i)
  rw [hnum] at h
  have hs := step_bits i
  omega

private structure Invariant (entry : Memory ℚ) (W : ℕ) (x : ℚ) (i : ℕ)
    (m : Memory ℚ) : Prop where
  safe : Safe entry W m
  index : m.index 4 = i
  half : m.data 17 = 1/2
  delta : m.data 16 = (1/2 : ℚ)^i
  cell : ∃ v : ℕ, v < 2^i ∧ m.data 15 = (v : ℚ)*(1/2 : ℚ)^i ∧
    m.data 15 ≤ x ∧ x < m.data 15 + (1/2 : ℚ)^i

private theorem scan_step {entry m : Memory ℚ} {x : ℚ} {k H i : ℕ}
    (hinput : entry.data 14 = x) (hi : i < k) (h : Invariant entry (width H k) x i m) :
    let step := Block.seq (.op (.mul 16 16 17)) <| .seq (.op (.add 18 15 16))
      (.branch (.scalarLT 14 18) .skip (.op (.copy 15 18)))
    ∃ n j, j ≤ 4 ∧ Block.Eval (Safe entry (width H k)) step m j n ∧
      Invariant entry (width H k) x (i+1) (n.putIndex 4 (n.index 4+1)) := by
  obtain ⟨v,hv,hlo,hl,hu⟩ := h.cell
  let d := (1/2 : ℚ)^(i+1)
  let mid := ((2*v+1 : ℕ) : ℚ)*d
  let m₁ := m.putData 16 d
  let m₂ := m₁.putData 18 mid
  have hd : (1/2 : ℚ)^i = 2*d := by dsimp [d]; rw [pow_succ]; ring
  have hv' : 2*v+1 < 2^(i+1) := by rw [pow_succ]; omega
  have hm : mid = m.data 15 + d := by rw [hlo,hd]; dsimp only [mid]; push_cast; ring
  have hs : ratBits d ≤ width H k := (step_bits _).trans (by unfold width; omega)
  have hb : ratBits mid ≤ width H k := (dyad_bits hv').trans (by unfold width; omega)
  have hmul : m.data 16 * m.data 17 = d := by rw [h.delta,h.half]; exact (pow_succ _ _).symm
  have e₁ : Block.Eval (Safe entry (width H k)) (.op (.mul 16 16 17)) m 1 m₁ := by
    simpa only [m₁,hmul] using
      Block.Eval.op_mul m 16 16 17 h.safe
        (data_safe h.safe (by decide : 15 ≤ 16) (by decide) (hmul ▸ hs))
  have hadd : m₁.data 15 + m₁.data 16 = mid := by simp [m₁,hm]
  have e₂ : Block.Eval (Safe entry (width H k)) (.op (.add 18 15 16)) m₁ 1 m₂ := by
    simpa only [m₂,hadd] using
      Block.Eval.op_add m₁ 18 15 16 e₁.safe_end
        (data_safe e₁.safe_end (by decide : 15 ≤ 18) (by decide) (hadd ▸ hb))
  have hin : m₂.data 14 = x := (e₂.safe_end.2.data 14 (by decide)).trans hinput
  by_cases hlt : x < mid
  · have guard : (Cond.scalarLT 14 18).test m₂ = true := by
      change decide (m₂.data 14 < m₂.data 18) = true
      rw [hin,show m₂.data 18 = mid by simp [m₂]]
      exact decide_eq_true hlt
    refine ⟨m₂,4,le_rfl, .seq e₁ (.seq e₂ (.branchTrue guard (.skip e₂.safe_end))), ?_⟩
    refine ⟨index_safe e₂.safe_end _,?_,?_,?_,⟨2*v,by omega,?_,?_,?_⟩⟩
    · simp [m₂,m₁,h.index]
    · simp [m₂,m₁,h.half]
    · simp [m₂,m₁,d]
    · simp only [Memory.putIndex_data]; change m₂.data 15 = (↑(2*v) : ℚ)*d
      rw [show m₂.data 15 = m.data 15 by simp [m₂,m₁],hlo,hd]
      push_cast
      ring
    · simpa [m₂,m₁] using hl
    · change x < m₂.data 15 + d
      simpa [m₂,m₁,hm] using hlt
  · have guard : (Cond.scalarLT 14 18).test m₂ = false := by
      change decide (m₂.data 14 < m₂.data 18) = false
      rw [hin]; simpa [m₂] using hlt
    let m₃ := m₂.putData 15 mid
    have he : m₂.data 18 = mid := by simp [m₂]
    have e₃ : Block.Eval (Safe entry (width H k)) (.op (.copy 15 18)) m₂ 1 m₃ := by
      simpa only [m₃,he] using Block.Eval.op_copy m₂ 15 18 e₂.safe_end
        (data_safe e₂.safe_end (by decide : 15 ≤ 15) (by decide) (he ▸ hb))
    refine ⟨m₃,4,le_rfl, .seq e₁ (.seq e₂ (.branchFalse guard e₃)), ?_⟩
    refine ⟨index_safe e₃.safe_end _,?_,?_,?_,⟨2*v+1,hv',?_,?_,?_⟩⟩
    · simp [m₃,m₂,m₁,h.index]
    · simp [m₃,m₂,m₁,h.half]
    · simp [m₃,m₂,m₁,d]
    · simp [m₃,mid,d]
    · simpa [m₃] using (le_of_not_gt hlt)
    · change x < m₃.data 15+d
      rw [show m₃.data 15 = mid by simp [m₃],hm]
      rw [hd] at hu
      linarith

private theorem value_of_cell {x : ℚ} {i v : ℕ} (hx : 0 ≤ x) (hx' : x < 1)
    (hl : (v : ℚ)*(1/2 : ℚ)^i ≤ x) (hu : x < (v : ℚ)*(1/2 : ℚ)^i + (1/2 : ℚ)^i) :
    value x i = (v : ℚ)*(1/2 : ℚ)^i := by
  have hp : 0 < (2 : ℚ)^i := by positivity
  have hlo : (v : ℚ)/(2:ℚ)^i ≤ x := by simpa [one_div_pow,div_eq_mul_inv] using hl
  have hhi : x < ((v : ℚ)+1)/(2:ℚ)^i := by simpa [one_div_pow,div_eq_mul_inv,add_mul] using hu
  have hf : ⌊(2 : ℚ)^i*x⌋₊ = v := by
    apply (Nat.floor_eq_iff (mul_nonneg hp.le hx)).mpr
    rw [mul_comm]
    exact ⟨(div_le_iff₀ hp).mp hlo,(lt_div_iff₀ hp).mp hhi⟩
  simp [value,min_eq_left hx'.le,max_eq_right hx,hf,div_eq_mul_inv]

/-- A uniform scalar-bound and a true instruction count for clipped quantization
at arbitrary precision. Exact dyadic ties take the upper subinterval. -/
theorem run_block (entry : Memory ℚ) (k H : ℕ) (x : ℚ) (hin : entry.data 14 = x)
    (hk : entry.index 3 = k) (hmem : ∀ i, ratBits (entry.data i) ≤ H) :
    ∃ n t, t ≤ 7*k+8 ∧
      Block.Eval (fun m => (∀ i, ratBits (m.data i) ≤ width H k) ∧ Frame entry m) block entry t n ∧
      n.data 15 = value x k := by
  let W := width H k
  have hsafe : Safe entry W entry := ⟨fun i => (hmem i).trans (by dsimp [W,width]; omega),
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩⟩
  have hz : ratBits (0 : ℚ) ≤ W := by change 3 ≤ W; dsimp [W,width]; omega
  have ho : ratBits (1 : ℚ) ≤ W := by change 3 ≤ W; dsimp [W,width]; omega
  have hh : ratBits (1/2 : ℚ) ≤ W := by rw [half_bits]; dsimp [W,width]; omega
  let m₁ := entry.putData 15 0
  let m₂ := m₁.putData 16 1
  let m₃ := m₂.putData 17 (1/2)
  have e₁ := const_eval hsafe 15 0 (by decide) (by decide) hz
  have e₂ := const_eval e₁.safe_end 16 1 (by decide) (by decide) ho
  have e₃ := const_eval e₂.safe_end 17 (1/2) (by decide) (by decide) hh
  have hm₀ : m₃.data 14 = x := (e₃.safe_end.2.data 14 (by decide)).trans hin
  have h₀ : m₃.data 15 = 0 := by simp [m₃,m₂,m₁]
  have h₁ : m₃.data 16 = 1 := by simp [m₃,m₂]
  by_cases hneg : x < 0
  · have guards : (Cond.scalarLT 14 15).test m₃ = true := by simp [Cond.test,hm₀,h₀,hneg]
    refine ⟨m₃,5,by omega,.seq (.seq e₁ (.seq e₂ e₃)) (.branchTrue guards (.skip e₃.safe_end)),?_⟩
    simp [h₀,value,min_eq_left (by linarith : x ≤ 1),max_eq_left hneg.le]
  · have hx := le_of_not_gt hneg
    have gz : (Cond.scalarLT 14 15).test m₃ = false := by simp [Cond.test,hm₀,h₀,hneg]
    by_cases hsub : x < 1
    · have gu : (Cond.scalarLT 14 16).test m₃ = true := by simp [Cond.test,hm₀,h₁,hsub]
      have hinit : Invariant entry W x 0 (m₃.putIndex 4 0) := by
        refine ⟨index_safe e₃.safe_end _,by simp,?_,?_,⟨0,by decide,?_,?_,?_⟩⟩
        · simp [m₃]
        · simpa using h₁
        · simpa using h₀
        · simpa [h₀] using hx
        · simpa [h₀] using hsub
      obtain ⟨n,j,hj,ev,hend⟩ := Block.Eval.forRange_invariant 4 3 k 4
        (Invariant entry W x) m₃ e₃.safe_end hinit
        (fun _ _ h => ⟨h.safe,h.index,(h.safe.2.index 3 (by decide)).trans hk⟩)
        (fun _ hi _ h => scan_step hin hi h)
      obtain ⟨v,_,hv,hl,hu⟩ := hend.cell
      rw [hv] at hl hu
      refine ⟨n,3+(1+(1+j+1)),by omega,.seq (.seq e₁ (.seq e₂ e₃))
        (.branchFalse gz (.branchTrue gu ev)),?_⟩
      exact hv.trans (value_of_cell hx hsub hl hu).symm
    · have gu : (Cond.scalarLT 14 16).test m₃ = false := by simp [Cond.test,hm₀,h₁,hsub]
      have fin := const_eval e₃.safe_end 15 1 (by decide) (by decide) ho
      refine ⟨m₃.putData 15 1,6,by omega,.seq (.seq e₁ (.seq e₂ e₃))
        (.branchFalse gz (.branchFalse gu fin)),?_⟩
      have hp : (2 : ℚ)^k = (↑(2^k : ℕ) : ℚ) := by norm_cast
      have hf : ⌊(2:ℚ)^k⌋₊ = 2^k := by rw [hp,Nat.floor_natCast]
      change (1:ℚ) = value x k
      rw [value,min_eq_right (le_of_not_gt hsub),max_eq_right (by decide : (0:ℚ) ≤ 1),
        mul_one,hf,← hp,div_self (by positivity : (2 : ℚ)^k ≠ 0)]

/-- Composed and halted machine trace of the quantizer. -/
theorem trace (entry : Memory ℚ) (k H : ℕ) (x : ℚ) (hin : entry.data 14 = x)
    (hk : entry.index 3 = k) (hmem : ∀ i, ratBits (entry.data i) ≤ H) :
    ∃ j ≤ 7*k+9, ∃ t : Fin (j+1) → State ℚ,
      RAM.Trace (block.compile 0 ++ [.halt 0]) (entry.atPC 0) j t ∧
      (t (Fin.last j)).output = some 0 ∧ (t (Fin.last j)).data 15 = value x k ∧
      ∀ i, scalarBound (width H k) (t i) ∧ Frame entry (t i).memory := by
  obtain ⟨n,j,hj,run,hout⟩ := run_block entry k H x hin hk hmem
  obtain ⟨t,ht,ho,hm,hs⟩ := run.halted_trace (tag := 0)
  exact ⟨j+1,by omega,t,ht,ho,(congrArg (fun m : Memory ℚ => m.data 15) hm).trans hout,hs⟩

end PowerGridRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
