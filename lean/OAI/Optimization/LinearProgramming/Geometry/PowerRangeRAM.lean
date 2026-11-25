import OAI.Optimization.LinearProgramming.RAM.Loops
import OAI.Optimization.LinearProgramming.Compression.PowerBits
import OAI.Optimization.LinearProgramming.PrimalDual.Bits
import Mathlib.Algebra.Order.Floor.Ring

/-! Range reduction for the rounded base-two power oracle. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace PowerRangeRAM
open RAM

/-- Scalar 0 contains θ, address 0 contains B. Scalars 8,9,10,11,12 hold
the exponent, scale, one, one half, and fractional part, respectively. -/
def block : Block :=
  let init := Block.seq (.op (.const 8 0)) <| .seq (.op (.const 9 1)) <|
    .seq (.op (.const 10 1)) (.op (.const 11 (1/2)))
  let move := Block.seq (.op (.sub 8 8 10)) (.op (.mul 9 9 11))
  let scan := Block.forRange 1 0 (.branch (.scalarLT 0 8) move .skip)
  let finish := Block.branch (.scalarLT 0 8)
    (.seq (.op (.const 9 0)) (.op (.const 12 0))) (.op (.sub 12 0 8))
  .seq init (.seq scan finish)

/-- Unrelated cells retain their entry values. -/
structure Frame (entry m : Memory ℚ) : Prop where
  data : ∀ i, i < 8 ∨ 12 < i → m.data i = entry.data i
  index : ∀ i, i ≠ 1 → m.index i = entry.index i

def width (H B : ℕ) (θ : ℚ) : ℕ := H + 2 * ratBits θ + 8 * B + 16

private def Safe (entry : Memory ℚ) (W : ℕ) (m : Memory ℚ) : Prop :=
  (∀ i, ratBits (m.data i) ≤ W) ∧ Frame entry m

private theorem data_safe {entry m : Memory ℚ} {W i : ℕ} {q : ℚ} (hm : Safe entry W m)
    (hi₀ : 8 ≤ i) (hi₁ : i ≤ 12) (hq : ratBits q ≤ W) :
    Safe entry W (m.putData i q) := by
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
    Safe entry W (m.putIndex 1 v) := by
  refine ⟨hm.1, ⟨hm.2.data, ?_⟩⟩
  intro j hj
  simpa [Memory.putIndex_ne _ hj] using hm.2.index j hj

private theorem const_eval {entry m : Memory ℚ} {W : ℕ} (hm : Safe entry W m)
    (i : ℕ) (q : ℚ) (hi₀ : 8 ≤ i) (hi₁ : i ≤ 12) (hq : ratBits q ≤ W) :
    Block.Eval (Safe entry W) (.op (.const i q)) m 1 (m.putData i q) :=
  .op hm (data_safe hm hi₀ hi₁ hq) (fun _ => rfl)

private theorem sub_eval {entry m : Memory ℚ} {W : ℕ} (hm : Safe entry W m)
    (i a b : ℕ) (q : ℚ) (hi₀ : 8 ≤ i) (hi₁ : i ≤ 12) (hq : ratBits q ≤ W)
    (heq : m.data a - m.data b = q) :
    Block.Eval (Safe entry W) (.op (.sub i a b)) m 1 (m.putData i q) := by
  subst q
  exact .op hm (data_safe hm hi₀ hi₁ hq) (fun _ => rfl)

private theorem mul_eval {entry m : Memory ℚ} {W : ℕ} (hm : Safe entry W m)
    (i a b : ℕ) (q : ℚ) (hi₀ : 8 ≤ i) (hi₁ : i ≤ 12) (hq : ratBits q ≤ W)
    (heq : m.data a * m.data b = q) :
    Block.Eval (Safe entry W) (.op (.mul i a b)) m 1 (m.putData i q) := by
  subst q
  exact .op hm (data_safe hm hi₀ hi₁ hq) (fun _ => rfl)

private theorem exponent_bits (t : ℕ) : ratBits (-(t : ℚ)) ≤ 3+t := by
  rw [PrimalDual.ratBits_neg]
  simp only [ratBits, Rat.num_natCast, Int.natAbs_natCast, Rat.den_natCast,
    show Nat.log2 1 = 0 from rfl, Nat.add_zero]
  exact Nat.add_le_add_left (Nat.log2_le_self _) _

private theorem half_bits : ratBits (1/2 : ℚ) = 4 := by
  rw [one_div, Compression.ratBits_inv_eq]
  rfl

private theorem scale_bits (t : ℕ) : ratBits ((1/2 : ℚ)^t) ≤ 3 + 4*t := by
  simpa only [half_bits, Nat.mul_comm t] using Compression.ratBits_natPow_le (1/2) t

private structure Invariant (entry : Memory ℚ) (W : ℕ) (θ : ℚ) (j : ℕ)
    (m : Memory ℚ) : Prop where
  safe : Safe entry W m
  index : m.index 1 = j
  one : m.data 10 = 1
  half : m.data 11 = 1/2
  scanned : ∃ t ≤ j, m.data 8 = -(t : ℚ) ∧ m.data 9 = (1/2 : ℚ)^t ∧
    θ < -(t : ℚ)+1 ∧ (t = j ∨ -(t : ℚ) ≤ θ)

/-- The scale is positive on reduction and set to zero on saturation. -/
structure Output (θ : ℚ) (B : ℕ) (m : Memory ℚ) : Prop where
  counter : m.index 1 = B
  saturated : θ < -(B : ℚ) → m.data 8 = -(B : ℚ) ∧ m.data 9 = 0 ∧ m.data 12 = 0
  reduced : -(B : ℚ) ≤ θ → m.data 8 = (⌊θ⌋ : ℚ) ∧
    m.data 9 = (2 : ℚ)^⌊θ⌋ ∧ m.data 12 = Int.fract θ

private theorem scan_step {entry m : Memory ℚ} {θ : ℚ} {B H j : ℕ}
    (hθ : entry.data 0 = θ) (hj : j < B)
    (h : Invariant entry (width H B θ) θ j m) :
    let move := Block.seq (.op (.sub 8 8 10)) (.op (.mul 9 9 11))
    ∃ n k, k ≤ 4 ∧ Block.Eval (Safe entry (width H B θ))
      (.branch (.scalarLT 0 8) move .skip) m k n ∧
      Invariant entry (width H B θ) θ (j+1) (n.putIndex 1 (n.index 1+1)) := by
  obtain ⟨t, ht, he, hp, hu, hdone⟩ := h.scanned
  have hin : m.data 0 = θ := (h.safe.2.data 0 (by decide)).trans hθ
  by_cases hlt : θ < -(t : ℚ)
  · have hstep : t = j := hdone.resolve_right (not_le.mpr hlt)
    subst t
    let c := -((j+1 : ℕ) : ℚ)
    let p := (1/2 : ℚ)^(j+1)
    let m₁ := m.putData 8 c
    let m₂ := m₁.putData 9 p
    have hc : ratBits c ≤ width H B θ := (exponent_bits _).trans (by unfold width; omega)
    have hpow : ratBits p ≤ width H B θ := (scale_bits _).trans (by unfold width; omega)
    have e₁ : Block.Eval (Safe entry (width H B θ)) (.op (.sub 8 8 10)) m 1 m₁ :=
      sub_eval h.safe _ _ _ _ (by decide) (by decide) hc (by rw [he,h.one]; dsimp [c]; push_cast; ring)
    have e₂ : Block.Eval (Safe entry (width H B θ)) (.op (.mul 9 9 11)) m₁ 1 m₂ :=
      mul_eval e₁.safe_end _ _ _ _ (by decide) (by decide) hpow
        (by simp [m₁, hp, h.half, p, pow_succ])
    refine ⟨m₂, 4, le_rfl, Block.Eval.branchTrue (by simp [Cond.test, hin, he, hlt]) (.seq e₁ e₂), ?_⟩
    refine ⟨index_safe e₂.safe_end _, ?_, ?_, ?_, ⟨j+1,le_rfl,?_,?_,?_,Or.inl rfl⟩⟩
    · simp [m₂,m₁,h.index]
    · simp [m₂,m₁,h.one]
    · simp [m₂,m₁,h.half]
    · simp [m₂,m₁,c]
    · simp [m₂,p]
    · push_cast; linarith
  · have hcond : (Cond.scalarLT 0 8).test m = false := by simp [Cond.test,hin,he,hlt]
    refine ⟨m,1,by decide, Block.Eval.branchFalse hcond (.skip h.safe), ?_⟩
    exact ⟨index_safe h.safe _, by simp [h.index], h.one, h.half,
      ⟨t,by omega,he,hp,hu,Or.inr (le_of_not_gt hlt)⟩⟩

/-- The entire range block has a linear time bound, including all guard and
control steps. The frame and bit invariant apply to all intermediate states. -/
theorem run_block (entry : Memory ℚ) (B H : ℕ) (θ : ℚ) (htheta : entry.data 0 = θ)
    (hB : entry.index 0 = B) (hθ : θ ≤ 0) (hmem : ∀ i, ratBits (entry.data i) ≤ H) :
    ∃ n k, k ≤ 7*B+10 ∧
      Block.Eval (fun m => (∀ i, ratBits (m.data i) ≤ width H B θ) ∧ Frame entry m) block entry k n ∧
      Output θ B n := by
  let W := width H B θ
  have hsafe : Safe entry W entry := ⟨fun i => (hmem i).trans (by dsimp [W,width]; omega),
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩⟩
  have hz : ratBits (0 : ℚ) ≤ W := by change 3 ≤ W; dsimp [W,width]; omega
  have ho : ratBits (1 : ℚ) ≤ W := by change 3 ≤ W; dsimp [W,width]; omega
  have hhalf : ratBits (1/2 : ℚ) ≤ W := by rw [half_bits]; dsimp [W,width]; omega
  let m₁ := entry.putData 8 0
  let m₂ := m₁.putData 9 1
  let m₃ := m₂.putData 10 1
  let m₄ := m₃.putData 11 (1/2)
  have e₁ := const_eval hsafe 8 0 (by decide) (by decide) hz
  have e₂ := const_eval e₁.safe_end 9 1 (by decide) (by decide) ho
  have e₃ := const_eval e₂.safe_end 10 1 (by decide) (by decide) ho
  have e₄ := const_eval e₃.safe_end 11 (1/2) (by decide) (by decide) hhalf
  have hinit : Invariant entry W θ 0 (m₄.putIndex 1 0) := by
    refine ⟨index_safe e₄.safe_end _, by simp, ?_, ?_, ⟨0,le_rfl,?_,?_,?_,Or.inl rfl⟩⟩
    · simp [m₄,m₃]
    · simp [m₄]
    · simp [m₄,m₃,m₂,m₁]
    · simp [m₄,m₃,m₂]
    · push_cast; linarith
  obtain ⟨s,k,hk,esc,hend⟩ := Block.Eval.forRange_invariant 1 0 B 4
    (Invariant entry W θ) m₄ e₄.safe_end hinit
    (fun _ s h => ⟨h.safe,h.index,(h.safe.2.index 0 (by decide)).trans hB⟩)
    (fun _ hj _ h => scan_step htheta hj h)
  obtain ⟨t,ht,he,hp,hu,hdone⟩ := hend.scanned
  have hin : s.data 0 = θ := (hend.safe.2.data 0 (by decide)).trans htheta
  by_cases hlt : θ < -(t : ℚ)
  · have htB : t = B := hdone.resolve_right (not_le.mpr hlt)
    subst t
    let s₁ := s.putData 9 0
    let s₂ := s₁.putData 12 0
    have f₁ := const_eval hend.safe 9 0 (by decide) (by decide) hz
    have f₂ := const_eval f₁.safe_end 12 0 (by decide) (by decide) hz
    have guard : (Cond.scalarLT 0 8).test s = true := by simp [Cond.test,hin,he,hlt]
    refine ⟨s₂,4+(k+4),by omega, .seq (.seq e₁ (.seq e₂ (.seq e₃ e₄))) (.seq esc
      (Block.Eval.branchTrue guard (.seq f₁ f₂))), ?_⟩
    refine ⟨hend.index, fun _ => ?_, fun hn => False.elim (hlt.not_ge hn)⟩
    simp [s₁,s₂,he]
  · have hlow : -(t : ℚ) ≤ θ := le_of_not_gt hlt
    have htB : -(B : ℚ) ≤ -(t : ℚ) := by exact_mod_cast (neg_le_neg (Int.ofNat_le.mpr ht))
    have hfloor : ⌊θ⌋ = -(t : ℤ) := Int.floor_eq_iff.mpr (by push_cast; exact ⟨hlow,hu⟩)
    have hbits : ratBits (θ - -(t : ℚ)) ≤ W :=
      (PrimalDual.ratBits_sub_le _ _).trans (by have := exponent_bits t; dsimp [W,width]; omega)
    let s₁ := s.putData 12 (θ - -(t : ℚ))
    have f := sub_eval hend.safe 12 0 8 (θ - -(t : ℚ)) (by decide) (by decide) hbits (by rw [hin,he])
    have guard : (Cond.scalarLT 0 8).test s = false := by simp [Cond.test,hin,he,hlt]
    refine ⟨s₁,4+(k+2),by omega, .seq (.seq e₁ (.seq e₂ (.seq e₃ e₄))) (.seq esc
      (Block.Eval.branchFalse guard f)), ?_⟩
    refine ⟨hend.index, fun hsat => False.elim ((htB.trans hlow).not_gt hsat), fun _ => ?_⟩
    rw [hfloor]
    simp [s₁,he,hp,Int.fract,hfloor,one_div,inv_pow]

/-- A complete assembled execution with all register states and the final halt. -/
theorem trace (entry : Memory ℚ) (B H : ℕ) (θ : ℚ) (htheta : entry.data 0 = θ)
    (hB : entry.index 0 = B) (hθ : θ ≤ 0) (hmem : ∀ i, ratBits (entry.data i) ≤ H) :
    ∃ k ≤ 7*B+11, ∃ t : Fin (k+1) → State ℚ,
      RAM.Trace (block.compile 0 ++ [.halt 0]) (entry.atPC 0) k t ∧
      (t (Fin.last k)).output = some 0 ∧ Output θ B (t (Fin.last k)).memory ∧
      ∀ i, scalarBound (width H B θ) (t i) ∧ Frame entry (t i).memory := by
  obtain ⟨n,k,hk,run,hout⟩ := run_block entry B H θ htheta hB hθ hmem
  obtain ⟨t,ht,ho,hm,hs⟩ := run.halted_trace (tag := 0)
  exact ⟨k+1,by omega,t,ht,ho,hm ▸ hout,hs⟩


/-- The zero scale is an executable test for the saturated branch. -/
theorem Output.zero_scale_iff {θ : ℚ} {B : ℕ} {m : Memory ℚ} (h : Output θ B m) :
    m.data 9 = 0 ↔ θ < -(B : ℚ) := by
  constructor
  · intro hzero
    by_contra! hlo
    have hpos := (h.reduced hlo).2.1
    rw [hzero] at hpos
    exact (zpow_pos (by decide : (0 : ℚ) < 2) ⌊θ⌋).ne' hpos.symm
  · exact fun hlt => (h.saturated hlt).2.1

/-- Standalone input convention: one dimension parameter and one scalar. The
output includes the terminal state, and the register bound now involves only
the supplied parameter and the binary size of the supplied scalar. -/
theorem input_trace (B : ℕ) (θ : ℚ) (hθ : θ ≤ 0) :
    ∃ k ≤ 7*B+11, ∃ t : Fin (k+1) → State ℚ,
      RAM.Trace (block.compile 0 ++ [.halt 0]) (start [B] [θ]) k t ∧
      (t (Fin.last k)).output = some 0 ∧ Output θ B (t (Fin.last k)).memory ∧
      ∀ i, scalarBound (width (ratBits θ) B θ) (t i) ∧
        Frame (start [B] [θ]).memory (t i).memory := by
  let m := (start [B] [θ]).memory
  have hi (j : ℕ) : ratBits (m.data j) ≤ ratBits θ := by
    cases j with
    | zero => exact le_rfl
    | succ j =>
      have hz : m.data (j+1) = 0 := by simp [m, State.memory, start]
      rw [hz]
      change 3 ≤ 3+_+_
      omega
  exact trace m B (ratBits θ) θ rfl rfl hθ hi

end PowerRangeRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
