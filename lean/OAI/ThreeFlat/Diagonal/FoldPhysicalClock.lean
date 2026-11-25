import OAI.ThreeFlat.Diagonal.FoldTraceSpace
import OAI.ThreeFlat.RAM.CapacityBudget
import OAI.ThreeFlat.Diagonal.NativeTrace

namespace OAI
/-! # Public trace grid for H with its installed code and full evaluator tape -/

namespace ThreeFlat.Diagonal.FoldTrace

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalPinsExpr RAM.PhysicalPinsExpr.Program
open TraceAddressRecord

def hFuel (u A : ℕ) := total u/u^(A-146)
def hHeader (u raw : ℕ) := raw+(1+6*u+u)*(16*u^10)
def hDepth (u A raw : ℕ) := (hHeader u raw+hFuel u A).log2

theorem hHeader_fits {u A L raw : ℕ} (hu : 200000≤u) (ha : A+8≤u) (save : 146≤A)
    (hl : 1≤L) (len : L≤2^(u^6)) (inputs : raw≤7*entryFuel u A L) :
    hHeader u raw≤hFuel u A := by
  let f := entryFuel u A L
  have pos : 1≤u := by omega
  have q : 2^(u^3)≤f := (Nat.pow_le_pow_right (by decide : 0<2)
    (Nat.pow_le_pow_right pos (by decide : 3≤10))).trans (volume_le_entryFuel pos (by omega) hl)
  have text := CapacityPadding.text_add_advice_fit (by omega : 128≤u)
  have code : (1+6*u+u)*(16*u^10)≤f :=
    (Nat.le_add_right _ _).trans (text.trans q)
  have hdr : hHeader u raw≤8*f := calc
    _ ≤ 7*f+f := Nat.add_le_add inputs code
    _ = _ := by ring
  have coeff : 8≤u^146 := (by omega : 8≤u).trans (Nat.le_self_pow (by decide) u)
  apply (Nat.le_div_iff_mul_le (Nat.pow_pos pos)).mpr
  calc
    _ ≤ (8*f)*u^(A-146) := Nat.mul_le_mul_right _ hdr
    _ ≤ (u^146*f)*u^(A-146) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ coeff)
    _ = f*u^A := by rw [Nat.mul_comm (u^146) f,Nat.mul_assoc,←pow_add,Nat.add_sub_of_le save]
    _ ≤ 2^(u^3)*2^(u^10)*L := Nat.div_mul_le_self ..
    _ ≤ _ := Nat.mul_le_mul_left _ len

theorem hClock {u A raw : ℕ} (hu : 128≤u) (head : hHeader u raw≤hFuel u A) :
    let d := hDepth u A raw
    hHeader u raw+hFuel u A≤2^(1+d) ∧ 2^d≤2*hFuel u A ∧ d≤3*u^10 ∧
    hHeader u raw≤2^(16*u^10) ∧ hFuel u A≤2^(16*u^10+1) := by
  let S := hHeader u raw
  let f := hFuel u A
  have Spos : 0<S := by dsimp [S,hHeader]; positivity
  have pos : 0<S+f := by omega
  let d := hDepth u A raw
  have clock := (Nat.log2_eq_iff pos.ne').mp (show (S+f).log2=d from rfl)
  have all : f≤total u := Nat.div_le_self ..
  have lim := (evaluator_coordinate_bits (x:=2*f) (by omega : 4≤u) (by change 2*f≤64*total u; omega)).1
  have high : 2^d<2^(3*u^10) := by omega
  have depth := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp high
  have w : 2^(3*u^10)≤2^(16*u^10) := Nat.pow_le_pow_right (by decide) (by omega)
  have sf : S+f≤2*f := by change hHeader u raw+hFuel u A≤2*hFuel u A; omega
  exact ⟨by simpa [Nat.add_comm] using clock.2.le,clock.1.trans sf,depth.le,
    (show S≤2^(3*u^10) by omega).trans w,
    ((show f≤2^(3*u^10) by omega).trans w).trans (Nat.pow_le_pow_right (by decide) (by omega))⟩

/-- The leaf-image estimate needs the sum of the three true exponents,
including the team and time coordinates of the H computation. -/
theorem hDepth_sharp {u A raw : ℕ} (hu : 128≤u) (head : hHeader u raw≤hFuel u A) :
    hDepth u A raw≤u^10+u^6+u^3+1 := by
  have rows := (hClock hu head).2.1
  have bound : hFuel u A≤total u := Nat.div_le_self ..
  have lim : 2^(hDepth u A raw)≤2^(u^10+u^6+u^3+1) := calc
    _ ≤ 2*hFuel u A := rows
    _ ≤ 2*total u := Nat.mul_le_mul_left _ bound
    _ = _ := by unfold total; rw [pow_add,pow_add,pow_add,pow_one]; ring
  exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp lim

theorem hClockFits {u A raw : ℕ} (M : Machine (16*u^10) u u u)
    (hu : 128≤u) (head : hHeader u raw≤hFuel u A) :
    NativeTrace.Fits M (hHeader u raw) raw (hDepth u A raw) (hFuel u A) := by
  obtain ⟨grid,_,_,header,time⟩ := hClock hu head
  have text := CapacityPadding.textFits_scale hu
  have u10 := Nat.le_self_pow (by decide : 10≠0) u
  exact ⟨by omega,text.registers.trans (Nat.pow_le_pow_right (by decide) (by omega)),by omega,
    header,time,grid,text,le_rfl⟩

theorem image_raw {F : Type} [Field F] [Fintype F] {u A L ports rows shared : ℕ}
    (s : Shape) [NeZero s.period] (G : BitNetwork F ports)
    (input : Fin rows → Fin ports → BitSource shared (s.area+2*s.halfBits))
    (keys : Fin ports→Record) (params : Fin s.parameterBits→Bool)
    (fit : Contraction.Fits (H s (PhysicalTraceSource.expanded G input) params) (16*u^10))
    (hu : 1≤u) (ha : A+8≤u) (hl : 1≤L)
    (hb : s.halfBits≤2^(u^3)*2^(u^10)*L/u^(A+2))
    (adv : s.advice≤2^(u^3)) (par : s.parameterBits≤2^(u^3))
    (metadata : (16*u^10)*FixedTraceImage.count G≤u^151) (threshold : 151≤u) :
    (inputImage s G input keys params fit).sizes.rawCount≤7*entryFuel u A L := by
  let f := entryFuel u A L
  have half := hb.trans (block_data_le_collapse_cap ha hl).1
  have vol : 2^(u^10)≤f := volume_le_entryFuel hu (by omega) hl
  have q : 2^(u^3)≤f := (Nat.pow_le_pow_right (by decide : 0<2)
    (Nat.pow_le_pow_right hu (by decide : 3≤10))).trans vol
  have poly : u^151≤f := (width_pow_le_two_pow_sq threshold).trans
    ((Nat.pow_le_pow_right (by decide : 0<2) (Nat.pow_le_pow_right hu (by decide : 2≤10))).trans vol)
  change 2*(s.halfBits+s.halfBits)+s.advice+s.parameterBits+(16*u^10)*FixedTraceImage.count G≤7*f
  change s.halfBits≤f at half
  omega

end ThreeFlat.Diagonal.FoldTrace

end OAI
