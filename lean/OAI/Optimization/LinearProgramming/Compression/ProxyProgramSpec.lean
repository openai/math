import OAI.Optimization.LinearProgramming.Compression.ProxyProgramBits

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.FieldTransfer

/-- One universal coefficient for the cubic bound on every rational register. -/
def proxySizeCoefficient : ℕ :=
  let cs := 5 * 10^5
  let cr := rangeRegisterBound 1 1 * (cs+2)
  let cp := 10^23*(cr+4)
  let ch := mantissaRegisterBound 1 1 * (cp+2)^3
  cs+cr+cp+ch+10^6*(ch+4)+10*(cr+4)

theorem proxyRegisterBound_le_polyBound (B fuel k : ℕ) :
    proxyRegisterBound B fuel k ≤ polyBound proxySizeCoefficient 3 (B+fuel+k) := by
  let X := B+fuel+k+1
  let S := 10^5*(B+4)
  let R := rangeRegisterBound S fuel
  let P := 10^23*(R+4)
  let H := mantissaRegisterBound P k
  let cs := 5 * 10^5
  let cr := rangeRegisterBound 1 1 * (cs+2)
  let cp := 10^23*(cr+4)
  let ch := mantissaRegisterBound 1 1 * (cp+2)^3
  have hx : 1 ≤ X := by dsimp [X]; omega
  have hb : B ≤ X := by dsimp [X]; omega
  have hf : fuel ≤ X := by dsimp [X]; omega
  have hk : k ≤ X := by dsimp [X]; omega
  have hx3 : X ≤ X^3 := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < X) (show 1 ≤ 3 by decide)
  have hs : S ≤ cs*X := by dsimp [S,cs]; omega
  have hr : R ≤ cr*X := calc
    R ≤ rangeRegisterBound 1 1 * (S+fuel+1) := by
      simpa [polyBound,R] using rangeRegisterBound_le_polyBound S fuel
    _ ≤ rangeRegisterBound 1 1 * ((cs+2)*X) := by
      apply Nat.mul_le_mul_left
      rw [Nat.add_mul]
      omega
    _ = cr*X := by dsimp [cr]; ring
  have hp : P ≤ cp*X := calc
    P = 10^23*(R+4) := rfl
    _ ≤ 10^23*((cr+4)*X) := by
      apply Nat.mul_le_mul_left
      rw [Nat.add_mul]
      omega
    _ = cp*X := by dsimp [cp]; ring
  have hh : H ≤ ch*X^3 := calc
    H ≤ mantissaRegisterBound 1 1 * (P+k+1)^3 := mantissaRegisterBound_le_polyBound P k
    _ ≤ mantissaRegisterBound 1 1 * ((cp+2)*X)^3 := by
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      rw [Nat.add_mul]
      omega
    _ = ch*X^3 := by dsimp [ch]; rw [mul_pow]; ring
  have h1 : 1 ≤ X^3 := hx.trans hx3
  have hs' := hs.trans (Nat.mul_le_mul_left cs hx3)
  have hr' := hr.trans (Nat.mul_le_mul_left cr hx3)
  have hp' := hp.trans (Nat.mul_le_mul_left cp hx3)
  change S+R+P+H+10^6*(H+4)+10*(R+4) ≤ (cs+cr+cp+ch+10^6*(ch+4)+10*(cr+4))*X^3
  have h4 : 4 ≤ 4*X^3 := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 4 h1
  have hh4 := Nat.add_le_add hh h4
  have hr4 := Nat.add_le_add hr' h4
  rw [← Nat.add_mul] at hh4 hr4
  calc
    _ ≤ cs*X^3+cr*X^3+cp*X^3+ch*X^3+10^6*((ch+4)*X^3)+10*((cr+4)*X^3) :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hs' hr') hp') hh)
        (Nat.mul_le_mul_left _ hh4)) (Nat.mul_le_mul_left _ hr4)
    _ = _ := by simp only [Nat.add_mul,Nat.mul_assoc]

theorem standard_start_ratBits (fuel k : ℕ) (q : ℚ) :
    scalarBound (ratBits q) (start [fuel,k] [q]) := by
  intro i
  cases i with
  | zero => simp [start]
  | succ i =>
    change ratBits 0 ≤ ratBits q
    unfold ratBits
    norm_num
    rw [show Nat.log2 1 = 0 by decide]
    omega

/-- The same run supplies the correct gridded value or symbolic tag, bounded arithmetic
and control work, and a cubic bound on the binary length of every live scalar register. -/
theorem logProxyProgram_spec (fuel k : ℕ) {mag : ℚ} (hm : 0 < mag) :
    ∃ ell ≤ 16*fuel+27*k+210, ∃ t : Fin (ell+1) → State ℚ,
      Trace logProxyProgram (start [fuel,k] [mag]) ell t ∧
      (∀ i, scalarBound (polyBound proxySizeCoefficient 3 (ratBits mag+fuel+k)) (t i)) ∧
      (match logProxyNumerator fuel k mag with
       | none => (t (Fin.last _)).output = some 1
       | some u => (t (Fin.last _)).output = some 0 ∧
           (t (Fin.last _)).data 0 = (u : ℚ)/2^(k+2)) := by
  obtain ⟨ell,hell,t,ht,hout⟩ := logProxyProgram_exec fuel k hm
  refine ⟨ell,hell,t,ht,?_,hout⟩
  intro i j
  have h := logProxyProgram_scalarBound fuel k (ratBits mag) hm (start [fuel,k] [mag])
    rfl rfl (by simp [start]) (by simp [start]) (by simp [start]) (standard_start_ratBits fuel k mag)
    (runExactly_of_trace ht i)
  exact (h j).trans (proxyRegisterBound_le_polyBound ..)

end Compression
end LinearProgramming
end Optimization
end OAI
