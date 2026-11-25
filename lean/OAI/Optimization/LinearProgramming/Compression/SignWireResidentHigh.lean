import OAI.Optimization.LinearProgramming.Compression.SignWireResidentData
import OAI.Optimization.LinearProgramming.Compression.SignWireHighShell

/-! The persistent outer numeric state, independent of the code serving a row. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire
open RAM MinorProxyCache

def ResidentHigh {n : ℕ} (mag : ℕ → ℚ) (L : Buffers) (fuel prec C R cap base : ℕ)
    (P : ℚ → Prop) (raw : Memory ℚ) : Prop :=
  ∃ old caller, ResidentNumeric (n:=n) mag L fuel prec C R base P old caller ∧
    HighShell raw old caller cap base (n+1)

/-- Arbitrary changes outside the persistent data window and the high even
address bank preserve the resident environment, including changes to every
physical scalar and address cell below 64. -/
theorem ResidentHigh.transfer {n fuel prec C R cap base : ℕ} {mag : ℕ → ℚ} {L : Buffers}
    {P : ℚ → Prop} {raw t : Memory ℚ} (env : ResidentHigh (n:=n) mag L fuel prec C R cap base P raw)
    (data : ∀ i, 32≤ i → i≤cap → (∀ j<n+1, 2*i≠4*(base+j)+2) → t.data (2*i)=raw.data (2*i))
    (index : ∀ i, 32≤ i → t.index (2*i)=raw.index (2*i)) :
    ResidentHigh (n:=n) mag L fuel prec C R cap base P t := by
  obtain ⟨old,caller,seed,shell⟩ := env
  exact ⟨old,caller,seed,shell.transfer data index⟩

theorem ResidentHigh.ofHighFrame {n fuel prec C R cap base : ℕ} {mag : ℕ → ℚ} {L : Buffers}
    {P : ℚ → Prop} {raw t : Memory ℚ} (env : ResidentHigh (n:=n) mag L fuel prec C R cap base P raw)
    (data : ∀ i, 64≤ i → i%2=0 → t.data i=raw.data i) (even : BitRAM.StableEven raw t) :
    ResidentHigh (n:=n) mag L fuel prec C R cap base P t :=
  env.transfer (fun i hi _ _ => data (2*i) (by omega) (by omega))
    (fun i hi => even (2*i) (by omega) (by omega))

theorem ResidentHigh.ofFrame {n fuel prec C R cap base : ℕ} {mag : ℕ → ℚ} {L : Buffers}
    {P : ℚ → Prop} {raw t : Memory ℚ} (h : ResidentHigh (n:=n) mag L fuel prec C R cap base P raw)
    (data : t.data=raw.data) (even : BitRAM.StableEven raw t) :
    ResidentHigh (n:=n) mag L fuel prec C R cap base P t := by
  obtain ⟨old,caller,seed,shell⟩ := h
  exact ⟨old,caller,seed,shell.ofFrame data even⟩

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
