import OAI.Computability.NearSquareRoot.PhysicalWalshCompileBank
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeEntry

/-! # A fixed entry command for the compiled recursive Walsh family

The recursion flag comes from the leading level ruler in the compact node
header. The same scan retains the complete input stream for every template.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile

open IntegerMultiplication Code Space Filter PhysicalWalshNode KernelPass
open GeneratorSyntax CommonRegisters PhysicalWalsh
open private dispatch dispatch_easy dispatch_wire from OAI.Computability.NearSquareRoot.PhysicalWalshNodeEntry

/-- A single scan over the physical input tags the recursive invocation. -/
noncomputable def entry : Cmd := Classical.choose (exists_scanner dispatch_easy)

private theorem entry_scan : Scans entry dispatch :=
  Classical.choose_spec (exists_scanner dispatch_easy)

theorem entry_effective {I : Type} [Primcodable I] : Effective ltr (fun _ : I => entry) :=
  effective_const ltr entry

theorem entry_registers : ∀ᶠ R in atTop, Within R entry := RegisterSelect.within_eventually _

/-- The command tags the node at any arity and input shape, with the
descriptor and every subsequent record retained. -/
theorem entry_shape {I : Type} (A : I → ℕ) (s : I → Shape) (x : (i : I) → Data (s i)) :
    ClosedRuns entry (fun i => allowance (A i) 1 (s i)) (fun i => allowance (A i) 1 (s i))
      (fun i => buffer (A i) (s i) (x i))
      (fun i => .fork (.atom (decide (0 < (s i).level))) (buffer (A i) (s i) (x i))) := by
  obtain ⟨C,run⟩ := entry_scan
  refine ⟨C*11,fun i env parked b hb => ?_⟩
  let v := (Header.wire (A i) (s i),flat (A i) (s i) (x i))
  have h := run v env parked b hb
  have sz : size v ≤ 10*(allowance (A i) 1 (s i)+1) := Header.payload_size ..
  have small : size v + 1 ≤ 11*(allowance (A i) 1 (s i)+1) := by omega
  have cap := Nat.mul_le_mul_left C small
  rw [← Nat.mul_assoc] at cap
  dsimp only [v] at h
  rw [dispatch_wire] at h
  exact h.mono cap (Nat.add_le_add_left cap _) cap

/-- Entry into the tagged recursion using the same invocation as the base and
successor commands. -/
theorem entry_closed {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W)
    (scan arena : Shape → ℕ) (cost : ∀ s, arena s ≤ scan s)
    (capacity : ∀ s, allowance (a+1) 1 s ≤ arena s) :
    let d := spec hw p scan arena cost
    ClosedRuns entry (fun t => scan (d.world t)) (fun t => arena (d.world t)) d.payload d.query := by
  intro d
  let u := fun t : Invocation hw p => t.shape
  let x := fun t : Invocation hw p => t.row
  exact (entry_shape (fun _ : Invocation hw p => a+1) u x).mono
    (fun t => (capacity (u t)).trans (cost _)) (fun t => capacity (u t))

end PhysicalWalshCompile

end NearSquareRoot
end Computability
end OAI
