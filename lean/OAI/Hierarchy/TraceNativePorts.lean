import OAI.Hierarchy.TraceNativeScale

namespace OAI
/-! # Actual machine-table port count for the native trace verifier -/

noncomputable section
namespace Hierarchy.TraceAdmission
open ThreeFlat Diagonal TraceDistribution Filter

theorem eventual_native_port_count {F : Type} [Field F] [Fintype F] {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ {pc regs words : ℕ}, pc≤64*w → regs≤64*w → words≤64*w → ∀ {k : ℕ} (_axes : k+1=u w+1-w/2)
      (M : Computability.VPVNP.BurstRAM.PrivateRAM.Machine (64*w) pc regs words) {N base fuel : ℕ}
      (fit : NativeTrace.Fits M N base ((k+1)+w/2) fuel)
      (q : Fintype.card F ≤ 2^(64*w)) (st : Computability.VPVNP.BurstRAM.Word (64*w)),
      let slots := (TraceStaticRow.gateTable q fit.width fit.labels base fuel st regs words
        ((k+1)+w/2)).cells
      let offsets := 1+(((k+1)+w/2)+((k+1)+w/2))
      offsets*slots*3 ≤ (3*5*10^26*65^14)*(w+1)^15 := by
  let a := 3*5*10^26*65^14
  have cap := (tendsto_order.mp scale.cap).2 2 (by norm_num)
  filter_upwards [cap,eventually_ge_atTop (Fintype.card F+4)] with w upper large
  intro pc regs words pcBound regBound wordBound k axes M N base fuel fit q st slots offsets
  have pos : (0:ℝ)<w := by exact_mod_cast (show 0<w by omega)
  have ub : u w ≤ 2*w := by exact_mod_cast ((div_lt_iff₀ pos).mp upper).le
  have depth : (k+1)+w/2 ≤ 2*w+1 := by omega
  have ns : slots ≤ 10^26*(64*w+1)^14 :=
    native_cells M fit q st (by omega) pcBound regBound wordBound (by omega)
  have off : offsets ≤ 5*(w+1) := by dsimp [offsets]; omega
  calc
    _ ≤ (5*(w+1))*(10^26*(65*(w+1))^14)*3 := by
        apply Nat.mul_le_mul_right
        exact Nat.mul_le_mul off (ns.trans (Nat.mul_le_mul_left _
          (Nat.pow_le_pow_left (by omega) _)))
    _ = a*(w+1)^15 := by dsimp [a]; ring

end Hierarchy.TraceAdmission

end
end OAI
