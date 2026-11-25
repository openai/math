import OAI.Hierarchy.GridSelfHeader

namespace OAI
/-! # Room for the original input, compact network and selector at one width -/

namespace Hierarchy.GridPhysicalAdmission
open Filter

open GridScale in
theorem admission_room {Q : ℕ→ℕ} {D : ℕ→ℝ} (env : Envelopes Q D) (k A c coeff degree : ℕ)
    (hk : 0<k) :
    ∀ᶠ w : ℕ in atTop, ∀ q,0<q→q≤Q w→let a:=overhead Q D w
      let bank:=pairs A w q
      let cap:=selector k w a-1
      ∀ n≤coeff*(w+1)^degree,
        GridSelfHeader.rawSize w (external k a bank) bank n≤GridDescription.sector w ∧
        12*bank≤GridDescription.sector w ∧ cap≤GridDescription.sector w ∧ 2^(3*w/5)≤cap := by
  filter_upwards [GridSelfHeader.raw_room_of_poly env k A c coeff degree hk,
    selector_room env k A c 0 0,eventually_ge_atTop 4] with w raw selection hw
  intro q hq top a bank cap n bound
  have R:=raw q hq top n bound
  have low : 2^(4*w)≤GridDescription.sector w :=
    Nat.pow_le_pow_right (by decide) (show 4*w≤32*w by omega)
  have total := R.2.1.trans low
  have data : bank*w^2≤GridSelfHeader.rawSize w (external k a bank) bank n := by
    unfold GridSelfHeader.rawSize;omega
  have count : 1+2^(3*w/5) ≤ selector k w a := by
    simpa only [Nat.add_zero] using selection q hq top (2^(3*w/5)) 0 le_rfl (by simp)
  have cube : 12≤w^2 := by have : 4^2≤w^2 := Nat.pow_le_pow_left hw _;omega
  have tape : selector k w a≤GridDescription.sector w :=
    Nat.pow_le_pow_right (by decide) (show w-(10*k+24)*a≤32*w by omega)
  exact ⟨total,(show 12*bank≤bank*w^2 by rw [Nat.mul_comm 12];exact Nat.mul_le_mul_left bank cube).trans (data.trans total),
    (Nat.sub_le _ _).trans tape,by dsimp only [cap];omega⟩

end Hierarchy.GridPhysicalAdmission

end OAI
