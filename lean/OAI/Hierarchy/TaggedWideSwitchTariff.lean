import OAI.Hierarchy.TaggedWideSiteCost
import OAI.Hierarchy.TaggedWideControl
import OAI.Hierarchy.ProbeStageAddress

namespace OAI
/-! # Price of the oriented private switches and their two padded ends -/
noncomputable section
namespace Hierarchy.Tagged.WideParent
open Filter Real ProbeStage ProbeStage.Native Computability.VPVNP.BurstRAM

/-- Reported widths are bounded independently of the full address word. -/
def columnBits (cap : ℕ) := Nat.log 2 (cap+1)+1

theorem column_lt (cap : ℕ) : cap<2^(columnBits cap) :=
  (Nat.lt_succ_self cap).trans (Nat.lt_pow_succ_log_self (by decide) (cap+1))

def column {W : ℕ} (cap : ℕ) (x : Word W) : Word (columnBits cap) :=
  ⟨x.val % 2^columnBits cap,Nat.mod_lt _ (Nat.two_pow_pos _)⟩

theorem column_read {W : ℕ} (cap : ℕ) (x : Word W) (bound : x.val≤cap) :
    (column cap x).val=x.val := Nat.mod_eq_of_lt (bound.trans_lt (column_lt cap))

/-- A synchronized ROM reads address words once per private row and reads
only the certified low width word for each of its private bits. The estimate
includes both endpoint padding tables even for an empty private switch. -/
theorem checked_switch_bill {κ A : ℝ} (B K d copies : ℕ) :
    ∃ C:ℝ,0≤C ∧ ∀ᶠ x : WideParent κ A in large κ A,∀ (rows priv : ℕ),
      priv≤rows → rows≤B*2^x.h →
      let cap:=K*x.w
      let b:=columnBits cap
      let address:=wordBits x.h d copies
      ((2*priv*cap*(200*b+65)+rows*(2+2*(2*(100*address+100)+cap*(100*b+100))):ℕ):ℝ)
        ≤C*((2:ℝ)^x.h*x.w*log (x.h:ℝ)) := by
  let P:=2+(2*(rounds d+1)+3+rounds d*stride d copies)
  let L:=max 1 (logb 2 ((K+1:ℕ):ℝ)+2+A/log 2)
  let E:ℝ:=600*(K:ℝ)*L+330*(K:ℝ)+400*(P:ℝ)+402
  have lp : 0≤L:=(by norm_num : (0:ℝ)≤1).trans (le_max_left ..)
  have ep : 0≤E:=by dsimp [E];positivity
  refine ⟨(B:ℝ)*E,by positivity,?_⟩
  have heights : Tendsto (h (κ:=κ) (A:=A)) (large κ A) atTop:=tendsto_comap
  filter_upwards [heights.eventually ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1)] with x big
  change 1≤log (x.h:ℝ) at big
  intro rows priv sub volume
  dsimp only
  have hx:=x.property.1
  have hw : 0<x.w:=x.formats.2.1
  have hw1 : (1:ℝ)≤x.w:=by exact_mod_cast hw
  have hsmall : K*x.w+1≤(K+1)*x.w:=by nlinarith only [hw]
  have bits : (columnBits (K*x.w):ℝ) ≤ L*log (x.h:ℝ) := by
    have est:=site_log A (K+1) (by omega) x.h x.w (K*x.w+1) big (by change 0<x.val.1;have two:=hx.1;omega)
      hw hx.2.2 (by omega) hsmall
    have slack:=mul_le_mul_of_nonneg_right (le_max_right 1 (logb 2 ((K+1:ℕ):ℝ)+2+A/log 2))
      (by linarith : 0≤log (x.h:ℝ))
    dsimp [columnBits];push_cast;linarith
  have paidHeight : x.h≤x.w:=hx.2.1
  have addrNat : wordBits x.h d copies≤P*x.w := by
    rw [wordBits_linear]
    dsimp [P]
    have off:=Nat.mul_le_mul_left (2*(rounds d+1)+3+rounds d*stride d copies) (show 1≤x.w from hw)
    nlinarith only [paidHeight,off]
  have addr : (wordBits x.h d copies:ℝ)≤(P:ℝ)*x.w:=by exact_mod_cast addrNat
  have bill : 2*priv*(K*x.w)*(200*columnBits (K*x.w)+65)+
      rows*(2+2*(2*(100*wordBits x.h d copies+100)+K*x.w*(100*columnBits (K*x.w)+100)))≤
      (B*2^x.h)*(600*(K*x.w)*columnBits (K*x.w)+330*(K*x.w)+400*wordBits x.h d copies+402) := by
    calc
      _ ≤ 2*rows*(K*x.w)*(200*columnBits (K*x.w)+65)+
          rows*(2+2*(2*(100*wordBits x.h d copies+100)+K*x.w*(100*columnBits (K*x.w)+100))) := by gcongr
      _ = rows*(600*(K*x.w)*columnBits (K*x.w)+330*(K*x.w)+400*wordBits x.h d copies+402) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ volume
  apply (show (↑(_):ℝ)≤↑(_) from Nat.cast_le.mpr bill).trans
  push_cast
  have paid : (x.w:ℝ)≤x.w*log (x.h:ℝ):=by nlinarith only [mul_nonneg (by positivity : 0≤(x.w:ℝ)) (sub_nonneg.mpr big)]
  have localBill : 600*((K:ℝ)*x.w)*columnBits (K*x.w)+330*((K:ℝ)*x.w)+400*wordBits x.h d copies+402≤
      E*((x.w:ℝ)*log (x.h:ℝ)) := by
    dsimp [E]
    nlinarith only [mul_le_mul_of_nonneg_left bits (by positivity : 0≤600*((K:ℝ)*x.w)),
      mul_le_mul_of_nonneg_left paid (by positivity : 0≤330*(K:ℝ)),
      mul_le_mul_of_nonneg_left paid (by positivity : 0≤400*(P:ℝ)),addr,hw1,paid]
  exact (mul_le_mul_of_nonneg_left localBill (by positivity : 0≤(B:ℝ)*2^x.h)).trans_eq (by ring)

end Hierarchy.Tagged.WideParent

end
end OAI
