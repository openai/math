import OAI.Hierarchy.TraceResourceClock
import OAI.Hierarchy.TraceResourcePlacement

namespace OAI
/-! # A common numerical layout for either evaluator's registration passes -/
namespace Hierarchy.TraceAdmission.Resources
open TraceDistribution Filter
open scoped Topology

theorem eventual_grid_layout {u s : ℕ→ℕ} (scale : Scale u s) (A : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ (k roots dirs stages span band size charges first H dir : ℕ)
      (_axes : k=u w+1-w/2) (_positive : 0<k) (_rootsBound : roots≤k*2^k) (_dirsBound : dirs≤w)
      (_stagesBound : stages≤A*(s w+1)) (_spanBound : span≤2^(3*w)) (_bandBound : band ≤ size)
      (_sizeBound : size≤2^(32*w)),
      let β:=16*2^(32*w)
      let dp:=β+2^(16*w)
      let p:=gridRows w (2^k) roots dirs span band size charges first
      charges+2*(first+roots)≤dp → H+22≤dp → dir+44+64*stages≤dp →
      Parents.Layout (64*w) H (H+1) dp p.lanes stages (dir+44) ∧
      TraceIntervalScanner.Layout (64*w) (dp+stages*p.lanes) p.heads p.links p.lanes p.roots ∧
      Room (64*w) (H+5) (H+6) p ∧ registrationTicks H (H+5) stages p≤2^(3*w/5) ∧
      14*2^(32*w)+resourceLength p≤β := by
  have runs:=(tendsto_order.mp scale.blocks).2 1 (by norm_num)
  filter_upwards [record_room scale 1,eventual_registration_time scale A,runs,eventually_ge_atTop (A+7)]
    with w volume cost sBound hw
  intro k roots dirs stages span band size charges first H dir axes positive rr dr sr length width small β dp p
    chargeTop headerTop dirTop
  rw [←axes] at volume
  have p0 : (0:ℝ)<w := by exact_mod_cast (by omega : 0<w)
  have rounds : s w≤w := by exact_mod_cast (by simpa using ((div_lt_iff₀ p0).mp sBound).le : (s w:ℝ)≤w)
  have amount : k*2^k≤2^(3*w/5) := calc
    _ ≤ 1+k*2^k := Nat.le_add_left ..
    _ ≤ (1*(s w+1))*(1+k*2^k) := Nat.le_mul_of_pos_left _ (by positivity)
    _ ≤ (1*(s w+1))*(1+k*2^k)*(64*w+1) := Nat.le_mul_of_pos_right _ (by positivity)
    _ ≤ _ := volume
  have smallPower : 2^(3*w/5)≤2^(3*w) := Nat.pow_le_pow_right (by decide) (by omega)
  have rootMass := rr.trans (amount.trans smallPower)
  have lanes := (Nat.le_mul_of_pos_left (2^k) positive).trans (amount.trans smallPower)
  have dirBound : dirs≤2^(3*w) := dr.trans ((show w<2^w from Nat.lt_two_pow_self).le.trans
    (Nat.pow_le_pow_right (by decide) (by omega)))
  have stageArea : stages≤2^(3*w) := calc
    _ ≤ A*(s w+1) := sr
    _ ≤ 2^w*2^w := Nat.mul_le_mul (by have : w<2^w:=Nat.lt_two_pow_self;omega)
      (by have : w<2^w:=Nat.lt_two_pow_self;omega)
    _ ≤ _ := by rw [←pow_add];exact Nat.pow_le_pow_right (by decide) (by omega)
  have std:=grid_room (by omega : 7≤w) (2^k) roots dirs span band size charges first stages
    (Nat.two_pow_pos _) lanes rootMass dirBound stageArea length (width.trans small) small chargeTop
  obtain ⟨parent,linked,rows,_,_,_⟩:=std
  have gap : dp≤p.scratch := by change β+2^(16*w)≤β+4*2^(16*w);omega
  have time:=cost p stages H (H+5)
    (by change roots≤(u w+1-w/2)*2^(u w+1-w/2); rw [←axes]; exact rr)
    (by change 2^k≤2^(u w+1-w/2); rw [←axes]) dr sr
  refine ⟨⟨parent.positive,by omega,by omega,dirTop,parent.room⟩,linked,
    {rows with control:=by omega,header:=by omega},time,grid_output_end (by omega) rootMass dirBound⟩

end Hierarchy.TraceAdmission.Resources

end OAI
