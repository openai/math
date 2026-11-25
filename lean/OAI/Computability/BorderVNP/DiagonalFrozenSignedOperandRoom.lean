import OAI.Computability.BorderVNP.DiagonalJointSeedStorage
import OAI.Computability.BorderVNP.PackedFrozenSeedExecute
import OAI.Computability.BorderVNP.PackedHistoryScheduleBudget
import OAI.Computability.BorderVNP.PackedBankCompiledScalars
import OAI.Computability.BorderVNP.PackedTerminalBoxWordFits

/-! # Room for the relocated operands and paid literals in the selected signed packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.FinalReports.Spare

/-- The absent spare reports and every live count vector have their native
length words at the chosen report precision, even for zero precision. -/
theorem packet_lengths {C g digits w : ℕ} {E : Type} (gfits : g < 2^w) (dfits : digits < 2^w) :
    (∀ c, (reports (C:=C) (g:=g) (digits:=digits) (E:=E) c).length < 2^w) ∧
    ∀ c r, r ∈ reports (C:=C) (g:=g) (digits:=digits) (E:=E) c → r.length < 2^w := by
  constructor
  · intro c
    refine Fin.lastCases ?_ (fun i => ?_) c
    · simp [reports]
    · simpa [reports,countPins] using gfits
  · intro c
    refine Fin.lastCases ?_ (fun i => ?_) c
    · simp [reports]
    · rintro r hr
      simp only [reports,Fin.lastCases_castSucc,List.mem_map] at hr
      obtain ⟨xs,member,rfl⟩ := hr
      obtain ⟨_,rfl⟩ := List.mem_ofFn.mp member
      simpa only [List.length_map,List.length_ofFn] using dfits

end Packing.FinalReports.Spare

namespace Diagonal

open Filter Cover Crossing Epoch TeamScales Packing Inherited DeckGrid InheritedBank Shortening.PublicCapacity
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open scoped Classical BorderVNP.Epoch.Cube

set_option maxHeartbeats 1200000
set_option maxRecDepth 6000

private theorem relocated_room {n r sites mass birth coefficient : ℕ} (hn : 15 ≤ n) (hr : 1 ≤ r)
    (hs : sites ≤ r*n) (hm : mass ≤ n) (hb : birth ≤ n) (hc : coefficient ≤ n) :
    max (15*mass) sites + max (max birth (coefficient*(mass+1))) (max 1 (15*mass))+1 < 2^(60*logWidth r n) := by
  let h := 2^(logWidth r n)
  have two : 2*n*r ≤ h := by
    dsimp only [h]
    rw [public_logWidth]
    exact Nat.le_pow_clog (by decide) _
  have rn : r*n ≤ h := (show r*n≤2*n*r by nlinarith only).trans two
  have nh : n ≤ h := (Nat.le_mul_of_pos_left n hr).trans rn
  have hh : 2 ≤ h := by omega
  have H1 : 15*mass ≤ h*h := Nat.mul_le_mul (hn.trans nh) (hm.trans nh)
  have H2 : coefficient*(mass+1) ≤ h*h+h := (Nat.mul_le_mul (hc.trans nh) (Nat.add_le_add_right (hm.trans nh) 1)).trans_eq (Nat.mul_succ _ _)
  have H3 : h ≤ h*h := Nat.le_mul_of_pos_left h (by omega)
  have H4 : max (15*mass) sites ≤ h*h := max_le H1 (hs.trans (rn.trans H3))
  have H5 : max (max birth (coefficient*(mass+1))) (max 1 (15*mass)) ≤ h*h+h :=
    max_le (max_le ((hb.trans nh).trans (Nat.le_add_left _ _)) H2)
      (max_le (by omega) (H1.trans (Nat.le_add_right _ _)))
  have square : 2*h ≤ h*h := Nat.mul_le_mul_right h hh
  have cube : 2*(h*h) ≤ h*h*h := by calc
    _ ≤ h*(h*h) := Nat.mul_le_mul_right _ hh
    _ = _ := by ring
  have fourth : 2*(h*h*h) ≤ h^4 := by calc
    _ ≤ h*(h*h*h) := Nat.mul_le_mul_right _ hh
    _ = _ := by ring
  calc
    _ < h^4 := by omega
    _ = 2^(logWidth r n*4) := (pow_mul ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {a extra E deg Q A B j : ℕ} {s : EpochScales S a extra}

/-- The complete rebased address plus scalar extent fits before a particular
history, word, or team is selected. The same estimate works for every larger
serialization word used by the hardware. -/
theorem JointSchedule.eventually_frozen_operand_room (b : JointSchedule s E deg Q A B j)
    (header : ℕ) (number : e.Entry → ℕ) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let T := epochs s.τ n
      let d := CoverScale.initialDepth (Cube D) r n-1
      let copies := width n s.α
      let mass := S.publicProgramFactor^T*initialMass (D:=D) n r d copies header
      let grid := Fintype.card (Cube D)
      let birth := max 2 (max copies (seedBoxCapacity n r grid d (Fintype.card (Direction grid))))
      let coeff := (birthWordCoefficient e+8)*(BankCharges.bound e+1)*(S.populationFactor+2)
      ∀ w ≥ 60*logWidth r n,
        max (15*mass) (boundary S (d+1) T).sites + max (max birth (coeff*(mass+1))) (max 1 (15*mass))+1 < 2^w ∧
          BoxRoster.paidWordLimit e < 2^w ∧ 3 < 2^w ∧ ∀ t, number t < 2^w := by
  let coeff := (birthWordCoefficient e+8)*(BankCharges.bound e+1)*(S.populationFactor+2)
  let table := Finset.univ.sup number
  filter_upwards [b.eventually_programSeedStorage header,eventually_boundaries S s,
    eventually_ge_atTop (15+coeff+BoxRoster.paidWordLimit e+table)] with n stored rectangles hn
  intro r T d copies mass grid birth cc w hw
  have hr : 1 ≤ r := stretch_one ..
  have h15 : 15 ≤ n := by omega
  have h1 : 1 ≤ n := by omega
  have hd : d+1 = CoverScale.initialDepth (Cube D) r n := by
    have hi : 1≤CoverScale.initialDepth (Cube D) r n := Nat.succ_pos _
    dsimp only [d]; omega
  have hs : (boundary S (d+1) T).sites ≤ r*n := by
    rw [hd]
    exact (show _ ≤ (boundary S (CoverScale.initialDepth (Cube D) r n) T).volume
      (CoverScale.sites (Cube D) (CoverScale.initialDepth (Cube D) r n)) by unfold Shortening.PublicCapacity.Shape.volume; omega).trans
      ((rectangles r hr).1 T le_rfl)
  have small : TeamScales.width n (1/5) ≤ n := Nat.floor_le_of_le
    ((Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast h1 : 1≤(n:ℝ)) (by norm_num : (1/5:ℝ) ≤ 1)).trans_eq (Real.rpow_one _))
  have loaded : 7*mass ≤ TeamScales.width n (1/5) := stored.2.1
  have hm : mass ≤ n := (by omega : mass ≤ TeamScales.width n (1/5)).trans small
  have initial : birth ≤ initialMass (D:=D) n r d copies header := by
    apply le_trans _ (SeedPlan.seedScalar_le_mass (D:=D))
    exact max_le_max le_rfl (max_le_max le_rfl (le_max_left ..))
  have pos : 0 < S.publicProgramFactor := by
    unfold SiteSchedule.publicProgramFactor SiteSchedule.bankRecordFactor Epoch.Round.epochRecordFactor
    positivity
  have low : birth ≤ n := (initial.trans (Nat.le_mul_of_pos_left _ (Nat.pow_pos pos))).trans hm
  have coefficient : coeff ≤ n := by omega
  have raw := relocated_room h15 hr hs hm low coefficient
  have extend := Nat.pow_le_pow_right (by decide : 0<2) hw
  have one : n < 2^w := (Nat.size_le.mp (CellMacro.Generator.size_le_logWidth n r hr)).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨raw.trans_le extend,(by omega),by omega,?_⟩
  intro t
  have bound : number t ≤ table := Finset.le_sup (s:=Finset.univ) (Finset.mem_univ t)
  omega

end Diagonal

end BorderVNP
end Computability
end OAI
