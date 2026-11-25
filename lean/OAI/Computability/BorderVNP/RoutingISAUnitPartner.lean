import OAI.Computability.BorderVNP.RoutingISAPaddingCommon

/-! # Checking a complete zero block on the unit branch

The cursor is copied from the persistent zero register, so the scan includes
the first physical position as well as the entire remaining block.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

/-- Initialize the position to zero and scan every physical word of this partner. -/
def unitPartner : Code := .seq (.copy 10 0) zeroScan

/-- The unit-branch check returns precisely on all-zero incident blocks, preserves
the setup registers and costs at most one cursor copy and one complete scan. -/
theorem unitPartner_check {w : ℕ} (f : BroadcastFrame) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (m : Memory w) (base : ℕ)
    (image : f.At (readings pub) (readings m)) (fit : f.Fits w (pub 0).val) :
    PartnerCheck pub macros m f.teams f.team (1 + f.capacity * (zeroScanBody.slots + 1) + 1)
      unitPartner (partnerInv f base) (f.ZeroFrom (readings m) 0) := by
  suffices paths : ∀ i < f.teams, i ≠ f.team → ∀ s : Bank w,
      partnerInv f base s → (s 11).val = i →
      (f.ZeroFrom (readings m) 0 i → ∃ es t, Runs pub macros unitPartner s m es t m ∧
        traceCost es ≤ 1 + f.capacity * (zeroScanBody.slots + 1) + 1 ∧
        partnerInv f base t ∧ t 11 = s 11) ∧
      (∀ {es t mt}, Runs pub macros unitPartner s m es t mt →
        mt = m ∧ partnerInv f base t ∧ t 11 = s 11 ∧ f.ZeroFrom (readings m) 0 i) from
    ⟨fun i hi hd s hs h11 => (paths i hi hd s hs h11).1,
     fun i hi hd s hs h11 => (paths i hi hd s hs h11).2⟩
  intro i hi hd s hs h11
  let u := Function.update s (10 : Reg) (s 0)
  have copy : Runs pub macros (.copy 10 0) s m [tick w] u m := Runs.localStep m rfl rfl
  have inv : partnerInv f base u := partnerInv_of_preserves hs fun k hk => by
    have hne : k ≠ 10 := by
      rintro rfl
      exact (by decide : ¬ ((10 : Reg).val ≤ 9 ∨ (10 : Reg) = 14 ∨ (10 : Reg) = 19)) hk
    simp only [u, Function.update_of_ne hne]
  have start : (u 10).val = 0 := by simpa only [u, Function.update_self, readings] using hs.1.1
  have limit : (u 7).val = f.capacity := inv.1.2.2.2.2.2.2.2.1
  have partner : u 11 = s 11 := Function.update_of_ne (by decide) ..
  have index : (u 11).val = i := (congrArg Fin.val partner).trans h11
  have room : ZeroScanRoom w (readings pub) (readings m) (u 11).val (u 10).val (u 7).val := by
    rw [index, start, limit]
    exact scanRoom image fit hi hd 0
  have bounds : (u 10).val ≤ (u 7).val := start ▸ Nat.zero_le _
  have good : (∀ j, (u 10).val ≤ j → j < (u 7).val →
      (m (zeroScanAddr (readings pub) (readings m) (u 11).val j)).val = 0) ↔
      f.ZeroFrom (readings m) 0 i := by
    simp only [start, limit, index, scanAddr_eq image, BroadcastFrame.ZeroFrom, readings]
  have post {t : Bank w} (hr : ZeroScanResult u t) : partnerInv f base t ∧ t 11 = s 11 := by
    refine ⟨partnerInv_of_preserves inv fun k hk => congrArg Fin.val (hr.2 k ?_ ?_ ?_),
      (hr.2 11 (by decide) (by decide) (by decide)).trans partner⟩
    · rcases hk with hk | rfl | rfl
      · omega
      · decide
      · decide
    · rintro rfl
      exact (by decide : ¬ ((10 : Reg).val ≤ 9 ∨ (10 : Reg) = 14 ∨ (10 : Reg) = 19)) hk
    · rintro rfl
      exact (by decide : ¬ ((12 : Reg).val ≤ 9 ∨ (12 : Reg) = 14 ∨ (12 : Reg) = 19)) hk
  constructor
  · intro hz
    obtain ⟨es, t, run, cost, res⟩ :=
      zeroScan_run pub macros m u inv.1.1 inv.1.2.1 bounds room (good.mpr hz)
    refine ⟨_, t, copy.seq run, ?_, post res⟩
    change 1 + traceCost es ≤ _
    rw [start, limit, Nat.sub_zero] at cost
    omega
  · intro es t mt run
    obtain ⟨v, mv, _, _, _, init, tail⟩ := Runs.seq_iff.mp run
    obtain ⟨_, hv, hm⟩ := init.unique_of_deterministic rfl copy
    subst v
    subst mv
    obtain ⟨mem, res, hz⟩ := zeroScan_sound pub macros m u inv.1.1 inv.1.2.1 bounds room tail
    exact ⟨mem, (post res).1, (post res).2, good.mp hz⟩

end RoutingISA

end BorderVNP
end Computability
end OAI
