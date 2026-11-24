import OAI.Computability.VPVNP.CompressorRecordsSelectedArena

/-! # Data-dependent reads and the absolute demand-role arena -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SelectedArena

open Compression BurstRAM VPVNP.CompressorRecords.Shrink
open scoped Fin.CommRing Classical

variable {a g w : ℕ} (X : State a (packingLaneBits a g)) (termBase stride : Word w)

private theorem demand_offsets (p : Fin 11 → Word w) (shr : Fin 14 → Word w) (T : IncidenceDirectory w)
    (mem : Memory w) (layout : Bool) (ins : DemandRAM.Inputs p shr T) (degree : (p 0).val=2^a)
    (inc : T.ActualColumns X mem) (place : ShrinkRAM.PlacementColumns X.slots X.baseIndex shr layout mem)
    (room : DemandRAM.oldCount X ≤ 2^w) (i : Word w) (hi : i.val<DemandRAM.oldCount X) :
    (BundleRAM.sourceSite p i).val < positions X ∧ (BundleRAM.targetSite p mem i).val < positions X ∧
      (DemandRAM.endpoints p mem i).1.val < positions X ∧ (DemandRAM.endpoints p mem i).2.val < positions X := by
  let E := BundleKeys.oldArcOrder (a := a) (g := g) X.baseIndex
  let e := E.symm ⟨i.val,hi⟩
  have he : i.val = (E e).val := by simp [e]
  let src := sourcePosition e
  let dst := sourcePosition (X.packingData.actual e)
  let code (x : Old X.Base a g) := ShrinkRAM.word w (oldNumber X.baseIndex x)
  obtain ⟨hs,ht⟩ := DemandRAM.site_inputs X T inc degree ins.incidence room e he
  have small (x : Old X.Base a g) : (code x).val < positions X :=
    (Nat.mod_le ..).trans_lt ((oldIndex_val X.baseIndex x) ▸ (oldIndex X.baseIndex x).isLt)
  have th : (mem (p 6+code src).val).val = (decide (X.packingData.thick src)).toNat := by
    have ⟨_,h,_,_⟩ := (Prod.mk.inj (place.atSite src)).imp_right Prod.mk.inj |>.imp_right (And.imp_right Prod.mk.inj)
    rw [ins.thick]
    exact h
  have bit : mem (p 6+code src).val = ((decide (X.packingData.thick src)).toNat : Word w) :=
    Fin.ext (th.trans (Nat.mod_eq_of_lt (th ▸ (mem (p 6+code src).val).isLt)).symm)
  refine ⟨hs ▸ small src, ht ▸ small dst, ?_⟩
  unfold DemandRAM.endpoints
  rw [hs,ht]
  change (code src + mem (p 6+code src).val*(code dst-code src)).val < _ ∧
    (code dst-mem (p 6+code src).val*(code dst-code src)).val < _
  rw [bit]
  by_cases h : X.packingData.thick src
  · simpa only [h,decide_true,Bool.toNat_true,Nat.cast_one,one_mul,add_sub_cancel,sub_sub_cancel] using
      And.intro (small dst) (small src)
  · simpa only [h,decide_false,Bool.toNat_false,Nat.cast_zero,zero_mul,add_zero,sub_zero] using
      And.intro (small src) (small dst)

theorem demand_outside (p₀ : Fin 14 → Word w) (T : IncidenceDirectory w) (layoutWord : Word w)
    (mem : Memory w) (layout : Bool) (degree : (p₀ 2).val=2^a) (inc : T.ActualColumns X mem)
    (place : ShrinkRAM.PlacementColumns X.slots X.baseIndex (shrinkWords X termBase stride p₀ layoutWord) layout mem)
    (old : OldInputs X termBase stride p₀ T) (fit : Fits X termBase stride)
    (i : Word w) (c : Fin 6) (hi : i.val<DemandRAM.oldCount X) :
    DemandRAM.inputAddr (demandWords X termBase stride p₀ T) mem i c < roleBase X termBase stride := by
  let p := demandWords X termBase stride p₀ T
  let shr := shrinkWords X termBase stride p₀ layoutWord
  have endFit : roleBase X termBase stride + 4*DemandRAM.absoluteCount X < 2^w := fit
  have oldFit : DemandRAM.oldCount X ≤ 2^w := by rw [DemandRAM.count_eq X]; omega
  obtain ⟨src,dst,cPos,dPos⟩ := demand_offsets X p shr T mem layout (inputs X termBase stride p₀ T layoutWord)
    degree inc place oldFit i hi
  have col (t : Fin 4) (off : Word w) (small : off.val < positions X) :
      (placementWord X termBase stride t+off).val < roleBase X termBase stride := by
    have ht := Nat.mul_le_mul_right (positions X) t.isLt
    rw [Nat.succ_mul] at ht
    have eq := column_value X termBase stride fit t
    change _ < placementBase X termBase stride+4*positions X
    exact (Nat.mod_le ..).trans_lt (show (placementWord X termBase stride t).val+off.val < placementBase X termBase stride+4*positions X by rw [eq]; omega)
  fin_cases c
  · change (T.actualOut+i).val < _
    have bound : origin X termBase stride ≤ roleBase X termBase stride := by unfold roleBase placementBase; omega
    have ho := old.actualOut
    exact (Nat.mod_le ..).trans_lt (show T.actualOut.val+i.val < roleBase X termBase stride by omega)
  · exact col 1 _ src
  · exact col 1 _ dst
  · exact col 2 _ cPos
  · exact col 3 _ cPos
  · exact col 0 _ dPos

theorem role_base_val (p₀ : Fin 14 → Word w) (T : IncidenceDirectory w) (fit : Fits X termBase stride) :
    (demandWords X termBase stride p₀ T 10).val = roleBase X termBase stride := by
  have room : roleBase X termBase stride + 4*DemandRAM.absoluteCount X < 2^w := fit
  exact Nat.mod_eq_of_lt (show roleBase X termBase stride < 2^w by omega)

theorem demand_regions (p₀ : Fin 14 → Word w) (T : IncidenceDirectory w) (layoutWord : Word w)
    (mem : Memory w) (layout : Bool) {l₀ : Bool}
    (hp : ShrinkRAM.Params p₀ a (Shrink.colors a) (Shrink.J a) g l₀) (inc : T.ActualColumns X mem)
    (place : ShrinkRAM.PlacementColumns X.slots X.baseIndex (shrinkWords X termBase stride p₀ layoutWord) layout mem)
    (old : OldInputs X termBase stride p₀ T) (fit : Fits X termBase stride) :
    DemandRAM.Regions (demandWords X termBase stride p₀ T) mem (DemandRAM.oldCount X) := by
  apply DemandRAM.regions X (demand_params X termBase stride p₀ T hp)
  · rw [role_base_val X termBase stride p₀ T fit]; exact fit.le
  · intro i c hi
    left
    rw [role_base_val X termBase stride p₀ T fit]
    exact demand_outside X termBase stride p₀ T layoutWord mem layout hp.degree inc place old fit i c hi

/-- Run the native role pass with no abstract read-address separation premise.
The earlier score, placement, incidence and term cells all lie in the preserved prefix. -/
theorem run_roles (p₀ : Fin 14 → Word w) (T : IncidenceDirectory w) (layoutWord : Word w)
    (mem : Memory w) (layout : Bool) {l₀ : Bool}
    (hp : ShrinkRAM.Params p₀ a (Shrink.colors a) (Shrink.J a) g l₀) (inc : T.ActualColumns X mem)
    (place : ShrinkRAM.PlacementColumns X.slots X.baseIndex (shrinkWords X termBase stride p₀ layoutWord) layout mem)
    (old : OldInputs X termBase stride p₀ T) (fit : Fits X termBase stride) :
    let p := demandWords X termBase stride p₀ T
    let M := (PrimedStackRAM.template DemandRAM.visit 0).instantiate w p
    ∃ rs, runSegment M.program 65 (some 0) mem (List.replicate (DemandRAM.oldCount X) []) = some rs ∧
      DemandRAM.RoleColumns X layout (roleBase X termBase stride) (after mem (eventLog rs)) ∧
      (∀ x, x < roleBase X termBase stride ∨ endAddr X termBase stride ≤ x → after mem (eventLog rs) x = mem x) ∧
      rs.length = DemandRAM.oldCount X ∧ (∀ r ∈ rs, r.events.length=64 ∧ countProbes r.events=10) ∧
      RAMBuckets.cost Report.probes rs = 11*DemandRAM.oldCount X := by
  have rb := role_base_val X termBase stride p₀ T fit
  have room : (demandWords X termBase stride p₀ T 10).val + 4*DemandRAM.absoluteCount X ≤ 2^w := rb.symm ▸ fit.le
  have r := DemandRAM.run_roles X T (demand_params X termBase stride p₀ T hp) (inputs X termBase stride p₀ T layoutWord)
    inc place room (fun i c hi => Or.inl (rb.symm ▸ demand_outside X termBase stride p₀ T layoutWord mem layout hp.degree inc place old fit i c hi))
  simpa only [rb,endAddr] using r

end CompressorRecords.SelectedArena

end VPVNP
end Computability
end OAI
