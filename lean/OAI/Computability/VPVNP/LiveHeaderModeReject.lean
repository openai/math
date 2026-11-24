import OAI.Computability.VPVNP.LiveHeaderPrepared
import OAI.Computability.VPVNP.LiveHeaderPrefixReject

/-! # Rejection of incompatible incident modes by the complete native header table -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram

open BurstRAM BurstRAM.PrivateRAM LiveHeaderSchedule LiveHeaderWidths LiveHeader
open LiveHeaderDescriptors ChainAssignments PrimedInputRAM

variable {w d : ℕ}

theorem bad_mode_native (s : Sizes) (base cap : ℕ) (hw : 4 ≤ w) (advice : CutSchedule.Bits s.advice)
    (cuts : AllCuts s.h s.delta) (g : Fin (2^(s.h+1))) (bad : physicalTag cuts g = none)
    (indices : s.h+2 ≤ 2^d) (adv : s.advice ≤ 2^d) (scratch : 2^d ≤ base)
    (fit : limit s base ≤ 2^w) (tagFit : stages.length ≤ 2^w) (fuel : 107 ≤ cap) :
    ¬ ∃ bs out, runSegment (nativeHeader w s base) cap (some 0) (physicalMemory (d := d) hw advice cuts g) bs =
      some out ∧ endState (some (0 : Word w)) out = none := by
  obtain ⟨xs,ma,first,goodA,ready⟩ := index_advice_prefix s base hw advice cuts g indices adv scratch fit
  obtain ⟨ys,m,second,goodB,img⟩ := Metadata.run_prefix s base d advice cuts g .unit
    (scalarFit_of_limit fit) scratch ma ready.headers ready.summary 10 (by decide) (by omega)
  let id : StageId := ⟨12,by decide⟩
  have pre : StagePrefix s base (some (⟨0,by decide⟩ : StageId)) (physicalMemory (d := d) hw advice cuts g)
      (xs++ys) (some id) m := first.append second
  have haddr (n : ℕ) (h : n ≤ base+14) : (Fin.ofNat (2^w) n).val = n := by
    apply Nat.mod_eq_of_lt
    rw [limit_eq] at fit
    omega
  have hg : ∀ x ∈ xs++ys, x.Good s := by
    intro x hx
    exact (List.mem_append.mp hx).elim (goodA x) (goodB x)
  have startTag : ∀ i, some (⟨0,by decide⟩ : StageId) = some i →
      physicalMemory (d := d) hw advice cuts g (Fin.ofNat (2^w) base).val = LiveStageLink.tagWord w i := by
    rintro _ ⟨⟩
    change physicalMemory (d := d) hw advice cuts g (Fin.ofNat (2^w) base).val = 0
    rw [haddr _ (by omega)]
    simp [physicalMemory,RAMMemory.initialMemory,show ¬base < 2^d by omega]
  have reject : ∀ f bits, execute (nativeStage w s base id) f ((nativeStage w s base id).start 0) m bits = none := by
    intro f bits
    let pub := scalarPub w s base .mode
    have left := img.readback 0 (by decide)
    have right := img.readback 1 (by decide)
    have half := img.readback 7 (by decide)
    have hl := left (Or.inr (Or.inl rfl))
    have hr := right (Or.inr (Or.inr rfl))
    have hdr : SiteHeaders d hw advice cuts g m :=
      fun v => (img.frame v.val (Or.inl (v.isLt.trans_le scratch))).trans (ready.headers v)
    have h0 : (pub 0).val = widthAddr base .liveLeft := haddr _ (by change base+1 ≤ base+14; omega)
    have h1 : (pub 1).val = widthAddr base .liveRight := haddr _ (by change base+2 ≤ base+14; omega)
    have h2 : (pub 2).val = flagAddr base .firstHalf := haddr _ (by change base+8 ≤ base+14; omega)
    let P := ((entry (Mode.program.template none)).2.instantiate w (rowData w s base .mode)).program
    change execute P f (P.start 0) m bits = none
    dsimp only [P]
    rw [entry_start]
    apply physical_mode_rejects hdr pub 0 ?_ ?_ ?_ bad f bits
    · rw [h0]
      change (m (base+1)).val = CutSchedule.width (s.h+1) s.delta g.val
      change (m (base+1)).val = CutSchedule.width (s.h+1) s.delta (g.val+1-1) at hl
      simpa using hl
    · rw [h1]; exact hr
    · rw [h2]; exact half
  exact pre.rejects_entry hg tagFit (by rw [stage_count]; omega) startTag reject

end LiveHeaderProgram

end VPVNP
end Computability
end OAI
