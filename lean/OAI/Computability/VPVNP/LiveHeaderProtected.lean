import OAI.Computability.VPVNP.LiveHeaderScalarProtected
import OAI.Computability.VPVNP.LiveHeaderPrimedProtected
import OAI.Computability.VPVNP.LiveHeaderScanProtected
import OAI.Computability.VPVNP.LiveHeaderAdviceStages
import OAI.Computability.VPVNP.LiveStageLinkInversion

/-!
# The native header machine preserves every address below its scratch base

The statement covers every successful native call, including calls started
on malformed input or intermediate memories. Thus the enclosing dispatcher
can keep its own stage tag immediately before the header scratch area.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM LiveHeaderSchedule LiveHeader
open scoped Fin.CommRing

variable {w : ℕ}

private theorem index_protected (s : Sizes) (base : ℕ) (fit : limit s base ≤ 2^w) (hw : 4 ≤ w)
    (fuel : ℕ) (state : Word w) (m : Memory w) (bits : List Bool) (rep : Report w)
    (run : let P := ((stageTemplate .index).2.instantiate w (rowData w s base .index)).program
      execute P fuel (P.start state) m bits = some rep) (a : ℕ) (ha : a < base) : after m rep.events a = m a := by
  rw [limit_eq] at fit
  let pub := indexWords w s base
  let bound : Word w := Fin.ofNat _ (s.h+2)
  let addr : Word w := Fin.ofNat _ a
  have ha' : addr.val = a := Nat.mod_eq_of_lt (by omega)
  have va : (pub 0).val = indexBase base := Nat.mod_eq_of_lt (by dsimp [indexBase]; omega)
  have vh : (pub 1).val = highAddr s base := Nat.mod_eq_of_lt (by dsimp [highAddr,indexBase]; omega)
  have vc : (pub 2).val = populationAddr s base := Nat.mod_eq_of_lt (by dsimp [populationAddr,highAddr,indexBase]; omega)
  have vb : bound.val = s.h+2 := Nat.mod_eq_of_lt (by omega)
  have hafter : (pub 0).val+(s.h+2) ≤ (pub 1).val := by rw [vh,va]; rfl
  have hcount : (pub 1).val < (pub 2).val := by rw [vc,vh]; exact Nat.lt_succ_self _
  dsimp only [stageTemplate] at run
  rw [entry_start,index_row] at run
  apply LiveHeaderBounded.frame_any indexTable pub bound fuel state m bits rep run a
  intro f r hlt hr
  have ht : addr.val < (pub 0).val := by rw [ha',va]; dsimp [indexBase]; omega
  have hi : state.val < s.h+2 := vb ▸ Fin.lt_def.mp hlt
  have hcast : (state.val : Word w) = state := Fin.ext (Nat.mod_eq_of_lt state.isLt)
  rw [←ha']
  exact (index_step hw pub _ addr hafter hcount ht state.val hi m bits r (hcast.symm ▸ hr)).2

private theorem advice_protected (s : Sizes) (base : ℕ) (fit : limit s base ≤ 2^w) (hw : 4 ≤ w)
    (fuel : ℕ) (state : Word w) (m : Memory w) (bits : List Bool) (rep : Report w)
    (run : let P := ((stageTemplate .advice).2.instantiate w (rowData w s base .advice)).program
      execute P fuel (P.start state) m bits = some rep) (a : ℕ) (ha : a < base) : after m rep.events a = m a := by
  rw [limit_eq] at fit
  let pub := adviceWords w s base
  let bound : Word w := Fin.ofNat _ s.advice
  let addr : Word w := Fin.ofNat _ a
  have ha' : addr.val = a := Nat.mod_eq_of_lt (by omega)
  have vb : bound.val = s.advice := Nat.mod_eq_of_lt (by omega)
  dsimp only [stageTemplate] at run
  rw [entry_start,advice_row] at run
  apply LiveHeaderBounded.frame_any adviceTable pub bound fuel state m bits rep run a
  intro f r hlt hr
  have hi : state.val < s.advice := vb ▸ Fin.lt_def.mp hlt
  have dst : adviceBase s base = base + 17 + 3*(s.h+2) := by
    dsimp [adviceBase,rightIndexBase,leftIndexBase,populationAddr,highAddr,indexBase]; omega
  have hv : (pub 1).val = adviceBase s base := Nat.mod_eq_of_lt (by rw [dst]; omega)
  have hfit : (pub 1).val+s.advice ≤ 2^w := by rw [hv,dst]; omega
  have ht : addr.val < (pub 1).val := by rw [ha',hv,dst]; omega
  have hcast : (state.val : Word w) = state := Fin.ext (Nat.mod_eq_of_lt state.isLt)
  rw [←ha']
  exact (advice_step hw pub rfl _ hfit addr ht state.val hi m bits r (hcast.symm ▸ hr)).2

/-- Each of the thirty-one source stages protects the lower part of memory
independently of the values read from scratch or processor words. -/
theorem component_protected (s : Sizes) (base : ℕ) (stg : Stage) (fit : limit s base ≤ 2^w) (hw : 4 ≤ w)
    (fuel : ℕ) (state : Word w) (m : Memory w) (bits : List Bool) (rep : Report w)
    (run : let P := ((stageTemplate stg).2.instantiate w (rowData w s base stg)).program
      execute P fuel (P.start state) m bits = some rep) (a : ℕ) (ha : a < base) : after m rep.events a = m a := by
  cases stg with
  | index => exact index_protected s base fit hw fuel state m bits rep run a ha
  | advice => exact advice_protected s base fit hw fuel state m bits rep run a ha
  | primedInit => exact PrimedStages.init_protected s base fit fuel state m bits rep run a ha
  | primedDigits => exact PrimedStages.digits_protected s base fit fuel state m bits rep run a ha
  | scan side f => exact ScanRows.call_preserves_below s base side f fit fuel state m bits run a ha
  | width slot => exact scalar_call_frame s base (.width slot) trivial fit fuel state m bits rep run a ha
  | flag flag => exact scalar_call_frame s base (.flag flag) trivial fit fuel state m bits rep run a ha
  | firstTail => exact scalar_call_frame s base .firstTail trivial fit fuel state m bits rep run a ha
  | mode => exact scalar_call_frame s base .mode trivial fit fuel state m bits rep run a ha
  | descriptor side f => exact scalar_call_frame s base (.descriptor side f) trivial fit fuel state m bits rep run a ha

/-- The linked header dispatcher itself preserves every word below the
scratch base. Its only extra write is to the inner tag at the base. -/
theorem native_protected (s : Sizes) (base : ℕ) (fit : limit s base ≤ 2^w) (hw : 4 ≤ w)
    (hfits : stages.length ≤ 2^w) (fuel : ℕ) (state : Word w) (m : Memory w) (bits : List Bool) (rep : Report w)
    (run : let P := (program.instantiate w (publicData w s base)).program
      execute P fuel (P.start state) m bits = some rep) (a : ℕ) (ha : a < base) : after m rep.events a = m a := by
  let addr : Word w := Fin.ofNat _ base
  have hv : addr.val = base := Nat.mod_eq_of_lt (by rw [limit_eq] at fit; omega)
  change execute (LiveStageLink.machine component next (bank w s base) addr).program fuel
    ((LiveStageLink.machine component next (bank w s base) addr).program.start state) m bits = some rep at run
  by_cases hgood : (m addr.val).val < stages.length
  · let i : StageId := ⟨(m addr.val).val,hgood⟩
    have htag : m addr.val = LiveStageLink.tagWord w i := Fin.ext (Nat.mod_eq_of_lt (m addr.val).isLt).symm
    have hrun := execute_extend run (2*stages.length+2)
    obtain ⟨r,hr,rfl⟩ := LiveStageLink.recover_call component next (bank w s base) addr i hfits (by omega) state m bits rep htag hrun
    rw [component_start] at hr
    have hf := component_protected s base (stage i) fit hw _ state m bits r hr a ha
    rw [LiveStageLink.linkedReport_after]
    cases r.result <;> cases next i <;> simp_all [writeMemory, Nat.ne_of_lt ha]
  · have hbad := LiveStageLink.execute_invalid component next (bank w s base) addr hfits state fuel m (le_of_not_gt hgood) bits
    dsimp only at hbad
    rw [run] at hbad
    contradiction

end LiveHeaderProgram

end VPVNP
end Computability
end OAI
