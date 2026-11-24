import OAI.Computability.VPVNP.LiveHeaderPrefix
import OAI.Computability.VPVNP.LiveHeaderUnique

/-! # Executing a partial header schedule and ruling out paths after rejection -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram

open BurstRAM BurstRAM.PrivateRAM LiveHeaderSchedule

variable {w : ℕ}

/-- The actual linked header machine reaches the scheduled suffix with the
specified persistent word, memory and stage tag. -/
theorem StagePrefix.run {s : Sizes} {base cap : ℕ} {fromId toId : Option StageId}
    {m out : Memory w} {xs : List (StageTrace w)} (a : StagePrefix s base fromId m xs toId out)
    (hfits : stages.length ≤ 2^w) (hroom : ∀ x ∈ xs, x.fuel+2*stages.length+5 ≤ cap)
    (htag : ∀ i, fromId = some i → m (Fin.ofNat (2^w) base).val = LiveStageLink.tagWord w i) :
    let addr : Word w := Fin.ofNat _ base
    let outs := xs.flatMap (fun x => x.output addr)
    let initial := fromId.map (fun _ => (0 : Word w))
    runSegment (program.instantiate w (publicData w s base)).program cap initial m (xs.flatMap StageTrace.paths) = some outs ∧
    endState initial outs = toId.map (fun _ => (0 : Word w)) ∧ after m (eventLog outs) = out ∧
    (∀ i, toId = some i → out addr.val = LiveStageLink.tagWord w i) := by
  induction a with
  | nil => exact ⟨rfl,rfl,rfl,htag⟩
  | @cons x m xs finalId finalMem run _ ih =>
    let addr : Word w := Fin.ofNat _ base
    have hc := (run_component s base x.id x.fuel (some 0) m x.paths).trans run.source
    obtain ⟨hr,hs,hm,_⟩ := LiveStageLink.runSegment_accepting component next (bank w s base) addr
      x.id hfits (hroom x (by simp)) 0 m x.paths x.reports (htag x.id rfl) run.frame hc run.accept
    change runSegment (program.instantiate w (publicData w s base)).program cap (some 0) m x.paths = some (x.output addr) at hr
    change endState (some 0) (x.output addr) = _ at hs
    change after m (eventLog (x.output addr)) = x.finalMem addr m at hm
    have ht : ∀ i, next x.id = some i → x.finalMem addr m addr.val = LiveStageLink.tagWord w i := by
      intro i hi
      unfold StageTrace.finalMem
      rw [hi,LiveStageLink.transferMemory_tag]
    obtain ⟨hr', hs', hm', ht'⟩ := ih (fun y hy => hroom y (List.mem_cons_of_mem _ hy)) ht
    change runSegment _ cap (some 0) m (x.paths++xs.flatMap StageTrace.paths) =
        some (x.output addr++xs.flatMap (fun y => y.output addr)) ∧
      endState (some 0) (x.output addr++xs.flatMap (fun y => y.output addr)) = finalId.map (fun _ => 0) ∧
      after m (eventLog (x.output addr++xs.flatMap (fun y => y.output addr))) = finalMem ∧ _
    refine ⟨?_,?_,?_,ht'⟩
    · rw [PrimedSchedule.runSegment_append,hr]
      simp only [Option.bind_some,hs,hm]
      rw [hr']; rfl
    · rw [endState_append,hs]; exact hs'
    · have hsplit (u v : List (Report w)) : after m (eventLog (u++v)) = after (after m (eventLog u)) (eventLog v) := by
        simp [eventLog,after,List.foldl_append]
      rw [hsplit,hm]; exact hm'

end LiveHeaderProgram

end VPVNP
end Computability
end OAI
