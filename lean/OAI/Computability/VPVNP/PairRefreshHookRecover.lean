import OAI.Computability.VPVNP.PairRefreshHookSite

/-! # Recovering the native job of a specified pair of refresh halves -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.Site

open BurstRAM PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open CompressorRecords CompressorRecords.PortRefresh NewSlots NodeArguments NodeArguments.ChildScan DFS

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates} {bits n hist t : ℕ}
  (R : Site B n hist bits) (ties : Fin t ≃ Tie (2^S.portExponent)) (stride : ℕ) (order : B.Entry ≃ Fin hist)
  (pub : Fin 11 → BurstRAM.Word bits) (m : Memory bits)

theorem recover_job (node : BurstRAM.Word bits) (s : Scratch bits n) (old : R.state.network.Half R.olderSite)
    (new : R.nextState.network.Half R.newerSite)
    (parent : RefreshHalfDecoder.parent R.nextState R.newerSite R.arena R.parent s = some new)
    (job : VisitPath bits n) (tail : List Bool)
    (hit : (R.hook ties stride order pub m).read node s (packed R.state R.olderSite old ++ tail) = some (job,tail)) :
    ∃ es updated, R.action ties stride order pub m old new
      ((packet R.state R.olderSite R.oldNode old).write R.arena s) = some (es,updated) ∧
      job = ⟨node,R.front pub m node old ++ es,(·=s),fun _ => updated⟩ := by
  obtain ⟨⟨out,rest⟩,hr,hj⟩ := Option.map_eq_some_iff.mp hit
  have jobEq : (⟨node,out.trace,(·=s),fun _ => out.updated⟩ : VisitPath bits n) = job := congrArg Prod.fst hj
  have tailEq : rest = tail := congrArg Prod.snd hj
  subst tail
  obtain ⟨parsed,tape,es,selected,trace⟩ := (RefreshHook.read_some_iff R.state R.olderSite R.nextState R.newerSite
    R.arena R.oldNode R.parent (R.front pub m) (R.action ties stride order pub m) _ _ _ _ _).mp hr
  have newer := Option.some.inj (parsed.symm.trans parent)
  have h₁ := (RefreshHalfDecoder.read_iff R.state R.olderSite _ out.value.1 rest).mpr tape
  have h₂ := (RefreshHalfDecoder.read_iff R.state R.olderSite (packed R.state R.olderSite old ++ rest) old rest).mpr rfl
  have older := (Prod.mk.inj (Option.some.inj (h₁.symm.trans h₂))).1
  rw [older,newer] at selected
  rw [older] at trace
  exact ⟨es,out.updated,selected,jobEq.symm.trans (congrArg (fun tr => (⟨node,tr,(·=s),fun _ => out.updated⟩ : VisitPath bits n)) trace)⟩

end PairSimulation.RefreshHook.Site

end VPVNP
end Computability
end OAI
