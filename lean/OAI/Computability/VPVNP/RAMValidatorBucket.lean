import OAI.Computability.VPVNP.RAMValidatorControl
import OAI.Computability.VPVNP.RAMSiteRun
import OAI.Computability.VPVNP.RAMWork

/-!
# Bounded machine simulation in a transcript bucket

The range test precedes the private calls. Each call checks all three probe
allowances before consuming a read guess. Once simulation stops, the processor
validates its unused choice suffix and its outgoing cut or terminal halt.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM.PrivateRAM

open VPVNP.BurstRAM

variable {w p r k : ℕ}

/-- Execute the calls and check their successor information. This includes
work spent before an eventual failure on arbitrary input. -/
def Machine.runBucket (M : Machine w p r k) (fuel S H v : ℕ) (input : Cut w)
    (output : Option (Cut w)) (bits : List Bool) : Option (List (Report w)) × ℕ :=
  if input.state.isSome → v * H ≤ input.cost ∧ input.cost < (v+1)*H then
    let loop := M.privateSite fuel H ((v+1)*H) (S*H) (2*H-1) input (2*H-1) bits
    match loop.output with
    | none => (none, 16 + loop.work)
    | some (rs, tail) =>
      let finish := finishReports input output rs tail
      (if finish.1 then some rs else none, 16 + loop.work + finish.2)
  else (none, 16)

theorem Machine.runBucket_result (M : Machine w p r k) (fuel S H v : ℕ) (input : Cut w)
    (output : Option (Cut w)) (bits : List Bool) :
    (M.runBucket fuel S H v input output bits).1 = validateSite M.program fuel S H v input output bits := by
  unfold Machine.runBucket validateSite runSite
  split
  · dsimp only
    rw [Machine.privateSite_output]
    cases runSiteLoop M.program fuel H ((v+1)*H) (S*H) (2*H-1) input (2*H-1) bits with
    | none => rfl
    | some z =>
      obtain ⟨rs, tail⟩ := z
      cases tail with
      | nil => cases output <;> simp [finishReports, meteredAdvance_result]
      | cons b bs => rfl
  · rfl

theorem Machine.runBucket_iff (M : Machine w p r k) {fuel S H v : ℕ} {input : Cut w}
    {output : Option (Cut w)} {bits : List Bool} {rs : List (Report w)} (hH : 0 < H) :
    (M.runBucket fuel S H v input output bits).1 = some rs ↔
      SiteCheck M.program fuel S H v input output rs ∧ bits = rs.flatMap (fun r => guessBits r.events) := by
  rw [Machine.runBucket_result, validateSite_iff hH]

theorem Machine.runBucket_work (M : Machine w p r k) (fuel S H v : ℕ) (input : Cut w)
    (output : Option (Cut w)) (bits : List Bool) (hH : 0 < H) (hf : H ≤ 2*fuel) :
    (M.runBucket fuel S H v input output bits).2 ≤
      48 + 256*(H+1)*(fuel+1)*(fuel+1)*(w+2) + (2*H)*(16*fuel+16) := by
  let loop := M.privateSite fuel H ((v+1)*H) (S*H) (2*H-1) input (2*H-1) bits
  have hl := M.privateSite_work_le hf ((v+1)*H) (S*H) input (2*H-1) bits
  change loop.work ≤ _ at hl
  by_cases hi : input.state.isSome → v * H ≤ input.cost ∧ input.cost < (v+1)*H
  · unfold Machine.runBucket
    rw [ite_eq_left hi]
    rw [show M.privateSite fuel H ((v+1)*H) (S*H) (2*H-1) input (2*H-1) bits = loop from rfl]
    dsimp only
    cases he : loop.output with
    | none =>
      dsimp only
      omega
    | some z =>
      obtain ⟨rs, tail⟩ := z
      have hr : runSite M.program fuel S H v input bits = some (rs, tail) := by
        unfold runSite
        rw [ite_eq_left hi]
        simpa only [loop, Machine.privateSite_output] using he
      obtain ⟨hs, _⟩ := (runSite_iff hH).mp hr
      have hb := finishReports_work input output rs tail H fuel
        (boundedReports_of_localSegment hs.calls (hs.cost_lt hH).le)
      dsimp only
      omega
  · unfold Machine.runBucket
    rw [ite_eq_right hi]
    omega

end BurstRAM.PrivateRAM

end VPVNP
end Computability
end OAI
