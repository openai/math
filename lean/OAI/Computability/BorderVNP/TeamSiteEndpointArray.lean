import OAI.Computability.BorderVNP.TeamSiteConsistencyExits
import OAI.Computability.BorderVNP.TeamSiteConsistencyHandoff

/-! # Array form of independent physical processor endpoints

The finite array of shared outgoing frames is checked at each site's own input
and output. In row zero the input is the public frame; all other rows use the
immediately preceding output.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite

open VPVNP BurstRAM TeamTapeHandoff TeamSiteConsistency

variable {w p r k a teams : ℕ}

private theorem endpoint_indices (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : TeamOpcode.Macros w a) (H limit cap : Word w) (teams : ℕ) (first : Frame w r)
    (input out : Fin teams → Frame w r) (blocks : Fin teams → List (TeamRAM.Event w))
    (head : ∀ j, j.val = 0 → input j = first)
    (adj : ∀ i j, j.val = i.val+1 → input j = out i) :
    EndpointRows P pub lib H limit cap first (List.ofFn blocks) (List.ofFn out) ↔
      ∀ j, EndpointRow P pub lib H limit cap (input j) (blocks j) (out j) := by
  induction teams generalizing first with
  | zero => simp [EndpointRows]
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ,EndpointRows,Fin.forall_fin_succ,head 0 rfl]
    apply and_congr_right
    intro _
    apply ih (out 0) (fun j => input j.succ) (fun j => out j.succ) (fun j => blocks j.succ)
    · intro j h; apply adj 0 j.succ; simp [h]
    · intro i j h; apply adj i.succ j.succ; simp [h]

/-- The complete native-PC handoff schedule is precisely the family of independently
checked processor rows, with their actual shared predecessor words. -/
theorem endpointRows_iff_pointwise (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : TeamOpcode.Macros w a) (H limit cap : Word w) (first : Frame w r)
    (blocks : Fin teams → List (TeamRAM.Event w)) (out : Fin teams → Frame w r) :
    EndpointRows P pub lib H limit cap first (List.ofFn blocks) (List.ofFn out) ↔
      ∀ j, EndpointRow P pub lib H limit cap (predecessor first out j) (blocks j) (out j) :=
  let checked := native_frame_checks first out
  endpoint_indices P pub lib H limit cap teams first _ out blocks checked.initial checked.adjacent

end TeamSite

end BorderVNP
end Computability
end OAI
