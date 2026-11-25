import OAI.Computability.BorderVNP.DiagonalNativeUnit
import OAI.Computability.BorderVNP.TransmissionImageReturns
import OAI.Computability.BorderVNP.TransmissionTableAllocation
import OAI.Computability.BorderVNP.RoutingISAPaddingSchedule
import OAI.Computability.BorderVNP.RoutingISARelayLoops

/-! # The padding and relay checks on the scheduler's actual table image

Both read-only checks consume the memory produced by the preceding interval and
offset passes. The word-level relay room follows from the two oriented leg lengths
and the allocated arrays.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM Transmission

variable {w : ℕ}

/-- On the allocated scheduling image the actual padding and relay scans have the
physical Boolean tests as their complete and sound conditions. Every return preserves
the complete external memory, including the received common broadcast. -/
theorem route_checks {l : TableLayout} {row : ℕ → TableRow} {before : ℕ → ℕ}
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (image : l.Image row before (readings m)) (al : l.Allocated w) (ordered : l.Ordered)
    (rowsFit : l.RowsFit w row) (hf : (pub 0).val = l.frame) (loaded : l.frameFields before)
    (f : BroadcastFrame) (im : f.At (readings pub) before) (fit : f.Fits w (pub 0).val)
    (teams : f.teams = l.teams)
    (capacity : ∀ u v, f.header + Routing.legLoad al.teamCount (l.widthMatrix row) u v +
      Routing.legLoad al.teamCount (l.widthMatrix row) v u ≤ f.capacity) :
    let width := tableWidth l row teams
    let len := fun x y => l.partnerLength row x f.team y
    NativeLinkCheck pub mac (.seq checkPadding checkRelays) s m
      (f.linkCheckTicks (headerSetup.slots+(readFrame 19 62 63 18).slots+1) paddingStartBlock.slots +
        relayCheckCost l.teams len)
      ((∀ v : Fin f.teams, v.val ≠ f.team → f.ZeroFrom (readings m) (f.usedPrefix fit width v) v) ∧
        RelayChecks l.teams len (readings pub) (readings m) f.team) := by
  intro width len
  have atFrame := image.broadcast_of_ordered ordered hf im
  have a := Schedule.of_table image al pub hf loaded f atFrame fit teams capacity
  have chk := checkPadding_schedule f pub mac s m atFrame fit width a.table a.pair a.capacity
  apply chk.seq
  intro t
  have fld (j : ℕ) (hj : j ≤ 20) : readings m (l.frame+j) = before (l.frame+j) :=
    image.before_records ordered (by have := ordered.frame; omega)
  have state : l.frameFields (readings m) := by
    simpa only [TableLayout.frameFields,fld 1 (by decide),fld 12 (by decide),fld 13 (by decide),
      fld 16 (by decide),fld 17 (by decide),fld 18 (by decide),fld 20 (by decide)] using loaded
  have relay := checkRelays_test pub mac al row t m rowsFit hf state atFrame.1 (fit.own.trans_eq teams)
    image.widths (image.relayRooms al (readings pub) hf loaded f atFrame fit capacity)
  have keep {z : Bank w} {mz : Memory w} (h : RelayState l (readings m) f.team l.teams (.ofWords z mz)) : mz = m :=
    funext fun i => Fin.ext (congrFun h.2.1 i)
  constructor
  · intro valid
    obtain ⟨es,z,mz,run,ct,post⟩ := relay.complete valid
    exact ⟨es,z,keep post ▸ run,ct⟩
  · intro es z mz run
    obtain ⟨valid,post⟩ := relay.sound run
    exact ⟨keep post,valid⟩

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
