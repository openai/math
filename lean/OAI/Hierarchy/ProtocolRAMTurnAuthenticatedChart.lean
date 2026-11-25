import OAI.Hierarchy.ProtocolRAMTurnAuthenticated
import OAI.Hierarchy.ProtocolRAMTurnCaptured
import OAI.Hierarchy.TaggedWirePublicSeatOrder
import OAI.Hierarchy.TaggedWireRoleTableROM

namespace OAI
/-! # Authenticating the native chart on each original source that contributes bits -/
noncomputable section
namespace Hierarchy.ProtocolRAMTurnSnapshot
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ProtocolRAMTurnChart
open AdaptiveProbe ProbeStage CoreBoard HistoryRoles RoleProgram
open scoped Fin.CommRing
variable {h W k attempts w : ℕ} (S : PurchaseSampler) (b : Board)
local notation "roles" => WordSeats.fixedRoom (k:=k) (attempts:=attempts) S
variable {old : Fin b.old→ℕ} {width : Fin b.edges→ℕ}
    {before : ∀i,0<old i→Bool→Public S h W k attempts}
    {after : ∀i,0<width i→Bool→Public S h W k attempts} {m : Memory w}

/-- A terminated source has an even code. Dividing by two returns the same fixed
per-site ordinal used to reserve its physical seat in the terminal matcher. -/
theorem original_bound (port : Bool→Public S h W k attempts) (side : Bool) :
    ProtocolRAMTurnOperands.printed S false port side false < 2*roles := by
  let a := port (if name (site S (port false))<name (site S (port true)) then side else !side)
  have valid : HistoryRoles.code S a<roles := code_bound S a
  change 2*HistoryRoles.code S a+0<2*roles
  omega

def chartData (site half : Bank) : Data :=
  ⟨b.forwardSite false,b.forwardSite true,b.widthBank,site,b.oldRole false,b.oldRole true,half⟩

theorem original_code (auth : Board.LiveReads S b old width before after m) (site half : Bank)
    (i : Fin b.old) (on : 0<old i) (side : Bool) (room : 2*roles≤2^w) :
    let v:=captured (chartData b site half) m
    (if side then v.targetRole else v.sourceRole) i.val=ProtocolRAMTurnOperands.printed S false (before i on) side false := by
  have fit := (original_bound S (before i on) side).trans_le room
  have physical := (auth.oldRole i on side).trans (ProtocolRAMTurnOperands.actual_word S false (before i on) side false)
  have read := (congrArg Fin.val physical).trans (Fin.val_cast_of_lt fit)
  cases side <;> exact read

theorem width_at (auth : Board.LiveReads S b old width before after m) (site half : Bank) (i : Fin b.old) :
    (captured (chartData b site half) m).width i.val=old i := auth.width i

theorem source_at (auth : Board.LiveReads S b old width before after m) (site half : Bank) (i : Fin b.old) (on : 0<old i)
    (side : Bool) (room : siteLast h (2^W) k+1≤2^w) :
    let v:=captured (chartData b site half) m
    (if side then v.rawTarget else v.rawSource) i.val=(name (HistoryRoles.site S (before i on side))).val := by
  have r := raw_site S b auth i on side room
  cases side <;> exact r

theorem captured_live (auth : Board.LiveReads S b old width before after m) (site half : Bank)
    (room : 2*roles≤2^w) (decode : ∀j,j<2*roles→half.read m (j:Word w)=((j/2:ℕ):Word w))
    (u : Geometry) (valid : u.item<b.old) (on : 0<(captured (chartData b site half) m).width u.item) :
    (chartData b site half).At (captured (chartData b site half) m) m u := by
  let i : Fin b.old := ⟨u.item,valid⟩
  have live : 0 < old i := by
    rw [← width_at S b auth site half i]
    exact on
  apply captured_at (chartData b site half) m u roles decode
  · exact (original_code S b auth site half i live false room).trans_lt (original_bound S (before i live) false)
  · exact (original_code S b auth site half i live true room).trans_lt (original_bound S (before i live) true)

end Hierarchy.ProtocolRAMTurnSnapshot
end

end OAI
