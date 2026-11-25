import OAI.Hierarchy.ProtocolRAMDateSpillOffsets
import OAI.Hierarchy.ProbeFixedWideTerminal
import OAI.Hierarchy.ProbeFixedWideDatedAmounts
import OAI.Hierarchy.ProbeFixedWidePacketShape
import OAI.Hierarchy.ProtocolRAMRowChoice

namespace OAI
/-! # Original chronological commodity and paid spill addresses -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.CoreBoard.HistoryRoles
open scoped Classical Fin.CommRing

/-- The role tapes interleave the original and reported flags. Both encode
the same geometric role in the high-order part of the local identifier. -/
def untagRole {D : ℕ} (i : Fin (2*D)) : Fin D :=
  ⟨i.val/2,by have bound:=i.isLt;omega⟩

/-- The physical half-end table contains the local role number. Read the
opposite site from that role in the full dated graph; the individual
summands in the prefix come from the separately dated spill-only graph. -/
def Side.fromSector {D : ℕ} (rows original sites full only bits : ℕ) (stride site role : Bank)
    (ordinal : Expr) : Side D :=
  let here:=Expr.lookup site .row
  let sector:=Expr.lookup role .row
  let entire:=SiteControls.columns (D:=D) original full sites bits stride here
  Side.atRole rows original only sites bits stride here ordinal
    (chooseField (2*D) 0 (fun j=>(entire (untagRole j)).opposite) sector)

theorem Side.fromSector_opposite {D W : ℕ} (rows original sites full only bits : ℕ) (stride site role : Bank)
    (ordinal : Expr) (m : Memory W) (r : Word W) (q : Fin D) (reported : Bool) (room : 2*D≤2^W)
    (seen : role.read m r=((2*q.val+reported.toNat:ℕ):Word W)) :
    ((Side.fromSector (D:=D) rows original sites full only bits stride site role ordinal).opposite).eval m r=
    ((SiteControls.columns original full sites bits stride (.lookup site .row) q).opposite).eval m r := by
  let j : Fin (2*D):=⟨2*q.val+reported.toNat,by have lt:=q.isLt;cases reported<;>simp;omega⟩
  have eqn : untagRole j=q := by
    apply Fin.ext
    change (2*q.val+reported.toNat)/2=q.val
    cases reported<;>simp;omega
  change (chooseField (2*D) 0 _ (.lookup role .row)).eval m r=_
  rw [eval_chooseField (2*D) 0 _ _ m r j (by simpa using room) (by
    change (role.read m r).val=0+j.val
    rw [seen,Fin.val_cast_of_lt (show 2*q.val+reported.toNat<2^W from j.isLt.trans_le room),Nat.zero_add])]
  simp only [eqn]

end Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native CoreBoard AdaptiveProbe
open HistoryRoles RoleProgram StripChart
open scoped Fin.CommRing Classical
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width bits datedROM terminalROM terminalWork : ℕ)
local notation "T" => v.wideTerminal h width bits terminalROM terminalWork
local notation "D" => v.widePacketDegree
local notation "sites" => siteLast h (2^v.W) k+1

/-- The old original role carries its strictly ordered settlement ID.
Paid destinations occupy the first numerical block and have ordinal
exactly equal to their reporter row. Both sides query the *same*
original lower-half coordinate as the endpoint table emitter. -/
def wideSpillOffsetSides (oldStart newStart leftOnly rightOnly : ℕ) :
    DatedSpillOffsets.Side D × DatedSpillOffsets.Side D :=
  let roleBits:=ProtocolRAMPurchaseSampler.bits (sites*D)
  let stride:=RoleROM.bank datedROM sites
  let b:=(T).board
  (DatedSpillOffsets.Side.fromSector b.old b.old sites oldStart leftOnly roleBits stride
      (b.oldSite false) (b.oldRole false) (v.wideRoleID h width bits),
   DatedSpillOffsets.Side.fromSector b.edges b.old sites newStart rightOnly roleBits stride
      (b.newSite false) (b.newRole false) .row)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
