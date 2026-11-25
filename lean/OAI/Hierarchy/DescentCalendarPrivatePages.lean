import OAI.Hierarchy.DescentCalendarPeerIntake
import OAI.Hierarchy.DescentResetPreparedPeerPages

namespace OAI
/-! # Calendar addresses and widths of the original private root pages -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront.EarlierBanks
open DescentResetLocalRoster ProtocolRAM
noncomputable section
def castTo {d r c n D R C N : ℕ} (hD : d=D) (hR : r=R) (hC : c=C) (hN : n=N)
    (b : EarlierBanks d r c n) : EarlierBanks D R C N := by
  subst D; subst R; subst C; subst N; exact b

theorem cast_actor {d r c n D R C N : ℕ} (hD : d=D) (hR : r=R) (hC : c=C) (hN : n=N)
    (b : EarlierBanks d r c n) :
    (castTo hD hR hC hN b).actorStarts=b.actorStarts ∧ (castTo hD hR hC hN b).actorData=b.actorData ∧
    (castTo hD hR hC hN b).oldRoster=b.oldRoster := by
  subst D; subst R; subst C; subst N
  exact ⟨rfl,rfl,rfl⟩

theorem cast_roots {d r c n D R C N : ℕ} (hD : d=D) (hR : r=R) (hC : c=C) (hN : n=N)
    (b : EarlierBanks d r c n) (s : Bool) (t : Root R (2^N)) :
    (castTo hD hR hC hN b).roots s t=b.roots s (cast (congrArg₂ Root hR.symm
      (congrArg (fun n=>2^n) hN.symm)) t) := by
  subst D; subst R; subst C; subst N
  rfl
end
end Hierarchy.DescentDatedAddressBook.CandidateFront.EarlierBanks

namespace Hierarchy.DescentResetPeerUnionRAM.PeerCatalog
open DescentResetLocalRoster ProtocolRAM
theorem move_page {C A : DescentContactPreROM.Layout} (equal : C=A) (b : Banks C)
    (s : Bool) (t : Root A.residual (2^A.n)) :
    (move equal b).pages s t=b.pages s (cast (congrArg (fun L : DescentContactPreROM.Layout=>
      Root L.residual (2^L.n)) equal.symm) t) := by subst A; rfl
end Hierarchy.DescentResetPeerUnionRAM.PeerCatalog

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook CandidateFront DescentCompiler DescentColonies DescentDenseHostOrder
open DescentPackedPrivateMenu DescentResetPeerUnionRAM DescentPackedColony DescentFallbackPeriod
open DescentSIMDLookup DescentResetLocalRoster ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {b : P→ℕ} {W : MarkedWorld F d P b}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl) (M nextM field metaBits : ℕ) (calendar : List ℕ)
set_option quotPrecheck false
set_option hygiene false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cap" => input.placement.cap
local notation "r" => (Z).k-(T).commonDepth
local notation "Ht" => GroupStage.depthBound D n f g
local notation "phys" => setupFront S ctl.board k tail i D f g M nextM field metaBits C ctl.bitsR calendar
local notation "cap_" => (calendar.take i).prod*256
local notation "width" => fieldBits (Z).graph r Ht (2^r*(2*cap)) (DescentRecordedRotorLayers.width f cap) C (Z).width
variable (paid : cap=cap_)

theorem calendar_residual : r=k := by rw [B.keyWidth,B.commonDepth,Nat.add_sub_cancel_left]

private theorem digits_congr {a b h : ℕ} {G : NonlinearExpanders.Graph a h} {G' : NonlinearExpanders.Graph b h}
    (k n count l C packet : ℕ) (dims : a=b) (boards : HEq G G') :
    fieldBits G k n count l C packet=fieldBits G' k n count l C packet := by
  subst b
  cases eq_of_heq boards
  rfl

include paid in
theorem calendar_private_width : (phys).privateBits=width := by
  change fieldBits ctl.board k Ht (2^k*(2*cap_)) (DescentRecordedRotorLayers.width f cap_) C ctl.bitsR=_
  rw [calendar_residual B,paid,B.width]
  exact (digits_congr k Ht _ _ C ctl.bitsR B.dimension B.graph).symm

variable (floor : ℕ)
  (roots : EarlierBanks input.placement.degree r cap (Z).n)
local notation "old" => EarlierBanks.castTo input.branch (calendar_residual B) paid B.dimension roots
local notation "inputs_" => canonical_peer_inputs B M nextM field metaBits calendar paid floor old

theorem calendar_private_page (s : Bool) (t : (Z).RootTicket T) :
    (inputs_).privatePages s t=roots.roots s t := by
  unfold canonical_peer_inputs
  dsimp only
  erw [PeerCatalog.move_page]
  dsimp only [CandidateFront.originalPages]
  erw [EarlierBanks.cast_roots]
  apply congrArg (roots.roots s)
  exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))

/-- The earlier public page remains a literal source of all private digits after the
three-neighbor scan, both scalar ranking scans, and the trunk palette are installed. -/
theorem retained_private_page {w Q a : ℕ} {H J : ℕ} (start : ℕ) (scene : (phys).Scene)
    (safe : (phys).SceneRoom start scene w) (oldMem : Memory w) (bank : Bank)
    (cells : Fin H→Fin J→Cell a) (bound : bank.Fits w start) (size : H*chunks J Q ≤ bank.size)
    (issued : Reads bank cells Q oldMem) : Reads bank cells Q ((phys).preScalar start scene safe oldMem) := by
  intro j
  rw [(phys).preScalar_lower start scene safe oldMem _ ((Nat.add_lt_add_left ((row H J Q j).isLt.trans_le size) _).trans_le bound.2.2)]
  exact issued j

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
