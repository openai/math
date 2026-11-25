import OAI.Hierarchy.ProtocolRAMTurnSnapshotChart
import OAI.Hierarchy.ProtocolRAMTurnOperands
import OAI.Hierarchy.TaggedWireTurnLive

namespace OAI
/-! # Decoding live original and reported catalogue slots from the actual turn-bank memory -/

namespace Hierarchy.ProtocolRAMTurnSnapshot
open Computability.VPVNP.BurstRAM PrivateRAM
open ProtocolRAM ProtocolRAMTurnItinerary AdaptiveProbe ProbeStage CoreBoard HistoryRoles RoleProgram
open scoped Fin.CommRing
variable {h W k attempts w occ : ℕ} (S : PurchaseSampler) (b : Board)
variable {old : Fin b.old→ℕ} {out : Fin b.edges→ℕ} {before : ∀i,0<old i → Bool → Public S h W k attempts} {after : ∀i,0<out i → Bool → Public S h W k attempts}
    {m : Memory w}

private theorem decode {x : Word w} {n : ℕ} (read : x=(n:Word w)) (small : n<2^w) : x.val=n :=
  (congrArg Fin.val read).trans (Fin.val_cast_of_lt small)

theorem original_role (auth : Board.LiveReads S b old out before after m) (key rank : Bank) (i : Fin b.old)
    (on : 0<old i) (side : Bool) (fit : ProtocolRAMTurnOperands.printed S false (before i on) side false<2^w) :
    let v := values (b.itinerary key rank) m
    (if side then v.oldTarget else v.oldSource) i.val=ProtocolRAMTurnOperands.printed S false (before i on) side false := by
  have ready := decode ((auth.oldRole i on side).trans (ProtocolRAMTurnOperands.actual_word S false (before i on) side false)) fit
  cases side <;> exact ready

theorem reported_site (auth : Board.LiveReads S b old out before after m) (key rank : Bank) (i : Fin b.edges)
    (on : 0<out i) (fit : ProtocolRAMTurnOperands.printed S true (after i on) false true<2^w) :
    (values (b.itinerary key rank) m).tailSite i.val=ProtocolRAMTurnOperands.printed S true (after i on) false true :=
  decode ((auth.newSite i on false).trans (ProtocolRAMTurnOperands.actual_word S true (after i on) false true)) fit

theorem reported_role (auth : Board.LiveReads S b old out before after m) (key rank : Bank) (i : Fin b.edges)
    (on : 0<out i) (side : Bool) (fit : ProtocolRAMTurnOperands.printed S true (after i on) side false<2^w) :
    let v := values (b.itinerary key rank) m
    (if side then v.headRole else v.tailRole) i.val=ProtocolRAMTurnOperands.printed S true (after i on) side false := by
  have ready := decode ((auth.newRole i on side).trans (ProtocolRAMTurnOperands.actual_word S true (after i on) side false)) fit
  cases side <;> exact ready

/-- Both numeric endpoint words of this live incurred edge, in the role
compiler's sorted physical order, feed the predecessor walk. -/
theorem reported_ends (auth : Board.LiveReads S b old out before after m) (i : Fin b.edges)
    (on : 0<out i) (lo hi : ℕ)
    (left : ProtocolRAMTurnOperands.printed S true (after i on) false true=lo)
    (right : ProtocolRAMTurnOperands.printed S true (after i on) true true=hi) :
    (b.newSite false).read m (i.val:Word w)=(lo:Word w) ∧
    (b.newSite true).read m (i.val:Word w)=(hi:Word w) := by
  exact ⟨(auth.newSite i on false).trans ((ProtocolRAMTurnOperands.actual_word S true (after i on) false true).trans
      (congrArg (fun z : ℕ=>(z:Word w)) left)),
    (auth.newSite i on true).trans ((ProtocolRAMTurnOperands.actual_word S true (after i on) true true).trans
      (congrArg (fun z : ℕ=>(z:Word w)) right))⟩

theorem key_at (key rank : Bank) (i : Fin occ) (edge : Fin b.edges) (memory : Memory w)
    (words : occ≤2^w) (size : occ≤key.size) (edges : b.edges≤2^w)
    (stored : memory (key.base+i.val)=(edge.val:Word w)) :
    (values (b.itinerary key rank) memory).edge i.val=edge.val := by
  change (memory (key.base+(i.val:Word w).val%key.size)).val=edge.val
  rw [Fin.val_cast_of_lt (i.isLt.trans_le words),Nat.mod_eq_of_lt (i.isLt.trans_le size)]
  exact decode stored (edge.isLt.trans_le edges)

theorem rank_at (key : Bank) (dst bits : ℕ) (i : Fin occ) (start : ℕ) (memory : Memory w)
    (words : 4*occ≤2^w) (size : 4*occ≤2^bits) (small : start<2^w)
    (stored : memory (dst+4*i.val+3)=(start:Word w)) :
    (values (b.itinerary key ⟨dst+3,bits⟩) memory).starts i.val=start := by
  have bound : i.val<occ := i.isLt
  change (memory (dst+3+((4*i.val:ℕ):Word w).val%(2^bits))).val=start
  rw [Fin.val_cast_of_lt (by omega),Nat.mod_eq_of_lt (by omega),show dst+3+4*i.val=dst+4*i.val+3 by omega]
  exact decode stored small

theorem raw_site (auth : Board.LiveReads S b old out before after m) (i : Fin b.old) (hi : 0<old i) (s : Bool)
    (fits : siteLast h (2^W) k+1≤2^w) :
    ((b.forwardSite s).read m (i.val:Word w)).val=(name (HistoryRoles.site S (before i hi s))).val :=
  decode (auth.rawSite i hi s) ((name (HistoryRoles.site S (before i hi s))).isLt.trans_le fits)

end Hierarchy.ProtocolRAMTurnSnapshot

end OAI
