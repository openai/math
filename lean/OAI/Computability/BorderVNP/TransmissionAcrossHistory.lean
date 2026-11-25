import OAI.Computability.BorderVNP.TransmissionAcross
import OAI.Computability.BorderVNP.TransmissionHistoryReadback
import OAI.Computability.BorderVNP.TransmissionLegTable

/-! # Delivered words in returned native team histories -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

/-- A successful native relay scan checks both legs of every actual nonlocal descriptor
bit. The quotient is computed from the prefix ordinal in the scheduler output. -/
theorem TableLayout.Image.checked_record {l : TableLayout} {row : ℕ → TableRow}
    {before after : ℕ → ℕ} (im : l.Image row before after) {hR : 2 < l.teams}
    {u z : Fin l.teams} (hd : u ≠ z) {i k : ℕ} (hi : i < l.count) (hk : k < (row i).width)
    (ends : (row i).first = u.val ∧ (row i).second = z.val ∨
      (row i).first = z.val ∧ (row i).second = u.val)
    (pub : Arg → ℕ) (mem : ℕ → ℕ)
    (checked : let v := Routing.relay hR hd (after (l.ordinals+i)+k)
      RelayChecks l.teams (fun x y ↦ l.partnerLength row x v y) pub mem v) :
    let j := after (l.ordinals+i)+k
    RelayWordAgrees pub mem u (Routing.relay hR hd j) z (j/(l.teams-2)) := by
  let j := after (l.ordinals+i)+k
  have hj : j < Routing.demand (l.widthMatrix row) u z := im.recordBit_lt_demand hd hi hk ends
  let bit : Routing.Hop hR (l.widthMatrix row) u (Routing.relay hR hd j) :=
    ⟨z, ⟨j, by simp [Routing.pairBits, hd, hj]⟩⟩
  exact ((relayChecks_iff_hops l row hR _ pub mem).mp checked) u bit

end RoutingISA

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission

variable {R r t d link inner n w header : ℕ} {Edge : Type}
variable {G : Wiring R r t d link inner n Edge} {pin : Fin d → Bool}
variable {ext : Exterior R r link → Bool} {width : Fin (R+1) → Fin (R+1) → ℕ}

/-- The physical peer and ordinal read by the handler on a receiver in register nine. -/
private theorem receiver_regs (b : Range w) (team : Word w) (j : ℕ) (fit : j < 2^w) :
    (b.bitBank team j 9).val = b.teamA.val ∧
    (b.bitBank team j 15).val + (b.bitBank team j 16).val = b.ordinal.val+j := by
  simp only [Range.bitBank, Function.update_self, Function.update_of_ne (by decide : (9 : Reg) ≠ 16),
    Function.update_of_ne (by decide : (15 : Reg) ≠ 16), Fin.val_ofNat, Nat.mod_eq_of_lt fit]
  exact ⟨rfl, rfl⟩

/-- The physical peer and ordinal read by the handler on a sender or shared receiver
in register ten. -/
private theorem sender_regs (a : Range w) (team : Word w) (j : ℕ) (fit : j < 2^w) :
    (a.bitBank team j 10).val = a.teamB.val ∧
    (a.bitBank team j 15).val + (a.bitBank team j 16).val = a.ordinal.val+j := by
  simp only [Range.bitBank, Function.update_self, Function.update_of_ne (by decide : (10 : Reg) ≠ 16),
    Function.update_of_ne (by decide : (15 : Reg) ≠ 16), Fin.val_ofNat, Nat.mod_eq_of_lt fit]
  exact ⟨rfl, rfl⟩

/-- The word in the returned remote consumer's final address equals the literal or
substituted pin word at the sender's original source address. The physical wire
equality follows from the relay test and shared exterior inputs. -/
theorem TransferBank.remote_data {u z : Fin (R+1)} (hd : u ≠ z)
    (sender receiver : TeamHistory w) {i j dst : ℕ}
    (row : i < sender.count) (slot : j < (sender.rows i).width.val)
    (sending : (sender.rows i).selected sender.team = some (some .sendData))
    (receiving : LastWrite receiver.rows receiver.team receiver.count i .receiveB j dst)
    (A : TransferBank G pin ext width w header u) (B : TransferBank G pin ext width w header z)
    (ap : A.pub = sender.pub) (am : A.mem = sender.before i)
    (bp : B.pub = receiver.pub)
    (bm : B.mem = bitMemory receiver.rows receiver.team receiver.pub receiver.initial receiver.bits i .receiveB j)
    (peerA : (sender.rows i).teamB.val = z.val) (peerB : (receiver.rows i).teamA.val = u.val)
    (ord : (sender.rows i).ordinal.val = (receiver.rows i).ordinal.val)
    {h : 2 < R+1} (bound : (sender.rows i).ordinal.val+j < Routing.demand width u z)
    (V : TransferBank G pin ext width w header (Routing.relay h hd ((sender.rows i).ordinal.val+j)))
    (checked : let k := (sender.rows i).ordinal.val+j
      RelayWordAgrees (readings V.pub) (readings V.mem) u (Routing.relay h hd k) z (k/(R+1-2))) :
    receiver.history.val.2.2 dst = sender.before i ((sender.rows i).source.val+j) := by
  have fit := slot.trans (sender.rows i).width.isLt
  have sa := sender_regs (sender.rows i) sender.team j fit
  have rb := receiver_regs (receiver.rows i) receiver.team j fit
  have wire := A.endpoint_eq hd B bound V checked 10 9 _ _ (sa.1.trans peerA) (rb.1.trans peerB)
    sa.2 (rb.2.trans (congrArg (·+j) ord.symm))
  rw [ap, am, bp, bm] at wire
  apply sender.remote_data receiver row slot sending receiving
  unfold TeamHistory.linkWord
  convert wire using 2
  rw [endpointNat_eq]
  simp only [Range.senderAddress, sa.1, sa.2]

/-- The two final consumer cells of a remote shared interval read the same physical
assignment after their relay has checked its two incident legs. -/
theorem TransferBank.remote_shared {u z : Fin (R+1)} (hd : u ≠ z)
    (left right : TeamHistory w) {i j a b : ℕ}
    (toA : LastWrite left.rows left.team left.count i .receiveA j a)
    (toB : LastWrite right.rows right.team right.count i .receiveB j b)
    (A : TransferBank G pin ext width w header u) (B : TransferBank G pin ext width w header z)
    (ap : A.pub = left.pub)
    (am : A.mem = bitMemory left.rows left.team left.pub left.initial left.bits i .receiveA j)
    (bp : B.pub = right.pub)
    (bm : B.mem = bitMemory right.rows right.team right.pub right.initial right.bits i .receiveB j)
    (peerA : (left.rows i).teamB.val = z.val) (peerB : (right.rows i).teamA.val = u.val)
    (ord : (left.rows i).ordinal.val = (right.rows i).ordinal.val)
    {h : 2 < R+1} (bound : (left.rows i).ordinal.val+j < Routing.demand width u z)
    (V : TransferBank G pin ext width w header (Routing.relay h hd ((left.rows i).ordinal.val+j)))
    (checked : let k := (left.rows i).ordinal.val+j
      RelayWordAgrees (readings V.pub) (readings V.mem) u (Routing.relay h hd k) z (k/(R+1-2))) :
    left.history.val.2.2 a = right.history.val.2.2 b := by
  have fit := toA.slot_lt.trans (left.rows i).width.isLt
  have sa := sender_regs (left.rows i) left.team j fit
  have rb := receiver_regs (right.rows i) right.team j fit
  have wire := A.endpoint_eq hd B bound V checked 10 9 _ _ (sa.1.trans peerA) (rb.1.trans peerB)
    sa.2 (rb.2.trans (congrArg (·+j) ord.symm))
  rw [ap, am, bp, bm] at wire
  exact left.remote_shared right toA toB wire

end TeamContraction

end BorderVNP
end Computability
end OAI
