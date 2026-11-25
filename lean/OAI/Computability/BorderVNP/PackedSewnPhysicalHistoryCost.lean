import OAI.Computability.BorderVNP.PackedSewnPhysicalOperandCost
import OAI.Computability.BorderVNP.PackedSewnTerminalHistory
import OAI.Computability.BorderVNP.PackedSewnRecordCost

/-! # Charged chronological source of the signed terminal emitter -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.Sewn

open SewnField VPVNP.VerifierNetwork
open private rawFrame oldAmount earlier from OAI.Computability.BorderVNP.PackedSewnTerminalHistory

/-- The saved chronological rows and the previous per-site widths are projections
of the installed terminal state. Only the raw fragments and the new sewing rows
add gates when these two banks are joined. -/
theorem terminalHistory_cubic {Z Geo : Type} [Fintype Z] [Fintype Geo] {s n w rows W : ℕ}
    (previous : Format) (code : Fin s ↪ Fin (2^w)) (raw : Frame Z (Fragment.Pin n w))
    (fit : s+n+1 ≤ rows) (indexWidth : Nat.clog 2 rows ≤ W) (wordWidth : w ≤ W) :
    (terminalHistory (Geo:=Geo) previous code raw).size ≤ raw.size+27000*rows*(W+1)^3 := by
  simpa only [terminalHistory,complete_size,earlier,Frame.initial_size,Nat.zero_add,rawFrame,
    Frame.subst_size] using tape_cubic code (rawFrame (Geo:=Geo) previous raw) (oldAmount previous) fit indexWidth wordWidth

end Packing.Inherited.FrozenTape.Sewn

namespace Packing.SewnField.Grid

open Crossing Inherited FrozenTape TeamContraction Diagonal.ExternalSew Diagonal.ExternalSew.GridHosts
open CellAddressCircuit VPVNP.VerifierNetwork Shortening.PublicCapacity PackedHistoryCircuit.Normalized.SelectedSchedule

variable {R r t pins link inner n V groups copies : ℕ} {E : Type}
    (G : Wiring R r t pins link inner n E) (hV : 0 < V) (count : groups*copies = R+1)
    (hg : 0 < blockWidth (r*n) V) (small : blockWidth (r*n) V ≤ link)
    {σ Geo : Type} [Fintype σ] [Fintype Geo] (shape : Shape) {C k w W : ℕ}
    (F : Fields shape.sites shape.edges (groups*V) C w k w σ) (name : ℕ → ℕ → ℕ)
    (present : Fin shape.edges → σ) (previous : Format) (original : ℕ)

/-- Cost in the actual routing rectangle of the old-cable pass, the six
team/tile fragment slots, their stable merge and the appended chronological
records consumed by the signed terminal packet. -/
theorem terminal_physical_history_cubic (hw : w≤W)
    (logs : Nat.clog 2 (routingRows shape C original ((R+1)*V)) ≤ W) :
    let raw := physicalOperands G hV count hg small F name present
    (Sewn.terminalHistory (Geo:=Geo) previous F.sites raw).size ≤
      1463400*routingRows shape C original ((R+1)*V)*(W+1)^3 := by
  intro raw
  let rows := routingRows shape C original ((R+1)*V)
  have mult : 0 < copies := by
    by_contra! no
    rw [show copies = 0 by omega,Nat.mul_zero] at count
    omega
  have ports : groups*V ≤ (R+1)*V := Nat.mul_le_mul_right V
    ((Nat.le_mul_of_pos_right groups mult).trans_eq count)
  have before : 1+CellAddressCircuit.count shape.sites shape.edges (groups*V) shape.sites ≤ 4*rows := by
    dsimp only [rows,routingRows,CellAddressCircuit.count]
    omega
  have after : 1+CellAddressCircuit.count shape.sites (shape.edges+4*(R+1)*V) ((R+1)*V) shape.sites ≤ 4*rows := by
    dsimp only [rows,routingRows,CellAddressCircuit.count]
    rw [Nat.mul_assoc 4]
    omega
  have addr : Nat.clog 2 (4*rows) ≤ W+2 := by
    apply Nat.clog_le_of_le_pow
    have bound := (Nat.le_pow_clog (by decide : 1<2) rows).trans (Nat.pow_le_pow_right (by decide) logs)
    simpa only [pow_add,pow_two,Nat.reduceMul,Nat.mul_comm 4] using Nat.mul_le_mul_left 4 bound
  have fragment := physicalOperands_cubic G hV count hg small F name present before after (by omega : w ≤ W+2) addr
  have compare : (W+2+1)^3 ≤ 27*(W+1)^3 :=
    (Nat.pow_le_pow_left (by omega : W+2+1≤3*(W+1)) 3).trans_eq (by ring)
  have frag : raw.size ≤ 1436400*rows*(W+1)^3 :=
    fragment.trans ((Nat.mul_le_mul_left (13300*(4*rows)) compare).trans_eq (by ring))
  have tape := Sewn.terminalHistory_cubic (Geo:=Geo) previous F.sites raw
    (Sewn.fragment_slots_le shape C original R V) logs hw
  exact tape.trans ((Nat.add_le_add_right frag _).trans_eq (by change _ = 1463400*rows*(W+1)^3; ring))

end Packing.SewnField.Grid

end BorderVNP
end Computability
end OAI
