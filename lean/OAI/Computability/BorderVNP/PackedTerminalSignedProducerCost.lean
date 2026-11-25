import OAI.Computability.BorderVNP.CellPacketGeometrySignedReports
import OAI.Computability.BorderVNP.PackedFinalTieCost

/-! # Gate counts of the genuine signed terminal packet producers -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native.Terminal

open Crossing Shortening.PublicCapacity Packing Packing.Inherited FrozenTape
open CellSparse Packet CellAddressCircuit VPVNP.VerifierNetwork PackedHistoryCircuit.Retained

variable {s : Shape} {n C d k w t entries : ℕ} {Z H R₀ B : Type}
  [Fintype Z] [Fintype H] [Fintype R₀] [Fintype B]
  (F : Fields s.sites s.edges n C d k w Z) (occupied : Fin s.edges → Z) (portUsed : Fin n → Bool)
  (boxes : Fin s.sites → List (Source.Box (Fin entries))) (entry : Fin entries → Fin s.sites)
  (old : Frame (Z ⊕ H) (Pins R₀ B t)) (valid : Z) (S : Schema R₀ B)
  (arena stride gap desc g digits : ℕ)

/-- Uniform size estimate for the cell addresses, scalar report words and
pointers in a terminal report frame. Both physical scalar field orders use
the same bound. -/
def ReportFieldBound (shape : Shape) (n C entries d k w g digits size : ℕ) : Prop :=
  ∀ R W, 1+CellAddressCircuit.count shape.sites shape.edges n C ≤ R → C+entries+1 ≤ R →
    d≤W ∧ k≤W ∧ w≤W ∧ Nat.clog 2 R≤W →
      size ≤ 8000*R*(W+1)^3+(C+C*g*digits)*w*(100*(w+1))+2

variable (fieldSource : Frame (Z ⊕ H) (FinalReports.Spare.Field C g digits (Fin entries) × Fin w))

local notation3 (prettyPrint := false) "feedAny" => feeds (s:=s) F occupied portUsed boxes old fieldSource valid
local notation3 (prettyPrint := false) "feed₀" => feeds (s:=s) F occupied portUsed boxes old
  (SignedFields.liveFrame F boxes entry arena stride gap desc g digits) valid
local notation3 "R₀₀" => 1+CellAddressCircuit.count s.sites s.edges n C+entries+n
local notation3 "report₀" => FinalReports.Spare.reports (C:=C) (g:=g) (digits:=digits) (E:=Fin entries)
local notation3 (prettyPrint := false) "volume₀" => sourceVolume S (FinalTies.tieSchema s.edges n w) boxes report₀

/-- Aggregate gate count for a physical terminal tape with either scalar field order. -/
theorem reportFeeds_size (bound : ReportFieldBound s n C entries d k w g digits fieldSource.size) (W : ℕ) (widths : d≤W ∧ k≤W ∧ w≤W ∧ Nat.clog 2 R₀₀≤W) :
    (feedAny).history.size+(feedAny).binding.size+(feedAny).table.size+(feedAny).field.size ≤
      old.size+(10000000*R₀₀+100*volume₀)*(W+1)^3 := by
  let R := R₀₀
  have base : 1+CellAddressCircuit.count s.sites s.edges n C ≤ R := by dsimp only [R]; omega
  have orig : C+entries+1 ≤ R := by dsimp only [R,CellAddressCircuit.count]; omega
  have second : 1+CellAddressCircuit.count s.sites s.edges n C+CellAddressCircuit.count s.sites s.edges n s.sites ≤ 8*R := by
    dsimp only [R,CellAddressCircuit.count]; omega
  have log : Nat.clog 2 (8*R) ≤ W+3 := by
    apply Nat.clog_le_of_le_pow
    have h := (Nat.le_pow_clog (by decide : 1<2) R).trans (Nat.pow_le_pow_right (by decide) widths.2.2.2)
    simpa only [pow_add,show (2:ℕ)^3=8 by decide,Nat.mul_comm 8] using Nat.mul_le_mul_left 8 h
  have b := FinalTies.terminalTape_cubic (shape:=s) F occupied portUsed second
    (W:=W+3) ⟨by omega,by omega,by omega,log⟩
  have cube : (W+3+1)^3 ≤ 64*(W+1)^3 := (Nat.pow_le_pow_left (by omega : W+3+1≤4*(W+1)) 3).trans_eq (by ring)
  have b' : (FinalTies.terminalTape (s:=s) F occupied portUsed).size ≤ 9472000*R*(W+1)^3 :=
    b.trans ((Nat.mul_le_mul_left (18500*(8*R)) cube).trans_eq (by ring))
  have tb := TerminalTable.bank_cubic F boxes R W base widths
  have fs := bound R W base orig widths
  have words : C+C*g*digits ≤ volume₀ := by rw [FinalReports.Spare.sourceVolume_eq]; omega
  have per : w*(100*(w+1))≤100*(W+1)^3 := by
    calc
      _ ≤ (W+1)*(100*(W+1)) := Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (by omega))
      _ ≤ _ := by nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3)]
  have fields : (C+C*g*digits)*w*(100*(w+1))≤100*volume₀*(W+1)^3 := by
    simpa only [Nat.mul_assoc,Nat.mul_left_comm 100] using Nat.mul_le_mul words per
  have rowPositive : 0 < R := by dsimp only [R]; omega
  have pos : 1 ≤ R*(W+1)^3 := Nat.mul_pos rowPositive (pow_pos (Nat.succ_pos W) 3)
  simp only [feeds,lift_size,Frame.select_size]
  change _ ≤ old.size+(10000000*R+100*volume₀)*(W+1)^3
  simp only [Nat.add_mul,Nat.mul_assoc] at b' tb fs fields ⊢
  omega

/-- Signed subtotal frame on the actual live inputs satisfies the packet field bound. -/
theorem signedReportFieldBound : ReportFieldBound s n C entries d k w g digits
    (SignedFields.liveFrame (H:=H) F boxes entry arena stride gap desc g digits).size := by
  intro R L base orig sizes
  simpa only [SignedFields.liveFrame_size] using
    SignedFields.frame_cubic F boxes entry arena stride gap desc g digits R L base orig sizes

/-- Cost of the actual site-key binding table, absolute-address and stable
box prefix scans, original pointers, and real signed subtotal fields. The
shared chronological frame enters exactly once. -/
theorem signedFeeds_size (W : ℕ) (widths : d≤W ∧ k≤W ∧ w≤W ∧ Nat.clog 2 R₀₀≤W) :
    (feed₀).history.size+(feed₀).binding.size+(feed₀).table.size+(feed₀).field.size ≤
      old.size+(10000000*R₀₀+100*volume₀)*(W+1)^3 := by
  exact reportFeeds_size (s:=s) F occupied portUsed boxes old valid S g digits _
    (signedReportFieldBound F boxes entry arena stride gap desc g digits) W widths

end CellPacketGeometry.History.Native.Terminal

end BorderVNP
end Computability
end OAI
