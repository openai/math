import OAI.Computability.BorderVNP.PackedTerminalSignedProducerCost
import OAI.Computability.BorderVNP.PackedTerminalActualPacketCost

/-! # Full gate and output-bit count for the signed terminal packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.TerminalCells

open Cover Crossing Packing Packing.CellAddressCircuit Packing.RoutingOutputs
open VPVNP.VerifierNetwork GeometryFrameEncoding CellPacketGeometry CellPacketGeometry.LiveWords
open CellPacketGeometry.History CellPacketGeometry.History.Native Packing.Inherited.FrozenTape CellSparse.Packet
open Shortening.PublicCapacity Packing.Inherited

variable {Γ Z H Row Payload : Type} [Fintype Γ] [Fintype Z] [Fintype H] [Fintype Row] [Fintype Payload]
  {s m n C d k w L J v cap dh qa : ℕ}
  (F : Fields s m n C d k w (Z ⊕ Bool)) (hk : k ≤ w) (old : Fin J → Fin s)
  (source : Frame Γ (Z ⊕ Bool)) (keep : Frame Γ H) (controls : Fin v → Fin (2^w))
  (S : Schema Row Payload) (boxes : Fin s → List (Source.Box (Fin J))) (arena stride gap desc g digits : ℕ)
  (occupied : Fin m → Z ⊕ Bool) (portUsed : Fin n → Bool)
  (historyTape : Frame ((Z ⊕ Bool) ⊕ H) (Pins Row Payload dh)) (valid : Z ⊕ Bool)
local notation "rows" => 1+CellAddressCircuit.count s m n C+J+n
local notation3 (prettyPrint := false) "feed₀" => Terminal.feeds (s:=⟨s,m⟩) F occupied portUsed boxes historyTape
  (SignedFields.liveFrame F boxes old arena stride gap desc g digits) valid
local notation3 (prettyPrint := false) "lastTape" => FinalTies.tieSchema m n w
local notation3 (prettyPrint := false) "rep₀" => FinalReports.Spare.reports (C:=C) (g:=g) (digits:=digits) (E:=Fin J)
local notation3 (prettyPrint := false) "priv₀" => FinalReports.Spare.priv (C:=C) (g:=g) (digits:=digits) (E:=Fin J)
variable (sh : ∀ r, (S.tags r).length ≤ cap) (th : ∀ r, ((FinalTies.tieSchema m n w).tags r).length ≤ cap)
  (hd : dh ≤ qa) (ht : d ≤ qa) (room : s<2^qa) (croom : C<2^k) (hs : ∀ r, S.width r ≤ w)
  (hl : ∀ r, (FinalTies.tieSchema m n w).width r ≤ w)
local notation3 (prettyPrint := false) "tpl" => template S lastTape boxes sh th priv₀ rep₀
variable (base : Fin (roster s S (FinalTies.tieSchema m n w)).length → Fin (C+1))
  (pointer : Fin J → (template S (FinalTies.tieSchema m n w) boxes sh th
    (FinalReports.Spare.priv (C:=C) (g:=g) (digits:=digits) (E:=Fin J)) FinalReports.Spare.reports).Fields)
  (pad : (roster s S (FinalTies.tieSchema m n w)).length < 2^qa) (dest header : ℕ)
local notation3 (prettyPrint := false) "packet" => (feed₀).ordered S lastTape boxes sh th priv₀ rep₀ hd ht room croom hs hl base pointer pad dest header

variable (fieldSource : Frame ((Z ⊕ Bool) ⊕ H) (FinalReports.Spare.Field C g digits (Fin J) × Fin w))
local notation3 (prettyPrint := false) "feedAny" => Terminal.feeds (s:=⟨s,m⟩) F occupied portUsed boxes historyTape fieldSource valid
local notation3 (prettyPrint := false) "packetAny" => (feedAny).ordered S lastTape boxes sh th priv₀ rep₀ hd ht room croom hs hl base pointer pad dest header

/-- Retaining the tape charges its gates once for any physical report field
frame satisfying the shared scalar bound. -/
theorem retainedReport_bits (bound : Terminal.ReportFieldBound ⟨s,m⟩ n C J d k w g digits fieldSource.size)
    (widths : d ≤ L ∧ k ≤ L ∧ w ≤ L ∧ Nat.clog 2 rows ≤ L)
    (wa : qa ≤ L) (wp : (tpl).publicDepth ≤ L) (wd : (tpl).chunkDepth ≤ L) (wb : (tpl).recordDepth ≤ L)
    (wh : Nat.clog 2 ((roster s S lastTape).length+(C+1)) ≤ L)
    (wl : Nat.clog 2 ((s+1)+(roster s S lastTape).length) ≤ L) :
    let o := Total (tpl).publicDepth (tpl).chunkDepth
    let out := m*3+(RoutingOutputs.count m C J n+((C+(J+C))+(v+o)))
    let emit := Retained.emitter F hk old id (Retained.privateControls F old controls packetAny) source keep
    emit.size+out*w ≤ source.size+keep.size+historyTape.size+
      (10020000*rows+16008100*sourceVolume S lastTape boxes rep₀+v)*(L+1)^3 := by
  let vol := sourceVolume S lastTape boxes rep₀
  intro o out emit
  let view := (packetAny).subst (Frame.initial (Sum.elim id (fun _ : H => Sum.inr false)))
  have routing := full_size_le F hk old (id : Fin n → Fin n) view (R:=rows) le_rfl widths
  have shares : emit.size = source.size+keep.size+(full F hk old id (withPrivateViews F old view)).size := by
    dsimp only [emit]
    rw [Retained.emitter_size,Retained.privateControls_size]
    simp [RoutingOutputs.full,withPrivateViews,view]
    omega
  have viewSize : view.size=(packetAny).size := by simp [view]
  have ordered := (feedAny).ordered_cubic S lastTape boxes sh th priv₀ rep₀ hd ht room croom hs hl base pointer pad dest header
    L widths.2.1 widths.2.2.1 wa wp wd wb wh wl
  have produce := Terminal.reportFeeds_size (s:=⟨s,m⟩) F occupied portUsed boxes historyTape valid S g digits fieldSource bound L widths
  have volume : o ≤ 1280*vol := (tpl).output_linear.trans
    ((Nat.mul_le_mul_left 20 (publicVolume_le_source S lastTape boxes sh th priv₀ rep₀)).trans_eq (by ring))
  have arity : out ≤ 3*rows+v+o := by
    dsimp only [out]
    rw [Nat.mul_comm m 3]
    exact output_count (v:=v) (o:=o) (R:=rows) le_rfl
  have hcube : w ≤ (L+1)^3 := by nlinarith only [widths.2.2.1,Nat.zero_le (L^3),Nat.zero_le (L^2)]
  have bits : out*w ≤ (3*rows+v+1280*vol)*(L+1)^3 :=
    Nat.mul_le_mul (arity.trans (Nat.add_le_add_left volume _)) hcube
  have gateSum : 15000*rows*(L+1)^3+16006010*vol*(L+1)^3+(10000000*rows+100*vol)*(L+1)^3+
      (3*rows+v+1280*vol)*(L+1)^3 ≤ (10020000*rows+16008100*vol+v)*(L+1)^3 := by
    calc
      _ = (10015003*rows+16007390*vol+v)*(L+1)^3 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  change (feedAny).history.size+(feedAny).binding.size+(feedAny).table.size+(feedAny).field.size ≤
    historyTape.size+(10000000*rows+100*vol)*(L+1)^3 at produce
  change (packetAny).size ≤ (feedAny).history.size+(feedAny).binding.size+(feedAny).table.size+(feedAny).field.size+
    16006010*vol*(L+1)^3 at ordered
  change emit.size+out*w ≤ source.size+keep.size+historyTape.size+(10020000*rows+16008100*vol+v)*(L+1)^3
  omega

set_option maxHeartbeats 1400000 in
/-- The actual signed emitter pays for the chronological source, prior
field computation, retained pins, and every physical output bit. It uses the
routing, pointer, binding and report frames on the supplied physical fields,
including when the staged fields have been widened to the terminal word. -/
theorem retainedSigned_bits (widths : d ≤ L ∧ k ≤ L ∧ w ≤ L ∧ Nat.clog 2 rows ≤ L)
    (wa : qa ≤ L) (wp : (tpl).publicDepth ≤ L) (wd : (tpl).chunkDepth ≤ L) (wb : (tpl).recordDepth ≤ L)
    (wh : Nat.clog 2 ((roster s S lastTape).length+(C+1)) ≤ L)
    (wl : Nat.clog 2 ((s+1)+(roster s S lastTape).length) ≤ L) :
    let o := Total (tpl).publicDepth (tpl).chunkDepth
    let out := m*3+(RoutingOutputs.count m C J n+((C+(J+C))+(v+o)))
    let emit := Retained.emitter F hk old id (Retained.privateControls F old controls packet) source keep
    emit.size+out*w ≤ source.size+keep.size+historyTape.size+
      (10020000*rows+16008100*sourceVolume S lastTape boxes rep₀+v)*(L+1)^3 := by
  exact retainedReport_bits F hk old source keep controls S boxes g digits occupied portUsed historyTape valid
    sh th hd ht room croom hs hl base pointer pad dest header
    (SignedFields.liveFrame (H:=H) F boxes old arena stride gap desc g digits)
    (Terminal.signedReportFieldBound (s:=⟨s,m⟩) (H:=H) F boxes old arena stride gap desc g digits) widths wa wp wd wb wh wl

end PackedHistoryCircuit.TerminalCells

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

/-- Convert the actual measured signed packet bound to a single rectangular
polylogarithmic charge. The output word may have the processor's larger power
of the logarithm, while the chronological input retains its compact width. -/
theorem signedEmitter_charge {emit out w hist mult shared R H vol v L : ℕ}
    (A B K v₀ d j t : ℕ) (rpos : 1 ≤ R) (hpos : 1 ≤ H)
    (measured : emit+out*w ≤ shared+(10020000*R+16008100*vol+v)*(L+1)^3)
    (source : shared ≤ (mult-1)*hist+B*R*H^t) (hm : 1 ≤ mult)
    (volume : vol ≤ A*R*H^d) (control : v ≤ v₀) (width : L ≤ K*H^j) :
    hist+emit+out*w ≤ mult*hist+((10020000+16008100*A+v₀)*(K+1)^3+B)*R*H^(max (d+3*j) t) := by
  have hp (i : ℕ) : 1 ≤ H^i := Nat.one_le_pow _ _ hpos
  have rle : R ≤ R*H^d := Nat.le_mul_of_pos_right _ (hp _)
  have c : v ≤ v₀*(R*H^d) := control.trans (Nat.le_mul_of_pos_right _ (rpos.trans rle))
  have lhs : 10020000*R+16008100*vol+v ≤ (10020000+16008100*A+v₀)*R*H^d := by
    calc
      _ ≤ 10020000*(R*H^d)+16008100*(A*R*H^d)+v₀*(R*H^d) :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ rle) (Nat.mul_le_mul_left _ volume)) c
      _ = _ := by ring
  have hi : L+1 ≤ (K+1)*H^j := by rw [Nat.add_mul,Nat.one_mul]; exact Nat.add_le_add width (hp _)
  let coeff := (10020000+16008100*A+v₀)*(K+1)^3
  have rhs : (10020000*R+16008100*vol+v)*(L+1)^3 ≤ coeff*R*H^(d+3*j) := by
    apply (Nat.mul_le_mul lhs (Nat.pow_le_pow_left hi 3)).trans_eq
    dsimp only [coeff]
    rw [pow_add,mul_pow,←pow_mul,Nat.mul_comm j 3]
    ring
  have total := rhs.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hpos (le_max_left (d+3*j) t)))
  have rest := Nat.mul_le_mul_left (B*R) (Nat.pow_le_pow_right hpos (le_max_right (d+3*j) t))
  have counts : hist+(mult-1)*hist=mult*hist := by
    rw [Nat.add_comm,←Nat.succ_mul]
    exact congrArg (·*hist) (by omega)
  change hist+emit+out*w ≤ mult*hist+(coeff+B)*R*H^(max (d+3*j) t)
  rw [Nat.add_mul,Nat.add_mul]
  omega

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
