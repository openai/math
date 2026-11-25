import OAI.Hierarchy.ProbeFixedWidePacketMiddle

namespace OAI
/-! # Both actual strip ballots publish native install and low-carry columns -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open LinearAlgebra.SpectralBooks ChordGraph
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard HistoryRoles
open Strip StripChart StripDirectory CatalogueRows WideCPU WireTelescope
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h width bits : ℕ)
local notation "N" => Stages h (2^v.W)
local notation "P" => v.widePlacement h width
local notation "M" => v.widePacketRoles h
local notation "D" => v.widePacketDegree
local notation "rows" => v.widePacketPhysical h width
local notation "sz" => v.widePacketShelf h
local notation "fs" => v.nativeFormats P h width
local notation "shift" => Fintype.card (Commodity (Fin (2^h)) N k)
local notation "source" => DatedRoleSheets.bank rows
variable (siteROM : ℕ) (siteStride : Bank) (preStart postStart : ℕ)
local notation "beforeWidth" => pageRead (source preStart sz bits 0) siteStride
local notation "beforeOther" => pageRead (source preStart sz bits 2) siteStride

local notation "nb" a => (v.wideBallotShape P h width (.attempt a)).columns+((M*3)*5+(D+D))
local notation "endKeys" a => (nb a)+v.wideBallotParties h a
local notation "middle" => PacketTurns.middleColumns M

def widePacketSheet (a : Attempt) (siteROM : ℕ) (siteStride : Bank) (preStart postStart : ℕ)
    (i : Fin (v.wideBallotParties h a)) : Fin (endKeys a)→Expr :=
  Fin.addCases (v.widePacketBody h width bits a siteROM siteStride preStart postStart i)
    (v.wideSignedSocketKey h width bits a siteROM siteStride preStart i)

theorem wideSheet_body (a : Attempt) (i : Fin (v.wideBallotParties h a)) (f : Fin (nb a)) :
    v.widePacketSheet h width bits a siteROM siteStride preStart postStart i (f.castAdd (v.wideBallotParties h a))=
      v.widePacketBody h width bits a siteROM siteStride preStart postStart i f := by simp [widePacketSheet]

theorem wideSheet_socket (a : Attempt) (i j : Fin (v.wideBallotParties h a)) :
    v.widePacketSheet h width bits a siteROM siteStride preStart postStart i (Fin.natAdd (nb a) j)=
      v.wideSignedSocketKey h width bits a siteROM siteStride preStart i j := by simp [widePacketSheet]

/-- Both strip charts use the same positions for all five installed turn words,
the wanted width of each old neighbor and the earned width of each new one. -/
def widePacketFields (e : Event) (siteROM : ℕ) (siteStride : Bank) (preStart postStart : ℕ) :
    Fields (v.widePacketShape h width e) := by
  cases e with
  | feed _=>exact ⟨Fin.elim0,Fin.elim0,Fin.elim0⟩
  | attempt a=>
    let base:=v.wideFields P h width siteROM (.attempt a)
    exact ⟨base.selected,base.site,fun i=>Fin.addCases
      (v.widePacketSheet h width bits a siteROM siteStride preStart postStart i)
      (v.widePacketMiddle h width a siteROM i)⟩

local notation "fields" => v.widePacketFields h width bits
local notation "base" => v.wideFields P h width siteROM

theorem widePacket_selected (a : Attempt) (i : Fin (v.wideBallotParties h a)) :
    (fields (.attempt a) siteROM siteStride preStart postStart).selected i=(base (.attempt a)).selected i := by
  cases a <;> rfl

theorem widePacket_site (a : Attempt) (i : Fin (v.wideBallotParties h a)) :
    (fields (.attempt a) siteROM siteStride preStart postStart).site i=v.wideBallotSite P h width siteROM a i := by
  cases a <;> rfl

set_option maxHeartbeats 1600000 in
theorem widePacket_sheet (a : Attempt) (i : Fin (v.wideBallotParties h a)) (f : Fin (endKeys a)) :
    (fields (.attempt a) siteROM siteStride preStart postStart).value i (f.castAdd middle)=
      v.widePacketSheet h width bits a siteROM siteStride preStart postStart i f := by
  simp only [widePacketFields]
  exact Fin.addCases_left (m := endKeys a) (n := middle) (motive := fun _ => Expr)
    (left := v.widePacketSheet h width bits a siteROM siteStride preStart postStart i)
    (right := v.widePacketMiddle h width a siteROM i) f

theorem widePacket_middle (a : Attempt) (i : Fin (v.wideBallotParties h a)) (f : Fin middle) :
    (fields (.attempt a) siteROM siteStride preStart postStart).value i (Fin.natAdd (endKeys a) f)=
      v.widePacketMiddle h width a siteROM i f := by
  exact Fin.addCases_right (m := endKeys a) (n := middle) (motive := fun _ => Expr)
    (left := v.widePacketSheet h width bits a siteROM siteStride preStart postStart i)
    (right := v.widePacketMiddle h width a siteROM i) f

theorem widePacket_body (a : Attempt) (i : Fin (v.wideBallotParties h a))
    (f : Fin ((v.wideBallotShape P h width (.attempt a)).columns+((M*3)*5+(D+D)))) :
    (fields (.attempt a) siteROM siteStride preStart postStart).value i ((f.castAdd (v.wideBallotParties h a)).castAdd middle)=
      v.widePacketBody h width bits a siteROM siteStride preStart postStart i f := by
  rw [widePacket_sheet,wideSheet_body]

theorem widePacket_socket (a : Attempt) (i j : Fin (v.wideBallotParties h a)) :
    (fields (.attempt a) siteROM siteStride preStart postStart).value i
      ((Fin.natAdd ((v.wideBallotShape P h width (.attempt a)).columns+((M*3)*5+(D+D))) j).castAdd middle)=
      v.wideSignedSocketKey h width bits a siteROM siteStride preStart i j := by
  rw [widePacket_sheet,wideSheet_socket]

theorem widePacket_base (a : Attempt) (i : Fin (v.wideBallotParties h a))
    (col : Fin (v.wideBallotShape P h width (.attempt a)).columns) :
    (fields (.attempt a) siteROM siteStride preStart postStart).value i (((col.castAdd ((M*3)*5+(D+D))).castAdd (v.wideBallotParties h a)).castAdd middle)=
      (base (.attempt a)).value i col := by
  rw [widePacket_body];exact packetFields_pre _ _ _ col

local notation "oldC" a => (v.wideBallotShape P h width (.attempt a)).columns

theorem widePacket_turn (a : Attempt) (i : Fin (v.wideBallotParties h a)) (f : Fin ((M*3)*5)) :
    (fields (.attempt a) siteROM siteStride preStart postStart).value i (((Fin.natAdd (oldC a) (f.castAdd (D+D))).castAdd (v.wideBallotParties h a)).castAdd middle)=
      v.widePacketGate h width bits a siteROM siteStride postStart i (f.castAdd D) := by
  rw [widePacket_body];exact packetFields_turn _ _ _ f

theorem widePacket_lowBefore (a : Attempt) (i : Fin (v.wideBallotParties h a)) (j : Fin D) :
    (fields (.attempt a) siteROM siteStride preStart postStart).value i
      (((Fin.natAdd (oldC a) (Fin.natAdd ((M*3)*5) (j.castAdd D))).castAdd (v.wideBallotParties h a)).castAdd middle)=
      v.widePacketLowBefore h width bits a siteROM siteStride preStart i j := by
  rw [widePacket_body];exact packetFields_before _ _ _ j

theorem widePacket_lowAfter (a : Attempt) (i : Fin (v.wideBallotParties h a)) (j : Fin D) :
    (fields (.attempt a) siteROM siteStride preStart postStart).value i
      (((Fin.natAdd (oldC a) (Fin.natAdd ((M*3)*5) (Fin.natAdd D j))).castAdd (v.wideBallotParties h a)).castAdd middle)=
      v.widePacketGate h width bits a siteROM siteStride postStart i (Fin.natAdd ((M*3)*5) j) := by
  rw [widePacket_body];exact packetFields_after _ _ _ j

theorem widePacket_low_read (a : Attempt) (i : Fin (v.wideBallotParties h a)) (side : Bool) (q : Fin D) :
    (fields (.attempt a) siteROM siteStride preStart postStart).value i (v.widePacketLowColumn h width a side q)=
      (if side then v.widePacketGate h width bits a siteROM siteStride postStart i (Fin.natAdd ((M*3)*5) q)
       else v.widePacketLowBefore h width bits a siteROM siteStride preStart i q) := by
  cases side
  · have atQ : v.widePacketLowColumn h width a false q=
        (((Fin.natAdd (oldC a) (Fin.natAdd ((M*3)*5) (q.castAdd D))).castAdd (v.wideBallotParties h a)).castAdd middle) :=
      Fin.ext (by simp [widePacketLowColumn,widePacketLowStart,add_assoc])
    simp only [atQ,widePacket_lowBefore,Bool.false_eq_true,ite_false]
  · have atQ : v.widePacketLowColumn h width a true q=
        (((Fin.natAdd (oldC a) (Fin.natAdd ((M*3)*5) (Fin.natAdd D q))).castAdd (v.wideBallotParties h a)).castAdd middle) :=
      Fin.ext (by simp [widePacketLowColumn,widePacketLowStart, Nat.add_assoc, Nat.add_comm])
    simp only [atQ,widePacket_lowAfter,ite_true]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
