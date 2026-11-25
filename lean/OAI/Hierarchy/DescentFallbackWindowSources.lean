import OAI.Hierarchy.DescentFallbackPacket
import OAI.Hierarchy.DescentFallbackPeriodRun
import OAI.Hierarchy.DescentPackedIssuedBookRank

namespace OAI
/-! # Packed window inputs from the previous signed wire, peer stencil and scalar census -/
namespace Hierarchy.DescentFallbackPeriod
open DescentSIMDLookup DescentSharedBookScan DescentSharedCableNames.Stage
open scoped Classical Fin.CommRing
noncomputable section
variable {r n D cap L field H G : ℕ}

variable (own : Fin H→Fin G→Fin L→ℕ) (roster : Fin H→Fin D→Option (Fin H))
    (signs : Fin H→Fin G→Fin L→Fin (2*cap)→Option (Live D cap)) (rank : Fin H→Fin (width r (2^n) D)→ℕ)
    (h : Fin H) (g : Fin G)
local notation "pkt" => inputs (field:=field) own roster signs rank h g

theorem own_read (i : Fin L) (fit : own h g i<2^field) : localWord pkt i=own h g i := by
  exact Fin.val_cast_of_lt fit

theorem rank_read (p : Fields r (2^n) D) (fit : rank h (fieldId p)<2^field) :
    score pkt p=rank h (fieldId p) := by exact Fin.val_cast_of_lt fit

theorem arrival_read (side : Bool) (i : Fin L) (s : Fin (2*cap))
    (fit : ∀t,own t g i+1<2^field) (bits : DescentSignedCableCodec.width D cap≤field) :
    arrival pkt side i s=(signs h g i s).bind (fun z=>if z.target=side then
      (roster h z.neighbor).map (fun t=>(z.neighbor,own t g i)) else none) := by
  have legal:=(DescentSignedCableCodec.encode (signs h g i s)).isLt.trans_le
    (Nat.pow_le_pow_right (by decide) bits)
  have source : signed pkt i s=signs h g i s := by
    simp only [signed,inputs,Fin.val_cast_of_lt legal,Fin.cast_val_eq_self,DescentSignedCableCodec.decode_encode]
  rw [arrival,source]
  cases mark : signs h g i s with
  | none=>rfl
  | some z=>
    simp only [Option.bind_some]
    by_cases go : z.target=side
    · simp only [ite_eq_left go]
      cases link : roster h z.neighbor with
      | none=>simp [peer,inputs,link]
      | some t=>
        have measured : peer pkt z.neighbor i = own t g i+1 := by
          change ((roster h z.neighbor).elim 0 (fun v=>(own v g i : Cell field)+1)).val = _
          rw [link]
          simpa only [Option.elim_some, Nat.cast_add, Nat.cast_one] using Fin.val_cast_of_lt (fit t)
        simp [go,measured]
    · simp [go]

end
end Hierarchy.DescentFallbackPeriod

end OAI
