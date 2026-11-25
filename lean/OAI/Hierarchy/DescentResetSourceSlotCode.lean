import OAI.Hierarchy.DescentResetParentCodec
import OAI.Hierarchy.DescentRosterOrder

namespace OAI
/-! # Source-slot decoding of the reset cable controller -/
noncomputable section
namespace Hierarchy.DescentResetCompactParent
/-- The installed interval digit is the ordinal among the literal old dyadic
labels. The cast widening its installed address does not affect this digit. -/
def sourceLabel (r : ℕ) (tag : Label r) : ℕ :=
  (DescentRosterOrder.compact ((Function.Embedding.subtype _).trans Nat.pairEquiv.toEmbedding) tag).val

/-- Recover the source's bounded row address from the identical source-oriented
fields already present at either end. Only direct rows have different local
numbers at the two receivers. -/
def sourceSlotFrom {H r Y L cap links program : ℕ} (stems leaves : ℕ) (j : ℕ)
    (row : Word H r Y L cap links program) : ℕ :=
  match row with
  | .inr (.inr (.inl (.inl (_,label),port)))=>
      stems+1+sourceLabel r label*(Y+leaves)+port.val
  | .inr (.inr (.inl (.inr (_,label,leg),port)))=>
      let root:=2^(r+1)+sourceLabel r label*(Y+1)+leg.val
      stems+1+root*(Y+leaves)+(Y+port.val)
  | _=>j

/-- The same gate accepts the measured numeric comparison code. An invalid code
routes to the public empty slot. -/
def sourceSlotCode (H r Y L cap links program stems leaves j missing number : ℕ) : ℕ :=
  (DescentResetParentCodec.seen (H:=H) (r:=r) (Y:=Y) (L:=L) (cap:=cap)
    (links:=links) (program:=program) number).elim missing (fun p=>sourceSlotFrom stems leaves j p.2)

theorem sourceSlotCode_read {H r Y L cap links program : ℕ} (stems leaves j missing : ℕ)
    (zero : Bool) (data : Word H r Y L cap links program) :
    sourceSlotCode H r Y L cap links program stems leaves j missing (DescentResetParentCodec.number zero data)=
      sourceSlotFrom stems leaves j data := by
  simp only [sourceSlotCode,DescentResetParentCodec.read_number,Option.elim_some]
end Hierarchy.DescentResetCompactParent

end

end OAI
