import OAI.Hierarchy.DescentResetPublicParentRead
import OAI.Hierarchy.DescentResetCompactSourceTicket
import OAI.Hierarchy.DescentResetContactShapePayload

namespace OAI
/-! # Active and empty rectangular candidate words on the physical public shelves -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentResetPublicParentWord DescentDenseHostOrder
open DescentResetLocalRoster DescentParallelBase DescentSIMDLookup DescentResetParentCodec
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "R" => B.reset.placement
local notation "Y" => 2^(Z).n
local notation "r" => (Z).k-(T).commonDepth
local notation "Ht" => GroupStage.depthBound D n f g
local notation "pal" => DescentDenseHostOrder.roster (Z).graph r Ht
local notation "s" => publicShape B
local notation "hostCodes" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "old" => W.granular B.count (z*G.b) B.fit

theorem palette_port (u : Host) :
    ((Z).rawHostRank T hostCodes u.1.2).val%(pal).card=(localRank (Z).graph r Ht ((Z).localShape T u.1.2)).val:=by
  rw [(Z).rawHostRank_read T hostCodes u.1.2,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt ((Z).hostFields T hostCodes u.1.2).2.isLt];rfl

/-- This family is total over the original normalized rectangular receiver
and includes zero-width terminal copies and genuinely nonexistent candidates. -/
theorem trunk_raster_word (u : Host) :
    let slot:=trunkCandidate B
    let x:=localOrigin B u slot
    trunkWord (Z).graph (s).halo r (s).span (s).cap (s).sockets (s).program Ht («meta» B u x).live.toNat (zeroCoarse B u).toNat
      (haloNumber B u (receiverRoot B u).1) (((Z).rawHostRank T hostCodes u.1.2).val%(pal).card)=
      x.elim 0 (fun z=>wordNumber B u z.val):=by
  intro slot x
  rw [palette_port B u]
  cases hit : x with
  | none=>rfl
  | some v=>
    obtain ⟨t,same⟩:=at_trunk B v (show localOrigin B u (trunkCandidate B)=some v from hit)
    have touched:=v.property.2
    rw [same] at touched
    change trunkWord _ _ _ _ _ _ _ _ 1 _ _ _=wordNumber B u v.val
    rw [same]
    exact trunk_word B u t touched

theorem actual_contact_grain (u : Host) (c : (R).Contact) (live : active (blocks B) u (contactParent B c)) :
    ∃e : (old).graph.Edge,(R).contact e=c:=by
  have positive : 0<(Z).unit:=by rw [B.unit,←B.next.grain];exact Nat.mul_pos B.next.placement.unitPos G.base_pos
  have mass:=live.1
  rw [(contact_units B c positive).1] at mass
  obtain ⟨e,found⟩:= Classical.choice (Fintype.card_pos_iff.mp mass)
  exact ⟨e,found⟩

/-- The input equations speak solely about the separately available old
sender payroll and the common old-halo rank for a genuine contributing
old grain. They are needed only on physically live candidate cells. -/
theorem contact_raster_word (u : Host) (slot : Fin (contactCount B)) (halo sender : ℕ)
    (atSource : ∀ (c : (R).Contact) (live : active (blocks B) u (contactParent B c)),
      contactDigit B u ⟨c,live⟩=slot → ∀e : (old).graph.Edge,(R).contact e=c →
      halo=haloNumber B u ((Z).rootVertex T ((R).owner false c)) ∧ sender=(Z).senderJoint T false c) :
    let v:=localOrigin B u (contactShelfIndex B slot)
    directWord s Ht («meta» B u v).live.toNat (zeroCoarse B u).toNat halo sender=
      v.elim 0 (fun z=>wordNumber B u z.val):=by
  intro v
  cases hit : v with
  | none=>rfl
  | some a=>
    obtain ⟨c,live,who,key⟩:=(contact_shelf_iff B u slot a).1 hit
    obtain ⟨e,orig⟩:=actual_contact_grain B u c live
    obtain ⟨host,row⟩:=atSource c live key e orig
    change directWord _ _ 1 _ _ _=wordNumber B u a.val
    rw [who,host,row]
    exact contact_word B u c

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
