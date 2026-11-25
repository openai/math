import OAI.Hierarchy.DescentResetPublicWordLookup
import OAI.Hierarchy.DescentResetNativeLocalBefore
import OAI.Hierarchy.DescentResetTrunkMeta

namespace OAI
/-! # The compact CPU results are the original trunk and direct parent ordinals -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentResetLocalRoster DescentResetCompactParent
open DescentResetParentCodec DescentResetPublicParentWord DescentDenseHostOrder DescentResetWireTags
open DescentSIMDLookup
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "R" => (Z).placement
local notation "Y" => 2^(Z).n
local notation "r" => (Z).k-(T).commonDepth
local notation "H" => input.placement.degree+2
local notation "L" => (2^(S.groupWidth k tail i+k-(T).commonDepth)+1)*H*2^k
local notation "Ht" => GroupStage.depthBound D n f g
local notation "K" => max Y (2^Ht)
local notation "P₀" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(Ht+1))
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k

def publicShape : DescentResetPublicParentWord.Shape:=⟨H,r,Y,L,input.placement.cap,K,P₀⟩
local notation "s" => publicShape B

theorem site_from_ticket (u : Host) (v : (R).Site) :
    attach s (haloDigit B u ((Z).rootVertex T v)) ((Z).rootTicket T v)=siteWord B u v:=by cases v <;>rfl

/-- The optional terminal port and both dyadic digits come from the fixed
receiver shape. Either tagged copy of the same trunk gives the same ticket. -/
theorem trunk_receiver_ticket (u : Host) (t : (Z).Fallback)
    (touch : (blocks B).src (trunkParent B t)=u ∨ (blocks B).dst (trunkParent B t)=u) :
    lookupTrunk (Z).graph r Ht (localRank (Z).graph r Ht ((Z).localShape T u.1.2)).val=
      some ((Z).rootTicket T (.inr t)):=by
  rw [lookup_trunk]
  let e:=trunkParent B t
  let birth:=DescentOrderedReset.grains W B.count B.order
  let coarse:=(Z).orderedReentry T birth
  have old:=trunk_host_words B t
  have placementSrc :
      ((blocks B).src e).1.2.val=(Z).commonName T (coarse.graph.src e):=by
    exact congrArg (fun x : Host=>x.1.2.val) (named_home B (coarse.graph.src e))
  have placementDst :
      ((blocks B).dst e).1.2.val=(Z).commonName T (coarse.graph.dst e):=by
    exact congrArg (fun x : Host=>x.1.2.val) (named_home B (coarse.graph.dst e))
  have check (side : Bool) : trunkTicket (Z).graph r
      (shape (Z).graph (.trunk side (DescentRelativeContacts.shortName (T).commonDepth ((T).code t))))=
        some ((Z).rootTicket T (.inr t)):=by
    dsimp only [trunkTicket,shape]
    split
    · rfl
    · rename_i absent
      exact (absent ((Z).fallLabel T t).property).elim
  change trunkTicket (Z).graph r (shape (Z).graph u.1.2.val)=_
  rcases touch with h₁|h₂
  · rw [←h₁,placementSrc,old.1.1];exact check false
  · rw [←h₂,placementDst,old.1.2];exact check true

theorem trunk_word (u : Host) (t : (Z).Fallback)
    (touch : (blocks B).src (trunkParent B t)=u ∨ (blocks B).dst (trunkParent B t)=u) :
    trunkWord (Z).graph H r L input.placement.cap K P₀ Ht 1 (zeroCoarse B u).toNat
      (haloNumber B u (receiverRoot B u).1) (localRank (Z).graph r Ht ((Z).localShape T u.1.2)).val=
      number (zeroCoarse B u) (nativeWord B u (trunkParent B t)):=by
  have same:=trunk_center_host B u t touch
  have rank : haloNumber B u (receiverRoot B u).1<H:=(haloDigit B u _).isLt
  rw [trunkWord,ite_eq_right (by decide : 1≠0),dite_eq_left rank,trunk_receiver_ticket B u t touch]
  change number (decide ((zeroCoarse B u).toNat≠0))
    (parent s (attach s (haloDigit B u (receiverRoot B u).1) ((Z).rootTicket T (.inr t))) none)=_
  rw [←same,show attach s (haloDigit B u ((T).code t).1) ((Z).rootTicket T (.inr t))=siteWord B u (.inr t) from site_from_ticket B u (.inr t)]
  simp only [nativeWord,trunkParent,Equiv.apply_symm_apply,namedWord]
  cases zeroCoarse B u <;> rfl

def directPayload (c : (R).Contact) : ℕ :=
  send s Ht ((Z).rootTicket T ((R).owner false c)) ⟨_,(Z).contactSlotWord_lt T false c⟩

theorem socket_from_payload (c : (R).Contact) :
    (if (Z).contactSlotWord T false c<Y then (Z).contactSlotWord T false c else (Z).contactSlotWord T false c-Y)=(directDigit B c).val:=by
  cases c with
  | inl p=>
    rw [ite_eq_left (show (Z).contactSlotWord T false (.inl p)<Y from ((R).outputName (T).commonDepth false p).2.isLt)]
    rfl
  | inr p=>
    let digit := (DescentResetCableSlots.leaf (R) Ht (T).bookHeight false
      (DescentChosenRouter.fallEnd (R) false p) (DescentChosenRouter.fallLeg (R) false p)).val
    have strip (y j : ℕ) : (if y+j<y then y+j else y+j-y)=j := by
      rw [ite_eq_right (Nat.not_lt_of_ge (Nat.le_add_right _ _))]
      omega
    exact strip Y digit

theorem contact_word (u : Host) (c : (R).Contact) :
    directWord s Ht 1 (zeroCoarse B u).toNat
      (haloNumber B u ((Z).rootVertex T ((R).owner false c))) (directPayload B c)=
      number (zeroCoarse B u) (nativeWord B u (contactParent B c)):=by
  let own:=(R).owner false c
  let p : Fin (Y+2^Ht):=⟨_,(Z).contactSlotWord_lt T false c⟩
  apply (direct_read s Ht (haloDigit B u ((Z).rootVertex T own)) (zeroCoarse B u)
    ((Z).rootTicket T own) p (directDigit B c) (socket_from_payload B c)).trans
  have atSite := site_from_ticket B u own
  rw [atSite]
  simp only [nativeWord,contactParent,Equiv.apply_symm_apply,namedWord,parent,own,Option.elim]
  rfl

theorem public_word_room {u : Host} (p) :
    number (zeroCoarse B u) (nativeWord B u p)<2^(Packed.bits (s).count):=
  (number_lt _ _).trans_le ((Nat.le_succ (s).count).trans (Nat.le_pow_clog (by decide) ((s).count+1)))

/-- The finite word found by either of the four-source CPU programs retains
the genuine, unpacked original number even at the largest allowed socket. -/
theorem public_stored {u : Host} (p) (wrote : ℕ) (named : wrote=number (zeroCoarse B u) (nativeWord B u p)) :
    (wrote:Cell (Packed.bits (s).count)).val=number (zeroCoarse B u) (nativeWord B u p):=by
  rw [named,Fin.val_cast_of_lt (public_word_room B p)]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
