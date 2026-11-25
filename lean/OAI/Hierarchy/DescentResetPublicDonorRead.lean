import OAI.Hierarchy.DescentResetPublicParentPosted
import OAI.Hierarchy.DescentReachedContactDonor

namespace OAI
/-! # True donor selected by a constant public socket on either side -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentResetPublicParentWord DescentDenseHostOrder
open DescentResetLocalRoster DescentResetParentCodec DescentSIMDLookup DescentPackedZip
open DescentContactReceiver DescentContactDonorSelection
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "R" => B.reset.placement
local notation "Ht" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "Y" => 2^(Z).n
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "N" => L*(2*input.placement.cap)
local notation "grp" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin grp) B.next.V k
local notation "half" => rootSlots r Y*(Y+2^Ht)

def donor_query (slot : Fin (contactCount B)) : Bool×ℕ:=
  let row : Fin 2×Fin half:=finProdFinEquiv.symm slot
  (finTwoEquiv row.1,row.2.val+1)

theorem donor_query_actual (u : Host) (c : (R).Contact) (live : active (blocks B) u (contactParent B c)) :
    let j:=contactDigit B u ⟨c,live⟩
    let side:=decide ((blocks B).src (contactParent B c)≠u)
    donor_query B j=(side,(Z).senderJoint T side c):=by
  intro j side
  let root:=(Z).rootTicket T ((R).owner side c)
  let sock:=contactSocket B side c
  have chart : j=finProdFinEquiv (finTwoEquiv.symm side,finProdFinEquiv (rootId r Y root,socketId Y Ht sock)):=rfl
  have amt : (socketId Y Ht sock).val=(Z).contactSlotWord T side c:=by
    cases c with
    | inl a=>exact good_contact_socket B side a
    | inr a=>exact tree_socket _
  rw [chart]
  simp only [donor_query,Equiv.symm_apply_apply,Equiv.apply_symm_apply,finProdFinEquiv_apply_val]
  simp only [ResetInput.senderJoint,send,amt,root,Nat.mul_comm]
  rw [Nat.add_comm ((Z).contactSlotWord T side c) _]

/-- The same finite prior sweep supplies the two numbers consumed by the direct formatting LUT.
The halo has a one-based code on this transport so a real first rank survives the first-live fold. -/
theorem direct_observed {a b : ℕ} (u : Host) (slot : Fin (contactCount B)) (c : (R).Contact)
    (live : active (blocks B) u (contactParent B c)) (key : contactDigit B u ⟨c,live⟩=slot)
    (own : Fin N→Cell a) (ticket halo : Fin N→Cell b)
    (label : ∀j,(own j).val=(originalDonor B u (donor_query B slot).1 j).elim 0
      (fun e=>(Z).senderJoint T (donor_query B slot).1 ((R).contact e)))
    (sent : ∀j e,originalDonor B u (donor_query B slot).1 j=some e→(ticket j).val=(Z).senderJoint T false ((R).contact e))
    (rank : ∀j e,originalDonor B u (donor_query B slot).1 j=some e→(halo j).val=
      haloNumber B u ((Z).rootVertex T ((R).owner false ((R).contact e)))+1)
    (st : ∀v,(Z).senderJoint T false v<2^b)
    (sh : ∀v,haloNumber B u ((Z).rootVertex T ((R).owner false v))+1<2^b) :
    (visits (donor_query B slot).2 own halo).val=haloNumber B u ((Z).rootVertex T ((R).owner false c))+1 ∧
    (visits (donor_query B slot).2 own ticket).val=(Z).senderJoint T false c:=by
  subst slot
  let side:=decide ((blocks B).src (contactParent B c)≠u)
  have chart:=donor_query_actual B u c live
  simp only [chart] at label sent rank ⊢
  have root:=contact_at_root B ⟨c,live.2⟩
  let code (v : (R).Contact):Cell b:=⟨_,sh v⟩
  have pos : code c≠0:=by intro eqn;have val:=congrArg Fin.val eqn;change _+1=0 at val;omega
  exact ⟨congrArg Fin.val (first_sender B u side c root live own halo code label (fun j e h=>Fin.ext (rank j e h)) pos),
    first_left_sender B u side c root live own ticket label sent st⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
