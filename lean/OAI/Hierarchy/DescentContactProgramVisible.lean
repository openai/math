import OAI.Hierarchy.DescentContactMeasuredUnits
import OAI.Hierarchy.DescentCandidateMaskRAM
import OAI.Hierarchy.DescentResetCompactedCandidates

namespace OAI
/-! # The positive directed socket in a reached contact mask is its actual installed cable -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentGL DescentSharedCableNames DescentIssuedFallbackPanel DescentPlainTerminal
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOldContactSender DescentGroupPeerOrder
open DescentContacts DescentDenseHostOrder DescentResetAttachments DescentStageEdgeReceipt DescentHostDirectory
open DescentContactDonorFront DescentContactPreROM DescentOldSenderReturn DescentResetOppositePayload
open DescentContactSenderMass DescentResetLocalRoster DescentResetPublicParentWord
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "R" => (Z).placement
local notation "A" => input.placement
local notation "m" => S.groupWidth k tail i+k
local notation "c" => (T).commonDepth
local notation "L" => 2^(m-c)
local notation "K" => 2*(A).cap
local notation "native" => input.order.trans Fin.valEmbedding
local notation "words" => S.resetInputDigits ctl.base ctl.radix i
local notation "small" => B.frame.enough.trans (Nat.sub_le ..)
local notation "basis" => B.frame.basis
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation:max "center" s:arg a:arg => ((Z).rootVertex T ((R).owner s a),(Z).rootBlock T ((R).owner s a))
local notation:max "senderId" s:arg a:arg => (Z).senderJoint T s a

variable (H M field query cargo base : ℕ) (pad : Fintype.card input.V≤H)
local notation "X" => donorFront B H M field query cargo
local notation "A₀" => (X).sender base
local notation "Y" => 2^(Z).n
local notation "Ht" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "N" => DescentOldContactSender.count (A).degree L (A).cap (Z).n r
local notation "origin" => input.vertex.trans (Fin.castLEEmb pad)
local notation:max "oldActor" u:arg => B.frame.host.symm (receiverRoot B u).1
local notation:max "lane" u:arg => (receiverRoot B u).2
local notation "oldCells" => Fin H→Block c→Fin N→Cell field
variable (setup : (senderDesk B field).Inputs) (xs : Fin H→Block B.terminals.commonDepth→Fin (DescentOldContactSender.count input.placement.degree (2^(S.groupWidth k tail i+k-B.terminals.commonDepth)) input.placement.cap B.reset.n (B.reset.k-B.terminals.commonDepth))→Cell field)
variable (measured : ∀v hi,decode (xs ((input.vertex.trans (Fin.castLEEmb pad)) v) hi)=(senderDesk B field).sample setup v hi)
local notation "locals" => fun side (j : Fin (L*K))=> (A₀).sentValue xs side (finProdFinEquiv.symm j) 0

local notation:max "mass" u:arg j:arg => (Date.values A₀ locals j (origin (oldActor u)) (lane u)).val
local notation:max "wing" j:arg => (donor_query B j).1
local notation:max "edge" a:arg => contactParent B a
local notation:max "atSide" s:arg a:arg => (if s then (blocks B).dst (edge a) else (blocks B).src (edge a))
local notation:max "shapeWord" s:arg a:arg => outputShape (Z).graph ((Z).k-(T).commonDepth) Ht s (senderId s a) ((Z).contactDepth s a)

/-- The receiver's former host and coarse digit plus its finite actor shape recover its full installed address. -/
theorem selected_shape_eq (u : Host) (s : Bool) (a : (R).Contact) (root : receiverRoot B u=center s a) :
    shapeWord s a=relativeShape B u+1 ↔ atSide s a=u := by
  rw [joint_endpoint B s a]
  exact ⟨fun h=>root_shape_injective B ((contact_endpoint_root B a s).trans root.symm) (Nat.add_right_cancel h),
    fun h=>by rw [h]⟩

variable (u : Stage.Host (Fin (S.groupCount (i+1))) B.next.V k) (j : Fin (contactCount B)) {b : ℕ} (x : Fin 9→Cell b)

local notation "origin_" => localOrigin B u (contactShelfIndex B j)

include measured in
/-- The only geometry supplied by the caller is the true equality read on the measured
socket joint and measured height. The socket can be empty or address a different actor on this old host. -/
theorem contact_program_visible
    (flag : 0< mass u j→(x 0).val≠0) (amt : (x 8).val=mass u j)
  (hits : ∀a : (R).Contact, 0< mass u j→ receiverRoot B u=center (wing j) a→
    (donor_query B j).2=senderId (wing j) a→
    ((x 1).val=(x 3).val ∨ (x 2).val=(x 3).val ↔ shapeWord (wing j) a=relativeShape B u+1))
  (wide : L*K<2^field) : DescentCandidateMaskRAM.visible x ↔ (origin_).isSome := by
  constructor
  · rintro ⟨_,amount,loc⟩
    have pos : 0< mass u j:=by simpa only [←amt] using amount
    obtain ⟨a,root,named,arrive⟩:=oriented_mass_live B H M field query cargo base pad setup xs measured u j pos
    obtain ⟨p,found,_⟩:=arrive ((selected_shape_eq B u (wing j) a root).1 ((hits a pos root named).1 loc))
    simp [found]
  · cases found : origin_ with
    | none=>simp
    | some p=>
      intro _
      obtain ⟨a,live,eqn,key⟩:=(contact_shelf_iff B u j p).1 found
      obtain ⟨paid,here⟩:=mass_selected B H M field query cargo base pad setup xs measured u j p found wide
      have pos : 0< mass u j:=by rw [paid];exact p.property.1
      have address:=donor_query_actual B u a live
      rw [key] at address
      have side:=congrArg Prod.fst address
      have root : receiverRoot B u=center (wing j) a:=by rw [side];exact contact_at_root B ⟨a,live.2⟩
      have named : (donor_query B j).2=senderId (wing j) a:=by rw [side];exact congrArg Prod.snd address
      rw [eqn] at here
      exact ⟨flag pos,by rwa [amt],(hits a pos root named).2 ((selected_shape_eq B u (wing j) a root).2 here)⟩

include measured in
/-- Fields four through seven are exactly the three already calculated local ranks and the
single directory self-absence chip. The contact count, incidence, mark and empty branches are derived here. -/
theorem contact_program_meta
    (flag : 0< mass u j→(x 0).val≠0) (amt : (x 8).val=mass u j)
  (hits : ∀a : (R).Contact, 0< mass u j→ receiverRoot B u=center (wing j) a→
    (donor_query B j).2=senderId (wing j) a→
    ((x 1).val=(x 3).val ∨ (x 2).val=(x 3).val ↔ shapeWord (wing j) a=relativeShape B u+1))
  (wide : L*K<2^field)
    (ranks : ∀p,origin_=some p→(x 4).val=localClass B u ((blocks B).src p.val) ∧
      (x 5).val=localClass B u ((blocks B).dst p.val) ∧ (x 6).val=localClass B u u)
    (self : (x 7).val≠0 ↔ u∉Stage.near B.next.placement u) :
    DescentCandidateMaskRAM.render x=DescentResetFieldAssembler.raw b («meta» B u origin_) := by
  have vis:=contact_program_visible B H M field query cargo base pad setup xs measured u j x flag amt hits wide
  cases found : origin_ with
  | none=>
    have quiet : ¬DescentCandidateMaskRAM.visible x:=by simp [found] at vis;exact vis
    simp [DescentCandidateMaskRAM.render,quiet,«meta»]
  | some p=>
    obtain ⟨a,live,eqn,_⟩:=(contact_shelf_iff B u j p).1 found
    obtain ⟨srcRank,dstRank,selfRank⟩:=ranks p found
    have seen : DescentCandidateMaskRAM.visible x:=vis.2 (by simp [found])
    have massAt:=amt.trans (mass_selected B H M field query cargo base pad setup xs measured u j p found wide).1
    have coreMember : p.val ∈ (B.reset.orderedReentry B.terminals (DescentOrderedReset.grains W B.count B.order)).core:=by
      rw [eqn]; exact (contact_units B a (by rw [B.unit,←B.next.grain];exact Nat.mul_pos B.next.placement.unitPos G.base_pos)).2
    simp [DescentCandidateMaskRAM.render,seen,«meta»,srcRank,dstRank,selfRank,propext self,coreMember,massAt]

/-- At an unavailable dense host the actual directory selector blanks field zero.
The remaining eight fields may contain arbitrary data from their own measured branches. -/
theorem contact_program_ghost {U H Res J bits : ℕ} (name : Fin U→Fin Res)
    (src : Fin Res→Fin J→Cell bits) (h : Fin H) (g : Fin J) (out : U≤h.val) (x : Fin 9→Cell bits)
    (real : x 0=DescentResetDenseOperand.dense name src h g) :
    DescentCandidateMaskRAM.render x=DescentResetFieldAssembler.raw bits DescentResetFieldAssembler.Meta.blank := by
  apply DescentCandidateMaskRAM.vacant_or_empty _ (.inl ?_)
  simp [real,DescentResetDenseOperand.dense,Nat.not_lt.mpr out]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
