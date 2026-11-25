import OAI.Hierarchy.DescentOldSenderReturn
import OAI.Hierarchy.DescentReachedContactDonor

namespace OAI
/-! # The previous signed sender registers interpreted at each reached reset receiver -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentIssuedFallbackPanel DescentGL
open DescentSIMDLookup DescentPlainTerminal DescentOldSenderReturn
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist b : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
set_option Elab.async false
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "R" => (Z).placement
local notation "m" => S.groupWidth k tail i+k
local notation "c" => (T).commonDepth
local notation "hSlot" => 2^(m-c)
local notation "K" => 2*(A).cap
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "E" => Stage.Grain (A)
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "ready" => input.valid
local notation "before" => input.order.trans Fin.valEmbedding
local notation "words" => S.resetInputDigits ctl.base ctl.radix i
local notation "frame" => B.frame.basis
local notation "small" => B.frame.enough.trans (Nat.sub_le ..)
local notation "here" => donor words frame small
local notation "idx" => address (A) before S ready
local notation "groups" => Function.Embedding.refl (Fin (S.groupCount i))
local notation "vertices" => input.vertex
local notation "oldH" => Fintype.card input.V
local notation:max "oldV" u:arg => B.frame.host.symm (receiverRoot B u).1
local notation:max "oldG" u:arg => (receiverRoot B u).2

def localQuery (s : Bool) (u : Host) (j : Fin (hSlot*K)) :=
  atSlot (A) before S ready s (here (oldV u) (oldG u) (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2

theorem original_query (s : Bool) (u : Host) (j : Fin (hSlot*K)) :
    originalDonor B u s j=(localQuery B s u j).map (priorGrain B).symm := rfl

/-- The measured signed byte used both by the reciprocal sender and the old halo
directory. This is the whole earlier chip, before selection of its socket field. -/
theorem contact_old_signed {H0 : ℕ} (prev : Fintype.card input.V≤H0)
    (u : Host) (s : Bool) (j : Fin (hSlot*K)) (e : (old).graph.Edge) (hit : originalDonor B u s j=some e) :
    let a:=finProdFinEquiv.symm j
    let v:=(vertices).trans (Fin.castLEEmb prev)
    let p:=port (A) s (beforeStem B e)
    previousSigned (b:=b) (A) before S ready groups v words frame small a.1 a.2
      (v (oldV u)) (oldG u)=DescentResetOppositePayload.rectangular (b:=b)
        (A) before S ready groups v p.1.2 (idx p).2 (v p.1.1.2) (groups p.1.1.1) := by
  intro a v p
  rw [original_query] at hit
  obtain ⟨grain,found,same⟩:=Option.map_eq_some_iff.mp hit
  obtain rfl : (priorGrain B).symm grain=e:=same
  have original : beforeStem B ((priorGrain B).symm grain)=grain:=(priorGrain B).apply_symm_apply grain
  have address:=(atSlot_iff (A) before S ready s _ a.2 grain).mp found
  have hsite : p.1=here (oldV u) (oldG u) a.1:=by
    change (port (A) s (beforeStem B ((priorGrain B).symm grain))).1=_
    rw [original];exact congrArg Prod.fst address
  have zone : (idx p).2=a.2:=by
    change (idx (port (A) s (beforeStem B ((priorGrain B).symm grain)))).2=_
    rw [original];exact congrArg Prod.snd address
  rw [zone,hsite]
  rfl

def senderWords (s : Bool) (e : (old).graph.Edge) : Fin 2→ℕ :=
  ![(Z).senderJoint T s ((R).contact e),(Z).contactDepth s ((R).contact e)]

variable (issued : Bool → Fin 2 → Fin (2*input.placement.cap) → Fin (Fintype.card input.V) →
  Block B.terminals.commonDepth → Fin (2^(S.groupWidth k tail i+k-B.terminals.commonDepth)) → Cell b)
local notation:max "atHere" s:arg field:arg u:arg j:arg => issued s field (finProdFinEquiv.symm j).2
  (vertices (oldV u)) (oldG u) (finProdFinEquiv.symm j).1
local notation:max "back" s:arg field:arg lo:arg z:arg => returned (A) before S ready groups vertices words frame small (issued (!s) field) s lo z

/-- The contract for an original sender's first two numeric registers. On reached rows it follows
from `GroupStage.sender_at` and `sender_vacant`, respectively. The value equality includes the
width check for the actual data field. -/
def OldSenderReads : Prop :=
  ∀(side : Bool) (register : Fin 2) (v : input.V) (hi : Block c) (lo : Fin hSlot) (column : Fin K),
    (issued side register column (vertices v) hi lo).val =
      (atSlot (A) before S ready side (here v hi lo) column).elim 0
        (fun e => senderWords B side ((priorGrain B).symm e) register)

variable (seen : OldSenderReads B issued)

include seen in
theorem old_label_at (u : Host) (s : Bool) (j : Fin (hSlot*K)) (field : Fin 2) :
    (atHere s field u j).val=(originalDonor B u s j).elim 0 (fun e=>senderWords B s e field) := by
  rw [original_query]
  have val:=seen s field (oldV u) (oldG u) (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  change _=(localQuery B s u j).elim 0 _ at val
  cases slot : localQuery B s u j <;>simpa only [slot,Option.map_some,Option.map_none,Option.elim_some,Option.elim_none] using val

variable (coded : DescentSignedCableCodec.width input.placement.degree input.placement.cap≤b) (positive : 0<b)

include seen coded positive in
theorem returned_label_at (u : Host) (s : Bool) (j : Fin (hSlot*K)) (e : (old).graph.Edge)
    (stored : originalDonor B u s j=some e) (field : Fin 2) :
    (back s field (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2 (vertices (oldV u)) (oldG u)).val=
      senderWords B (!s) e field := by
  rw [original_query] at stored
  obtain ⟨p,off,eqn⟩:=Option.map_eq_some_iff.mp stored
  obtain rfl : (priorGrain B).symm p=e:=eqn
  let other:=port (A) (!s) p
  let y:=rearrange frame (oldBlock words other.1)
  have hit:=returned_at (A) before S ready groups vertices words frame small coded positive (issued (!s) field) s
    (oldV u) (oldG u) (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2 p off
  have filled:=seen (!s) field other.1.1.2 (high small y) (low y) (idx other).2
  rw [opposite_slot (A) before S ready words frame small s p,Option.elim_some] at filled
  exact (congrArg Fin.val hit).trans filled

include seen coded positive in
theorem left_joint_at (u : Host) (s : Bool) (j : Fin (hSlot*K)) (e : (old).graph.Edge)
    (stored : originalDonor B u s j=some e) :
    (if s then (back s 0 (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2 (vertices (oldV u)) (oldG u)).val
      else (atHere s 0 u j).val)=(Z).senderJoint T false ((R).contact e) := by
  cases s
  · simpa [stored,senderWords] using old_label_at B issued seen u false j 0
  · exact returned_label_at B issued seen coded positive u true j e stored 0

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
