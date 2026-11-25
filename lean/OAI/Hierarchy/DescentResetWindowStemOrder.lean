import OAI.Hierarchy.DescentClosedStemRoster
import OAI.Hierarchy.DescentInstalledPublicHeader
import OAI.Hierarchy.DescentPackedTicketChronology
import OAI.Hierarchy.DescentIssuedChronology
import OAI.Hierarchy.DescentResetStemCompactOrder

namespace OAI
/-! # Authentic chronological order on two same-polarity old reset stems -/
noncomputable section
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentOrderedReset DescentPacking
open DescentPackedTicketChronology DescentIssuedFallbackPanel DescentGL DescentResetAttachments
open scoped Classical BigOperators
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "identifier" => (Z).installedResetOrdinal T vertexCode birth
local notation "signedOrder" => input.order.trans Fin.valEmbedding
local notation "prior" => DescentOrderedReset.grains W (A).grainCount input.order
local notation "E" => Stage.Grain A
local notation "End" => (old).graph.Edge
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation "fits" => B.frame.enough.trans (Nat.sub_le ..)

theorem beforeStem_code (x : End) : (birth x).val=(prior (beforeStem B x)).val := by
  obtain ⟨e,j⟩:=x
  change DescentOrderedWords.offset B.order B.count e+j.val=
    DescentOrderedWords.offset input.order (A).grainCount e+j.val
  apply congrArg (·+j.val)
  rw [B.order_eq,B.count_eq]

theorem stem_ordinal (s : Bool) (x : End) :
    (identifier (stemParent B (s,x))).val=(prior (beforeStem B x)).val+
      (∑e,B.count e)*(finTwoEquiv.symm s).val := by
  have ordField :=congrArg Prod.fst ((Z).stemArchive T vertexCode birth s x)
  exact ordField.trans (congrArg (·+_) (beforeStem_code B x))

/-- Compare the two genuine rows using the previous source, its outgoing
signed edge slot and the within-edge grain ordinal. -/
def stemPrior (x y : E) : Prop :=
  DescentPackedTicketChronology.before
    (originalId W.graph.Site (W.graph.src x.1)) (outgoingSlot A S input.valid input.order x).val x.2.val
    (originalId W.graph.Site (W.graph.src y.1)) (outgoingSlot A S input.valid input.order y).val y.2.val

theorem stem_before (sorted : SourceSorted W input.order) (s : Bool) (x y : End) :
    (identifier (stemParent B (s,x))).val<(identifier (stemParent B (s,y))).val ↔
    stemPrior (input:=input) (beforeStem B x) (beforeStem B y) := by
  rw [stem_ordinal B s x,stem_ordinal B s y,Nat.add_lt_add_iff_right]
  exact actual_before A S input.valid input.order sorted _ _

theorem stem_before_path {W₀ : MarkedWorld F d P bits} {j z₀ D₀ : ℕ}
    {first : Reached W₀ G q ε S k j z₀ D₀ w hist} (path : Chronology.Path first input)
    (ordinary : path.ordinaryOnly) (elapsed : j < i) (s : Bool) (x y : End) :
    (identifier (stemParent B (s,x))).val<(identifier (stemParent B (s,y))).val ↔
    stemPrior (input:=input) (beforeStem B x) (beforeStem B y) :=
  stem_before B (path.ordinary_sorted ordinary elapsed) s x y

/-- A genuine signed predecessor panel per receiver. The range check and
coordinate filters coincide with those used to construct the reset roster. -/
def priorStemPanel (u : Host) (s : Bool) :=
  let v:=B.frame.host.symm (receiverRoot B u).1
  let hi:=(receiverRoot B u).2
  let eligible (e : E):=((A).pos (endSite A s e)).2=v ∧
    group (T).commonDepth (rearrange B.frame.basis (oldBlock digits (Stage.home A (endSite A s e))))=hi.val
  panel A signedOrder S input.valid digits B.frame.basis fits s v hi eligible

def priorStemSlot (s : Bool) (j : End) :
    Fin (2^(S.groupWidth k tail i+k-(T).commonDepth))×Fin (2*(A).cap) :=
  localAddress A signedOrder S input.valid digits B.frame.basis s (beforeStem B j)

theorem priorStemPanel_read (u : Host) (s : Bool) (j : End)
    (atCell : (blocks B).src (stemParent B (s,j))=u ∨ (blocks B).dst (stemParent B (s,j))=u) :
    priorStemPanel B u s (priorStemSlot B s j)=some (beforeStem B j) := by
  apply panel_at _ _ _ _ _ _ _ _ _ _ _ (fun _ valid=>valid)
  exact stem_cell B u s j atCell

theorem stem_before_panel (sorted : SourceSorted W input.order) (u : Host) (s : Bool) (x y : End)
    (atX : (blocks B).src (stemParent B (s,x))=u ∨ (blocks B).dst (stemParent B (s,x))=u)
    (atY : (blocks B).src (stemParent B (s,y))=u ∨ (blocks B).dst (stemParent B (s,y))=u) :
    (priorStemPanel B u s (priorStemSlot B s x)).any (fun a=>
      (priorStemPanel B u s (priorStemSlot B s y)).any (fun b=>decide (stemPrior (input:=input) a b))) =
      decide ((identifier (stemParent B (s,x))).val<(identifier (stemParent B (s,y))).val) := by
  rw [priorStemPanel_read B u s x atX,priorStemPanel_read B u s y atY]
  change decide (stemPrior (input:=input) (beforeStem B x) (beforeStem B y))=_
  exact decide_eq_decide.mpr (stem_before B sorted s x y).symm

open DescentResetStemCompactOrder

def compactStemSource (u : Host) (a : E) : ℕ :=
  sourceDigit A digits B.frame.basis fits input.vertex (B.frame.host.symm (receiverRoot B u).1)
    (receiverRoot B u).2 a

def compactStemBefore (u : Host) (a b : E) : Prop :=
  DescentPackedTicketChronology.before
    (compactStemSource B u a) (outgoingSlot A S input.valid input.order a).val a.2.val
    (compactStemSource B u b) (outgoingSlot A S input.valid input.order b).val b.2.val

theorem compactStem_room (u : Host) (a : E) :
    compactStemSource B u a<(2^(S.groupWidth k tail i+k-(T).commonDepth)+1)*((A).degree+2)*2^k ∧
      (outgoingSlot A S input.valid input.order a).val<(A).cap ∧ a.2.val<(A).cap :=
  ⟨source_room A digits B.frame.basis fits input.vertex _ _ a,(outgoingSlot A S input.valid input.order a).isLt,
    a.2.isLt.trans_le (Stage.grain_room A signedOrder S input.valid a.1)⟩

theorem stem_before_compact (age : 0 < i) (sorted : SourceSorted W input.order)
    (u : Host) (s : Bool) (x y : End)
    (atX : (blocks B).src (stemParent B (s,x))=u ∨ (blocks B).dst (stemParent B (s,x))=u)
    (atY : (blocks B).src (stemParent B (s,y))=u ∨ (blocks B).dst (stemParent B (s,y))=u) :
    (identifier (stemParent B (s,x))).val<(identifier (stemParent B (s,y))).val ↔
      compactStemBefore B u (beforeStem B x) (beforeStem B y) := by
  rw [stem_ordinal B s x,stem_ordinal B s y,Nat.add_lt_add_iff_right]
  exact scope_before A S input.valid digits B.frame.basis fits input.vertex
    (B.frame.host.symm (receiverRoot B u).1) (receiverRoot B u).2 input.valid.coordinates
    (input.siteName age) input.order sorted s (beforeStem B x) (beforeStem B y)
    (stem_cell B u s x atX) (stem_cell B u s y atY)

theorem stem_before_compact_path {W₀ : MarkedWorld F d P bits} {j z₀ D₀ : ℕ}
    {first : Reached W₀ G q ε S k j z₀ D₀ w hist} (path : Chronology.Path first input)
    (ordinary : path.ordinaryOnly) (elapsed : j < i) (u : Host) (s : Bool) (x y : End)
    (atX : (blocks B).src (stemParent B (s,x))=u ∨ (blocks B).dst (stemParent B (s,x))=u)
    (atY : (blocks B).src (stemParent B (s,y))=u ∨ (blocks B).dst (stemParent B (s,y))=u) :
    (priorStemPanel B u s (priorStemSlot B s x)).any (fun a=>
      (priorStemPanel B u s (priorStemSlot B s y)).any (fun b=>decide (compactStemBefore B u a b))) =
      decide ((identifier (stemParent B (s,x))).val<(identifier (stemParent B (s,y))).val) := by
  rw [priorStemPanel_read B u s x atX,priorStemPanel_read B u s y atY]
  change decide (compactStemBefore B u (beforeStem B x) (beforeStem B y))=_
  exact decide_eq_decide.mpr (stem_before_compact B (by omega) (path.ordinary_sorted ordinary elapsed) u s x y atX atY).symm

end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
