import OAI.Hierarchy.DescentGoodRotorSlots
import OAI.Hierarchy.DescentInstalledRotorStem
import OAI.Hierarchy.DescentGoodTapStemKey

namespace OAI
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentCompiler DescentColonies
open DescentResetTrunks DescentRotor DescentResetGates DescentChosenRouter DescentRouterBank
open DescentResetAttachments DescentNamedContact DescentPrimitivePalette Chronology Computability.BorderVNP.Crossing
open DescentStageEdgeReceipt ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
open scoped Fin.CommRing
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist n h C f g cut tail : ℕ} {G : PoweredGadget F}
    {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset cap ctl) (hp : 0<p) (pos : 0<B.reset.unit) (whole : p∣B.reset.unit)
local notation "unit" => B.reset.unit/p
local notation "birth" => DescentOrderedReset.grains W B.count B.order

open DescentRotorOperandQueryROM.Shape DescentResetPublicOperandBook DescentResetOperandComponents
variable {field query lanes nodes args grain : ℕ}
local notation "cfg" => publicOperandConfig B field query lanes unit unit nodes args grain
variable (side : Bool) (root : B.reset.placement.Good)
local notation "E" => Cells B.reset.placement side root
local notation "src" => source B.reset.placement side root
local notation "dst" => target B.reset.placement side root
local notation "circuit" => B.reset.circuit side root
local notation "raw_" => W.granular B.count (z*G.b) B.fit
local notation "key" => (Function.Embedding.subtype
  (fun e : (raw_).graph.Edge=>B.reset.placement.owner side (B.reset.placement.contact e)=.inl root)).trans birth
local notation "slot" => publicRotorSlots B side root
local notation "label" => B.reset.goodLabel B.terminals root
local notation "ord" => DescentRotor.Ordered.orderedAddress key src dst B.reset.positive
variable (x : (publicOperandConfig B field query lanes (B.reset.unit/p) (B.reset.unit/p) nodes args grain).Data B.reset.n) (req : Mouth B.reset.n)
local notation:max "prior" e:arg => Config.earlierCount src dst key req e
local notation "fiber" => DescentRotorOperandRanks.At src dst (fun point=>(if req.pin then point.2 else point.1)=req.vertex)

/-- The measured public rotor pages read at their actual old signed rows.
The chronological comparison is the one used in the mounted program. -/
structure GoodTapRows : Prop where
  present : ∀e : E,(cfg).endpoints side label x (slot e)=some (src e,dst e)
  missing : ∀j,(¬∃e : E,slot e=j)→(cfg).endpoints side label x j=none
  earlier : ∀a b : E,DescentFallbackItemSelect.before ((cfg).oldItem x side) (slot a) (slot b)↔key a<key b
  traffic : (cfg).traffic x side label=DescentBaseProfile.matrixOfBundles src dst
  layers : DescentRecordedRotorLayers.layers B.reset.n (cfg).packetWidth (cfg).gain (((cfg).reg x) 0).val=(circuit).layers
  capacity : (((cfg).reg x) 0).val=cap.placement.cap

include hp pos whole in
/-- The occupied fabric tap returns the exact native quartet. Its second
word can come from the next old grain at the same hardware port. -/
theorem good_tap_issued_word (rows : GoodTapRows (p:=p) (field:=field) (query:=query) (lanes:=lanes)
      (nodes:=nodes) (args:=args) (grain:=grain) B side root x)
    (node arg : ℕ) (active : ((cfg).oldConfig.header ((cfg).basic x) 0).val≠0)
    (control : (cfg).rotor.public_selector B.reset.graph (cfg).multiplicity (cfg).grain node arg ((cfg).reg x)=
      some (side,label,req))
    (firstItem : E) (selected : (if req.pin then dst firstItem else src firstItem)=req.vertex ∧
      ((circuit).choose (ord firstItem).1).val=req.layer ∧ (ord firstItem).2.val=req.digit)
    (covered : req.within< min 2 (Fintype.card fiber*unit-(prior firstItem*unit+req.batch))) :
    let start:=prior firstItem*unit+req.batch
    let word:=start+req.within
    let count:=min 2 (Fintype.card fiber*unit-start)
    ∃donor : fiber,prior donor.val=word/unit ∧
      (cfg).mixed B.reset.graph node arg x=some
        (if req.pin then (cfg).rotorContactAt side cap.placement.cap label req.vertex
          else (cfg).oldConfig.stemAt side cap.placement.cap ((cfg).oldItem x side (slot donor.val)),
         if req.pin then word else word%unit,count,req.pin) :=by
  intro start word count
  have positive : 0<unit:=Nat.div_pos (Nat.le_of_dvd pos whole) hp
  have native:=(cfg).public_word B.reset.graph (circuit) key x side label req slot
    rows.present rows.missing rows.earlier rows.traffic rows.layers firstItem selected positive
  have takePresent {P : Prop} [Decidable P] {yes : P → Prop} {no : ¬P → Prop}
      (branch : dite P yes no) (hit : P) : yes hit := by simpa only [dite_eq_left hit] using branch
  obtain ⟨donor,rank,_,value⟩:=takePresent native covered
  refine ⟨donor,rank,?_⟩
  let output (cap₀ : ℕ) : Option (ℕ × ℕ × ℕ × Bool) := some
    (if req.pin then (cfg).rotorContactAt side cap₀ label req.vertex
     else (cfg).oldConfig.stemAt side cap₀ ((cfg).oldItem x side (slot donor.val)),
     if req.pin then word else word%unit,count,req.pin)
  exact ((cfg).public_dispatch B.reset.graph node arg x side label req active control).trans
    (value.trans (congrArg output rows.capacity))

/-- The rank on the original socket itself. This formulation uses the physical
socket recovered by the mounted gate, so it includes both old-port transports. -/
theorem good_tap_stem_rank (leg : req.pin=false) (firstItem donor : E)
    (startsAt : src firstItem=req.vertex) (endsAt : src donor=req.vertex)
    (rawPort : Bool×B.reset.placement.Public) (identity : rawPort=(side,B.reset.placement.input side firstItem.val)) :
    ∃item : DescentNamedContact.Fibre (B.reset.placement.input rawPort.1) rawPort.2,
      item.val=donor.val ∧
      (DescentOrderedWords.before (DescentOrderedReset.fibreKey birth (B.reset.placement.input rawPort.1) rawPort.2) item).card=
        prior donor :=by
  subst rawPort
  obtain ⟨item,proven,rankAt⟩ := DescentResetLaneIssue.source_fibre_rank B.reset.placement.contact B.reset.placement.input B.reset.placement.site
    B.reset.placement.owner B.reset.placement.align side (.inl root)
    (head B.reset.placement side root) (DescentChosenRouter.tail B.reset.placement side root) birth req leg firstItem donor startsAt endsAt
  refine ⟨item,proven,rankAt.trans ?_⟩
  exact congrArg (fun use : Fintype E => @Config.earlierCount E use _ _ src dst key req donor) (Subsingleton.elim _ _)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
