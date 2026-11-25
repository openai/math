import OAI.Hierarchy.DescentProgramArgumentKeys
import OAI.Hierarchy.DescentClosedFreshArgumentKeys

namespace OAI
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentCompiler DescentColonies
open DescentResetTrunks DescentRotor DescentResetGates DescentChosenRouter DescentRouterBank
open DescentResetAttachments DescentNamedContact DescentPrimitivePalette Chronology Computability.BorderVNP.Crossing
open DescentStageEdgeReceipt ThreeFlat.Routing
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist n h C f g cut tail : ℕ} {G : PoweredGadget F}
    {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset cap ctl) (hp : 0<p) (one : 1≤R) (pos : 0<B.reset.unit) (whole : p∣B.reset.unit)
    (wide : max 1 (max B.reset.width (C*B.reset.width))≤R) (a : Archive W) (sh : WorldShape p R a.bit)
local notation "split_" => sh.granular B.count (z*G.b) B.fit hp (B.unit ▸ pos) (B.unit ▸ whole)
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "unit" => B.reset.unit/p
local notation "splitEq" => ((Nat.div_mul_cancel whole).symm : B.reset.unit=unit*p)
local notation "installed" => reentryWorldShape split_ B.reset B.terminals birth _ hp splitEq (resetMenu B) one wide
local notation "next_" => (resetArchive B p hp whole a).bit
local notation "coarse" => B.reset.orderedReentry B.terminals birth

open DescentResetFreshWires DescentResetLocalNodes DescentOrderedWords
local notation "before_" => BitDescription.granular W B.count (z*G.b) B.fit a.bit
local notation "pre_" => (before_).batchedReset B.reset B.terminals birth unit p hp splitEq (resetMenu B)
local notation "middle_" x:arg => NodeOrder.followNames B.reblock pre_ x
local notation "where_" x:arg => resetOrigin B hp whole a x
local notation "dev_" => B.reset.laneShape birth unit p hp splitEq

open DescentLaneGates
local notation "prog_" v:arg => B.reset.laneProgram birth unit p hp splitEq v
local notation "words_" v:arg => fun t : Boundary B.reset.bank v=>boundaryWidth B.reset.bank v t/p
local notation "fit_" v:arg => B.reset.laneWidth_eq unit p splitEq v

/-- The ordered bank installer preserves a wire's word and translates a public
socket through the old fibres in their issued order. -/
def deviceRoute (v : B.reset.bank.Site) (r : BlockRef p (boundaryWidth B.reset.bank v)) :
    (coarse).graph.Edge×ℕ :=
  match r with
  | ⟨.inl edge,word,_⟩=>((motherNames B).symm (.inr (.inr edge.val)),word)
  | ⟨.inr socket,word,fit⟩=>
    let order:=DescentOrderedReset.fibreKey birth (B.reset.placement.input socket.val.1) socket.val.2
    let widths:=fun _ : Fibre (B.reset.placement.input socket.val.1) socket.val.2=>B.reset.unit
    let ref : BlockRef p (boundaryWidth B.reset.bank v):=⟨.inr socket,word,fit⟩
    let picked:=(DescentOrderedWords.address order widths).symm (ref.atBit ⟨0,hp⟩).2
    (stemParent B (socket.val.1,picked.1.val),picked.2.val/p)

theorem device_route_key (x : NodeOrder.All next_) (v : B.reset.bank.Site)
    (u : (prog_ v).Node) (origin : where_ x=.inr (.inr ⟨v,u⟩)) (slot : ℕ)
    (r : BlockRef p (boundaryWidth B.reset.bank v)) (read : ((dev_ v).keys u)[slot]?=some (.inl r)) :
    keyCable installed (middle_ x) slot=some (deviceRoute B hp v r) :=by
  rcases r with ⟨edge|socket,word,fit⟩
  · exact device_installed_wire B hp one pos whole wide a sh x v u origin slot word edge fit read
  · exact device_installed_socket B hp one pos whole wide a sh x v u origin slot word socket fit read

/-- This is the installed reset operand of a formal gate argument at any
covered word, with its full prefix of preceding operands. -/
theorem device_formal_key (x : NodeOrder.All next_) (v : B.reset.bank.Site)
    (u : (prog_ v).Node) (origin : where_ x=.inr (.inr ⟨v,u⟩)) (arg : Fin (((prog_ v).op u).arity))
    (i : Fin ((((prog_ v).op u).arg arg).count (words_ v))) :
    let earlier:=(List.ofFn ((prog_ v).op u).arg).take arg.val
    let slot:=(earlier.map (fun l=>l.count (words_ v))).sum+i.val
    let word:=laneBlock (words_ v) (fit_ v) hp (((prog_ v).op u).arg arg) i
    keyCable installed (middle_ x) slot=some (deviceRoute B hp v word) :=by
  intro earlier slot word
  exact device_route_key B hp one pos whole wide a sh x v u origin slot word
    (program_key_at (words_ v) (fit_ v) hp (prog_ v) u arg i)

/-- An arbitrary in-range device slot selects a genuine lane of this very
node, before reblocking to its new first cable. -/
theorem device_word_cases (x : NodeOrder.All next_) (v : B.reset.bank.Site)
    (u : (prog_ v).Node) (origin : where_ x=.inr (.inr ⟨v,u⟩)) (slot : ℕ)
    (live : slot<((dev_ v).keys u).length) :
    ∃ (left : List (Lane p (boundaryWidth B.reset.bank v))) (l : Lane p (boundaryWidth B.reset.bank v))
      (right : List (Lane p (boundaryWidth B.reset.bank v))) (i : Fin (l.count (words_ v))),
      List.ofFn ((prog_ v).op u).arg=left++l::right ∧ slot=(left.map (fun a=>a.count (words_ v))).sum+i.val ∧
      keyCable installed (middle_ x) slot=some (deviceRoute B hp v (laneBlock (words_ v) (fit_ v) hp l i)) :=by
  obtain ⟨left,l,right,i,cut,index,read⟩:=program_key_cases (words_ v) (fit_ v) hp (prog_ v) u slot live
  exact ⟨left,l,right,i,cut,index,device_route_key B hp one pos whole wide a sh x v u origin slot _ read⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
