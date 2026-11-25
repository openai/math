import OAI.Hierarchy.DescentRetainedOriginalDigits
import OAI.Hierarchy.DescentPrimaryTokenCoordinates
import OAI.Hierarchy.DescentRecordedStencilCell

namespace OAI
/-! # Actual predecessor tokens on the reached reset's retained primary -/
namespace Hierarchy.DescentPrimitivePalette
open DescentSixParty DescentSixParty.Chronology DescentSixParty.ResetInput DescentKernelHistory
open DescentCompiler DescentColonies DescentGL DescentResetLocalNodes DescentOrdinaryAtomFieldRAM
open DescentPaidResidentCount.Reset DescentLocalArchiveOrder DescentSIMDLookup DescentIssuedFallbackPanel
open DescentPlainTerminal DescentChosenRouter DescentFallbackShapeTable DescentRelativeContacts
open DescentRetainedControl DescentResetHostSize Reached.NodeCells
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist p : ℕ}
  {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (b : ClosedReset cap ctl) (a : Archive W) (early : Local a.bit)
local notation "A" => cap.placement
local notation "Z" => b.reset
local notation "T" => b.terminals
local notation "dim" => (T).commonDepth
local notation "wide" => S.groupWidth k tail i+k
local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation:max "ix" u:arg => StarKeys.filled W.graph (A).pos (A).block digits u
local notation "oldId" => (A).site cap.vertex cap.valid.coordinates
local notation "small" => b.frame.enough.trans (Nat.sub_le ..)
local notation "roster" => ClosedReset.Recorded.old_roster (reset:=b)
local notation "safe" => (roster).2.2.2.2.2.choose
local notation:max "Node" u:arg => (a.bit.recipe u).Node
variable (mover:DescentRetainedHomeMover.Layout)
local notation "v" => mover.transfer
variable (total:(v).high+(v).low=wide) (axis:(v).cut=dim)
  (blocks:(v).blocks=2^k) (groups:(v).groups=S.groupCount i)
  (size:2^((v).high+(v).low)=(v).groups*(v).blocks) (fits:(v).cut≤(v).high+(v).low)
  (L:DescentGL.Layout ((v).high+(v).low)) (won:HEq L b.frame.basis)
  (room:Fintype.card cap.V≤(v).hosts) (token : NodeOrder.All a.bit→Cell (v).bits)
  (positive:∀u,(token u).val≠0) (nodeRoom:∀u,Fintype.card (Node u)≤(v).previousNodes)
local notation "hl" => congrArg (fun k:ℕ=>2^k) axis
local notation "ll" => congrArg (fun k:ℕ=>2^k) (congrArg₂ Nat.sub total axis)
local notation "coords" => finCongr ll
local notation "name" => cap.vertex.trans (Fin.castLEEmb room)
local notation "old" => previousTokens cap a.bit early (v) blocks groups token
variable (t : (Z).Fallback)
local notation "u₀" => b.frame.host.symm ((T).code t).1
local notation "carrier" => name u₀
local notation "hi" => (Z).rootBlock T (.inr t)
local notation "coarse" => (hi).cast (hl).symm
local notation:max "source" lo:arg => (rearrange b.frame.basis).symm (join small hi lo)
local notation:max "rail" lo:arg => (rearrange L).symm (join fits coarse ((coords).symm lo))
local notation:max "pos" lo:arg => (finProdFinEquiv.symm (Fin.cast size (rail lo)):Fin (v).groups×Fin (v).blocks)
local notation:max "census" lo:arg => ∑u:W.graph.Site,if ((A).pos u).2=u₀ ∧ ix u=source lo then Fintype.card (Node u) else 0

include won in
private theorem physical_position (lo : Block (wide-dim)) :
    ((pos lo).1.cast groups,(pos lo).2.cast blocks)=digits (source lo):=by
  have wholeHigh:(coarse).cast hl=hi:=Fin.ext rfl
  have wholeLow:((coords).symm lo).cast ll=lo:=Fin.ext rfl
  simpa only [wholeHigh,wholeLow] using
    moved_position S ctl.base ctl.radix total groups blocks size fits L axis b.frame.basis won small coarse ((coords).symm lo)

include won in
private theorem physical_input (lo:Block (wide-dim)) :
    let address:=digits (source lo)
    old (pos lo).2 carrier (pos lo).1=old (address.2.cast blocks.symm) carrier (address.1.cast groups.symm):=by
  intro address
  have split:=physical_position b mover total axis blocks groups size fits L won t lo
  have left: (pos lo).2=address.2.cast blocks.symm:=by
    apply Fin.ext
    exact congrArg (fun y=>y.2.val) split
  have right:(pos lo).1=address.1.cast groups.symm:=by
    apply Fin.ext
    exact congrArg (fun y=>y.1.val) split
  rw [left,right]

local notation "code" => cell ((Z).k-dim) (shortName dim ((T).code t)).2
variable (word:Block (wide-dim)→ℕ) (shape:Fin mover.shapes)
  (which:Fin mover.shapes→Option ℕ) (Y:Fin (v).hosts→Fin (v).grouped→Cell mover.control.rootWidth)
local notation "aa" => fun j : Fin (v).donors=>decide (word (coords j)/2=code)
local notation "cmp" => fun j l : Fin (v).donors=>decide (source (coords j)<source (coords l))
variable (sensed:filter (D:=mover.degree) (L:=(v).donors) (cap:=mover.cap)
  (which shape) (Y carrier coarse)=vector aa cmp)
variable (stencil:∀lo,word lo/2=DescentPlainTerminal.Suffix.Stencil.shapeCode (wide-dim)
  (2^(Z).n) (DescentPlainTerminal.Suffix.fieldsRelative dim (ClosedReset.Recorded.originalCell (reset:=b) u₀ (source lo))))
local notation:max "out" nx:arg => mover.targetInputs which Y (mover.oldStrips size fits L old) (finProdFinEquiv (nx,shape)) carrier coarse
local notation "oldRank" => fun u : DescentNamedContact.Fibre (T).home t =>(early u.val).toEmbedding.trans Fin.valEmbedding
local notation "ticket" => ((Z).homeTicket T oldId t).trans Fin.valEmbedding

include won positive in
private theorem census_read (lo : Block (wide-dim)) (j : Fin (v).previousNodes) :
    (ScalarOperand.take j (old (pos lo).2 carrier (pos lo).1)).val≠0 ↔ j.val<census lo:=by
  rw [physical_input b a early mover total axis blocks groups size fits L won room token t lo]
  exact previous_population cap a.bit early (v) blocks groups token positive room digits u₀ (source lo) j

include won positive nodeRoom sensed stencil in
/-- The routed primitive numeral is literally the preceding archive's numeral at
the original actor, after sorting its actual home fibre. -/
theorem calendar_old_primitive (pivot : DescentNamedContact.Fibre (T).home t) (node : Node pivot.val)
    (nx:Fin (v).nodes) (actual:nx.val=(oldOrder (fun u:DescentNamedContact.Fibre (T).home t=>Node u.val)
      ticket oldRank ⟨pivot,node⟩).val) : out nx=token ⟨pivot.val,node⟩:=by
  let _ : ∀ u : (W.granular b.count (z*G.b) b.fit).graph.Site, Fintype ((a.bit.recipe u).Node) := fun _ => inferInstance
  let j:Fin (v).previousNodes:=(early pivot.val node).castLE (nodeRoom pivot.val)
  let lo:=low (c:=dim) (rearrange b.frame.basis (ix pivot.val))
  have src:=moved_old_original b.frame _ _ _ _ _ _ _ _ _ _ roster t word stencil mover coords shape carrier coarse which Y sensed
    size fits L old (fun u=>Node u) oldId (GroupStage.scheduled_site_order S A ctl.base ctl.radix cap.vertex cap.valid.coordinates)
    early (fun l=>population_bound cap a.bit (v) digits u₀ (source l) nodeRoom)
    (census_read b a early mover total axis blocks groups size fits L won room token positive t)
    pivot node j rfl nx actual
  refine src.trans ?_
  refine (congrArg (fun val => ScalarOperand.take (a:=(v).bits) j val)
    (physical_input b a early mover total axis blocks groups size fits L won room token t lo)).trans ?_
  have orig:=old_home_digit b.frame t pivot
  have host:=b.frame.homeHost pivot.val
  rw [pivot.property] at host
  have hhost:((A).pos pivot.val).2=u₀:=(Equiv.eq_symm_apply _).mpr host.symm
  refine (congrArg₂ (fun (address : Block wide) (actor : cap.V) => ScalarOperand.take (a:=(v).bits) j
    (old ((digits address).2.cast blocks.symm) (name actor) ((digits address).1.cast groups.symm))) orig.symm hhost.symm).trans ?_
  exact previous_at_original cap a.bit early (v) blocks groups token room digits pivot.val node j rfl

include won positive nodeRoom sensed stencil in
theorem calendar_old_padding (nx:Fin (v).nodes)
    (absent:(∑u:DescentNamedContact.Fibre (T).home t,Fintype.card (Node u.val))≤nx.val) : out nx=0:=by
  let _ : ∀ u : (W.granular b.count (z*G.b) b.fit).graph.Site, Fintype ((a.bit.recipe u).Node) := fun _ => inferInstance
  exact moved_old_padding b.frame _ _ _ _ _ _ _ _ _ _ roster t word stencil mover coords shape carrier coarse which Y sensed
    size fits L old (fun u=>Node u) (fun l=>population_bound cap a.bit (v) digits u₀ (source l) nodeRoom)
    (census_read b a early mover total axis blocks groups size fits L won room token positive t) nx absent

end
end Hierarchy.DescentPrimitivePalette

end OAI
