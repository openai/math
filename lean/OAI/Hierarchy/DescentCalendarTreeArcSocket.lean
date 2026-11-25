import OAI.Hierarchy.DescentInstalledTreeArc
import OAI.Hierarchy.DescentCalendarPublicSocketField
import OAI.Hierarchy.DescentClosedDeviceArgumentKeys

namespace OAI
/-! # The reached socket of an installed internal fallback operand -/

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open Computability.BorderVNP.Crossing DescentKernelHistory DescentLaneGates DescentBundleHistory DescentChosenRouter
open DescentContactTree DescentRouterSlots DescentTreePrefixIntervals DescentCompiler DescentResetGates
open DescentResetLocalRoster DescentResetCableSlots DescentColonies
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1600000

variable {F P : Type} [Field F] {d : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => (Z).placement
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "ht" => GroupStage.depthBound D n f g
variable {p split : ℕ} (hp : 0 < p) (unitFit : B.reset.unit=split*p)
  (s : Bool) (t : B.reset.Fallback)
  (e : Item B.reset.placement.contact B.reset.placement.owner s (.inr t))
  (b : Fin split) (d₀ : Fin (B.reset.placement.fallbackBook s t).height) (incoming : Bool)
local notation "bk" => (placement).fallbackBook s t
local notation "contact_" => link (placement).contact (placement).owner s (.inr t)
local notation "name_" => DescentFixedNamedContact.code (bk).codes contact_
local notation "leaf" => (bk).codes (contact_ e)
local notation "prefix_" => DescentTreePrefixIntervals.cut (Nat.succ_le_of_lt d₀.isLt) leaf
local notation "wire" => privateWire B (fallOccurrence B s t ⟨d₀,prefix_⟩)
local notation "node" => (⟨treeArcLevel d₀ incoming,prefixAt name_ (treeArcLevel d₀ incoming).val e⟩ : Physical.Site (bk).height)
local notation "venue" => (⟨(s,.inr t),node⟩ : (Z).bank.Site)
local notation "lane_" => treeArcLane (K:=F) (C₀:=C) (k:=B.reset.k) (n:=B.reset.n) (h:=h) (bits:=B.reset.width)
    (u:=B.reset.unit) (N:=∑ x,B.count x) placement (Z).graph (Z).positive (Z).pay (Z).circuit birth d split p hp unitFit s t e b d₀ incoming
local notation "measure" => fun a => boundaryWidth (Z).bank venue a/p
local notation "multiple" => (Z).laneWidth_eq split p unitFit venue
local notation:max "blockRef_" j:arg => laneBlock measure multiple hp lane_ j
local notation "host" => (if incoming then (blocks B).dst wire else (blocks B).src wire)
local notation:max "cfg" fi:arg qu:arg la:arg ba:arg nd:arg ar:arg => flatConfig B fi qu la ba split nd ar
local notation:max "num" fi:arg qu:arg la:arg ba:arg nd:arg ar:arg => (cfg fi qu la ba nd ar).treeAt s incoming input.placement.cap
  (bk).height d₀.val (start ht leaf) ((Z).fallLabel T t,((T).code t).2.2)

/-- A real internal operand word routes to the original private cable. The
physical width bound counts the old items with precisely this child prefix. -/
private theorem tree_arc_ref (r : BlockRef p (boundaryWidth (Z).bank venue))
    (port : Sum.map Subtype.val Subtype.val r.port = .inl (.inr ⟨(s,.inr t),⟨d₀,prefix_⟩⟩)) :
    deviceRoute B hp venue r=(wire,r.block) ∧
      (r.block+1)*p ≤ ∑ _e : Cell name_ (d₀.val+1) prefix_, (Z).unit := by
  rcases r with ⟨edge|socket,word,fit⟩
  · have key : edge.val = .inr ⟨(s,.inr t),⟨d₀,prefix_⟩⟩ := Sum.inl.inj port
    change (word+1)*p ≤ (Z).bank.width edge.val at fit
    rw [key] at fit
    dsimp only [ResetInput.bank,DescentMixedRouter.network,DescentNetworkSubstitution.network,
      DescentChosenRouter.selected,DescentMixedRouter.device,DescentFixedExceptionalRouter.device,
      DescentLocalAdapters.graph,DescentFixedNamedContact.network,DescentFixedNamedContact.paddedTree,
      DescentContactTree.Physical.graph,DescentContactTree.Physical.nodeWidth,DescentRouterSlots.amount] at fit
    refine ⟨?_,fit.trans_eq ?_⟩
    swap
    · exact congrArg (fun inst : Fintype (Cell name_ (d₀.val+1) prefix_) =>
        (@Finset.univ _ inst).sum (fun _ => B.reset.unit)) (Subsingleton.elim _ _)
    change ((motherNames B).symm (.inr (.inr edge.val)),word) = _
    rw [key]
    rfl
  · simp at port

/-- Both the incoming operand at the successor level and the outgoing operand
at the preceding level use the same physical arc. Its published socket names
the original endpoint and retains the exact covered word. -/
def tree_arc_socket (field query lanes batches nodes args : ℕ) (j : Fin ((lane_).count measure)) :
    let word:=(lane_).bundleStart+j.val
    Σ' socket : PublicSocket B host split word true (num field query lanes batches nodes args),
      deviceRoute B hp venue (blockRef_ j)=(wire,word) ∧ socket.face.val=(wire,incoming) := by
  intro word
  have indexAt : prefixAt name_ (d₀.val+1) e=prefix_ := by
    funext ix
    have inside := ix.isLt.trans_le (Nat.succ_le_of_lt d₀.isLt)
    simp [prefixAt,DescentFixedNamedContact.code,DescentTreePrefixIntervals.cut,inside]
    rfl
  have physical := (installed_tree_arc (K:=F) (C₀:=C) (k:=B.reset.k) (n:=B.reset.n) (h:=h) (bits:=B.reset.width)
    (u:=B.reset.unit) (N:=∑ x,B.count x) placement (Z).graph (Z).positive (Z).pay (Z).circuit birth
    d split p hp unitFit s t e b d₀ incoming).1
  rw [indexAt] at physical
  have out := tree_arc_ref B hp s t e d₀ incoming (blockRef_ j) physical
  have positive : 0<split := Fin.pos b
  have count : (word+1)*p ≤ (Fintype.card (Cell name_ (d₀.val+1) prefix_)*split)*p := by
    have upper := out.2
    change (word+1)*p ≤ ∑ _e : Cell name_ (d₀.val+1) prefix_, B.reset.unit at upper
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,unitFit,Nat.mul_assoc] using upper
  have within := (Nat.div_lt_iff_lt_mul positive).2 (Nat.le_of_mul_le_mul_right count hp)
  let socket := reached_tree_socket (field:=field) (query:=query) (lanes:=lanes) (batches:=batches)
    (nodes:=nodes) (args:=args) B s t e d₀ incoming word within
  exact ⟨socket,out.1,rfl⟩

local notation "raw" => DescentFixedExceptionalRouter.device d (placement).contact (placement).input
  (placement).site (placement).owner (fun _ : (W.granular B.count (z*G.b) B.fit).graph.Edge => split*p)
  s (.inr t) (bk).codes
local notation "rawProg" => DescentTreeLaneProgram.program d (placement).contact (placement).input
  (placement).site (placement).owner (placement).align split p hp s (.inr t) (bk).codes birth (2^(Z).n) node
local notation "rawLane" => ((rawProg).op (⟨e,rfl⟩,b)).arg (treeArcPin incoming)
local notation "rowCount" => tree_arc_measure (K:=F) (C₀:=C) (k:=B.reset.k) (n:=B.reset.n) (h:=h) (bits:=B.reset.width)
    (u:=B.reset.unit) (N:=∑ x,B.count x) placement (Z).graph (Z).positive (Z).pay (Z).circuit birth
  d split p hp unitFit s t e b d₀ incoming

/-- Use the literal decoder's local lane index directly. Its printed word is
unchanged by installing that lane in the selected bank. -/
def tree_arc_raw_socket (field query lanes batches nodes args : ℕ)
    (j : Fin ((rawLane).count (fun x => boundaryWidth raw node x/p))) :
    let word:=(rawLane).bundleStart+j.val
    Σ' socket : PublicSocket B host split word true (num field query lanes batches nodes args),
      deviceRoute B hp venue (blockRef_ (j.cast (rowCount).1.symm))=(wire,word) ∧
        socket.face.val=(wire,incoming) := by
  intro word
  let index := j.cast (rowCount).1.symm
  have address : (lane_).bundleStart+index.val=word := congrArg (fun first => first+j.val) (rowCount).2
  let answer (w : ℕ) :=
    Σ' socket : PublicSocket B host split w true (num field query lanes batches nodes args),
      deviceRoute B hp venue (blockRef_ index)=(wire,w) ∧ socket.face.val=(wire,incoming)
  exact Eq.mp (congrArg answer address)
    (tree_arc_socket B hp unitFit s t e b d₀ incoming field query lanes batches nodes args index)

local notation "gate_" => installedTreeGate (K:=F) (C₀:=C) (k:=B.reset.k) (n:=B.reset.n) (h:=h) (bits:=B.reset.width)
    (u:=B.reset.unit) (N:=∑ x,B.count x) placement (Z).graph (Z).positive (Z).pay (Z).circuit birth d split p hp
  unitFit s t node ⟨e,rfl⟩ b

/-- The combined socket and key for the slot selected by the literal two-operand
tree program, including all words of preceding operands. -/
def tree_arc_keyed_socket (field query lanes batches nodes args : ℕ)
    (j : Fin ((rawLane).count (fun x => boundaryWidth raw node x/p))) :
    let word := (rawLane).bundleStart+j.val
    let ref := blockRef_ (j.cast (rowCount).1.symm)
    let earlier := (List.ofFn ((rawProg).op (⟨e,rfl⟩,b)).arg).take (treeArcPin incoming).val
    let slot := (earlier.map (fun l => l.count (fun x => boundaryWidth raw node x/p))).sum+j.val
    Σ' socket : PublicSocket B host split word true (num field query lanes batches nodes args),
      (((Z).laneShape birth split p hp unitFit venue).keys gate_)[slot]?=some (.inl ref) ∧
        deviceRoute B hp venue ref=(wire,word) ∧ socket.face.val=(wire,incoming) := by
  intro word ref earlier slot
  obtain ⟨socket,route,face⟩ := tree_arc_raw_socket B hp unitFit s t e b d₀ incoming field query lanes batches nodes args j
  refine ⟨socket,?_,route,face⟩
  have source := DescentRetainedRangeDigits.before_multiple ((Z).treePorts split p unitFit s t node) multiple
  have convertRef := tree_arc_wordBlock (K:=F) (C₀:=C) (k:=B.reset.k) (n:=B.reset.n) (h:=h) (bits:=B.reset.width)
    (u:=B.reset.unit) (N:=∑ x,B.count x) placement (Z).graph (Z).positive (Z).pay (Z).circuit birth d split p
    hp unitFit s t e b d₀ incoming multiple source j
  have read := (Z).tree_gate_lanes birth split p hp unitFit s t node ⟨e,rfl⟩ b source (treeArcPin incoming) j
  exact read.trans (congrArg (fun r : BlockRef p (boundaryWidth (Z).bank venue) => some (Sum.inl r)) convertRef.symm)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
