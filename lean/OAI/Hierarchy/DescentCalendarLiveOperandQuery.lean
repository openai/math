import OAI.Hierarchy.DescentCalendarLiveOperand
import OAI.Hierarchy.DescentClosedRosterCoverage

namespace OAI
/-! A donor/slot result denotes the actual signed old-stem or trunk occurrence at the receiver. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt
open DescentParallelBase DescentResetSignedScan DescentNextSignedWindow DescentCableDonorNames
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
open scoped Fin.CommRing
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "cnt" => fun e=>(coarse).graph.width e/(Z).unit
local notation "world" => (Z).orderedOrdinary T birth
local notation "tape" => (Z).nativeResetEdges T vertexCode birth
local notation "index" => (tape).order.trans Fin.valEmbedding
local notation "dense" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "groups" => S.groupCount (i+1)
local notation "rawSite" => B.raw.siteFrom (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=groups)) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "sparse" => DescentResetLocalOrder.allCode B.raw index S B.valid rawSite
local notation "renameEdge" => DescentPhysicalOrder.rename sparse
local notation "next" => B.reblock.result
local notation "A" => B.next.placement
local notation "ord" => B.next.order.trans Fin.valEmbedding
local notation "stream'" => Stage.stream A ord
local notation "board" => Stage.source A ord
local notation "wt" => weight B
local notation "grains" => emit B
local notation "piece'" => piece B
local notation "base'" => first B


open scoped BigOperators
open DescentNextSignedWindow
local notation "C₀" => blocks B
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "live" => fun e : (coarse).graph.Edge=>e∈(coarse).core
local notation "fit" => Stage.measured A ord S B.next.valid
variable (names : Stage.Host (Fin (S.groupCount (i+1))) B.next.V k ↪ ℕ)

open DescentNextSignedWindow.Native
open DescentDatedAddressBook.ResetOutput DescentSIMDLookup DescentOperandStateBanks
open DescentResetOperandComponents DescentResetOperandSlices
local notation "unitAt" host => GrainPorts.Unit A ord C₀ host
local notation "faceAt" host:max u:max => Roster.face A ord C₀ host u
local notation "peerAt" host:max u:max => DescentResetWindowFields.neighbor A ord S B.next.valid names C₀ host (faceAt host u)
local notation "liveAt" host:max u:max => Stage.live A ord S B.next.valid names host (GrainPorts.port A ord C₀ host u)


open DescentIssuedFallbackPanel DescentOperandCandidateLookup
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "before" => input.order.trans Fin.valEmbedding
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "addr" j => localAddress (c:=(T).commonDepth) input.placement before S input.valid digitsIn B.frame.basis false (beforeStem B j)

private theorem native_code {N bits : ℕ} (j : Fin N) (room : N<2^bits) :
    ((1+j.val:ℕ):Cell bits)=code room (some j) := by
  apply Fin.ext
  rw [Fin.val_cast_of_lt (by have inside:=j.isLt;omega : 1+j.val<2^bits)]
  change 1+j.val=j.val+1
  omega

private theorem unsigned_slot (host : Host) (u : unitAt host) (side : u.val.2=false) :
    (grainSlot B host u).val=
      ((localRoster B host) (Roster.resident A ord C₀ host (faceAt host u))).val := by
  change (finProdFinEquiv ((if u.val.2 then 1 else 0 : Fin 2),_)).val=_
  simp [side,finProdFinEquiv_apply_val]

theorem outgoing_operand_query (host : Host) (u : unitAt host) (edge : (old).graph.Edge)
    (mother : u.val.1.1=stemParent B (false,edge)) (orientation : u.val.2=false)
    (shape : DescentResetRetainedCableLaw.Shape) (x : shape.Input) (donor : shape.Donor) (slot : shape.Slot)
    (foundAt : shape.found x=some (donor,false,slot)) (cap : shape.cap=input.placement.cap)
    (lo : donor.val=(addr edge).1.val) (localSlot : slot.val=(addr edge).2.val)
    (room : 2*totalLocal B<2^shape.queryBits) :
    shape.query x=code room (some (grainSlot B host u)) := by
  let resident:=Roster.resident A ord C₀ host (faceAt host u)
  have edgeAt : resident.val=stemParent B (false,edge) := mother
  have active : DescentResetLocalRoster.active C₀ host (stemParent B (false,edge)) :=
    edgeAt ▸ resident.property
  have ident : resident=⟨stemParent B (false,edge),active⟩:=Subtype.ext edgeAt
  have stored:=stem_number B host false edge active
  rw [←ident] at stored
  have unsigned:=unsigned_slot B host u orientation
  have numeric : (grainSlot B host u).val=(finProdFinEquiv (donor,slot)).val := by
    rw [unsigned]
    change ((localRoster B host) resident).val=_
    rw [stored]
    simp [finProdFinEquiv_apply_val,cap,lo,localSlot,show (finTwoEquiv.symm false).val=0 by decide]
  rw [shape.original_query x donor false slot foundAt]
  change ((1+(finProdFinEquiv (donor,slot)).val:ℕ):Cell shape.queryBits)=_
  rw [←numeric]
  exact native_code _ room

theorem incoming_operand_query (host : Host) (u : unitAt host) (original : (Z).Fallback)
    (mother : u.val.1.1=trunkParent B original) (orientation : u.val.2=false)
    (shape : DescentResetRetainedCableLaw.Shape) (x : shape.Input) (donor : shape.Donor) (slot : shape.Slot)
    (foundAt : shape.found x=some (donor,true,slot)) (cap : shape.cap=input.placement.cap)
    (donors : shape.donors=2^((S.groupWidth k tail i+k)-(T).commonDepth))
    (room : 2*totalLocal B<2^shape.queryBits) :
    shape.query x=code room (some (grainSlot B host u)) := by
  let resident:=Roster.resident A ord C₀ host (faceAt host u)
  have edgeAt : resident.val=trunkParent B original := mother
  have active : DescentResetLocalRoster.active C₀ host (trunkParent B original) := edgeAt ▸ resident.property
  have ident : resident=⟨trunkParent B original,active⟩:=Subtype.ext edgeAt
  have stored:=trunk_number B host original active
  rw [←ident] at stored
  have unsigned:=unsigned_slot B host u orientation
  have numeric : (grainSlot B host u).val=2*shape.strip := by
    rw [unsigned]
    change ((localRoster B host) resident).val=_
    rw [stored]
    simp only [stemsCount,DescentResetRetainedCableLaw.Shape.strip,donors,cap]
  rw [shape.original_query x donor true slot foundAt]
  change ((1+2*shape.strip:ℕ):Cell shape.queryBits)=_
  rw [←numeric]
  exact native_code _ room

private theorem code_some {b N : ℕ} (room : N<2^b) {q : Option (Fin N)} {j : Fin N}
    (v : code room q=code room (some j)) : q=some j := by
  cases q with
  | none =>
    have eqn:=congrArg Fin.val v
    change 0=j.val+1 at eqn
    omega
  | some k =>
    have eqn:=congrArg Fin.val v
    change k.val+1=j.val+1 at eqn
    exact congrArg some (Fin.ext (by omega))

/-- The physical carrier and its mathematical roster may have definitionally
different widths. One cancellation of the numerical query identifies the row
selected by the registered adder on that same site and group. -/
theorem selected_at_grain {H G rows queryBits : ℕ} (shape : rows=totalLocal B)
    (host : Host) (u : unitAt host) (location : Fin H→Fin G→Option Host)
    (q : Fin H→Fin G→Option (Fin (2*rows))) (r : Fin H) (g : Fin G)
    (liveHere : location r g=some host)
    (room : 2*rows<2^queryBits) (oldRoom : 2*totalLocal B<2^queryBits)
    (word : Cell queryBits) (issued : code room (q r g)=word)
    (branch : word=code oldRoom (some (grainSlot B host u))) (signed coeff : ℕ) (f : Field) :
    DescentOperandCandidateLookup.selected q (fun j h g=>nativeCandidateField signed coeff f ((location h g).bind (fun v=>
      candidateRows B names v (j.cast (congrArg (2*·) shape))))) r g =
      nativeCandidateField signed coeff f (some (grainRecord B names host u)) := by
  subst rows
  have row := code_some room (issued.trans branch)
  simp [DescentOperandCandidateLookup.selected,row,liveHere,grain_recorded]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
