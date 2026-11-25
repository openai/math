import OAI.Hierarchy.DescentCalendarMoverWindow
import OAI.Hierarchy.DescentRetainedPrimaryCompleteness
import OAI.Hierarchy.DescentVacantPrimaryToken

namespace OAI
/-! # Retained and vacant terminal rows of the measured home selection -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentRetainedControl DescentCompiler DescentColonies DescentSIMDLookup DescentGL DescentPackedColony DescentPackedZip
open DescentPaidResidentCount.Reset DescentFallbackPeriod DescentFallbackPeriod.Projected
open DescentSharedCableNames.Stage DescentStageEdgeReceipt DescentIssuedFallbackPanel DescentGroupPeerOrder
open DescentPackedWalsh DescentPacking.PackedMatch.Local.Stage DescentContactSenderDate
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cc" => (T).commonDepth
local notation "r" => (Z).k-cc
local notation "m" => S.groupWidth k tail i+k
local notation "dep" => GroupStage.depthBound D n f g
local notation "H" => S.hostSize i
local notation "J" => 2^cc
local notation "cap" => (A).cap
local notation "deg" => (A).degree
local notation "full" => (A).wire*((A).z*G.b)*cap
local notation "pad" => input.valid.host
local notation "id_" => input.vertex.trans (Fin.castLEEmb pad)
local notation "peer" => PackedFlow.Padded.roster (D:=deg) (A) (Recorded.oldName input) pad
local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation "names" => cableNames k (groupRank (Fin.valEmbedding (n:=S.groupCount i)) ((id_).trans Fin.valEmbedding))
variable {M field bw N K R hm lb tiny p nbits t : ℕ}
    (rc : Receiver deg cap N (Z).n r cc H (S.groupCount i) K R M hm lb tiny field dep bw)
    (book : RootBook (Z).n r deg (2^r) cap field) (space : rc.PreparedFits book) (mem : Memory bw)
    (hdr : OriginalHeader B pad rc book mem) (src : RootSources deg (2^r) cap)
local notation "paid" => Recorded.paddedValue (b:=field) cc r peer (Recorded.oldDepth B) (Recorded.oldWidth B)
local notation "middle" => rc.preparedMid book space mem
local notation "done" => rc.preparedImage book space mem
local notation "rank_" => fun v j=>(DescentSharedBookScan.ranks (a:=r) (Y:=2^(Z).n) (D:=deg)
  (book.common rc.projectionEnd H) (2^dep) (dep+2) middle v j).val
local notation "axis" => congrArg (fun u=>2^(u-cc)) B.keyWidth

variable (x : OriginalArrays B pad field)
open DescentRotorWindowArchive
variable (move : DescentRetainedHomeMover.Layout)
local notation "v" => move.transfer
variable (hostAxis:(v).hosts=H) (dimAxis:(v).high+(v).low=m) (cutAxis:(v).cut=cc)
    (degreeAxis:move.degree=deg) (loadAxis:move.cap=cap) (fieldAxis:move.rootField=field)
local notation "lowEq" => congrArg (fun u:ℕ=>2^u) (congrArg₂ Nat.sub dimAxis cutAxis)
local notation "slots" => (lowEq).trans (axis).symm
local notation "highEq" => congrArg (fun u:ℕ=>2^u) cutAxis
local notation "lift" => (show move.control.rootWidth=field*DescentRotorWindowArchive.count deg (2^r) cap from
  congrArg₂ Nat.mul fieldAxis (by change DescentRotorWindowArchive.count move.degree (v).donors move.cap=DescentRotorWindowArchive.count deg (2^r) cap;exact congrArg₂ (fun n c=>DescentRotorWindowArchive.count n (v).donors c) degreeAxis loadAxis |>.trans (congrArg (fun n=>DescentRotorWindowArchive.count deg n cap) slots)))
local notation:max "data" h:arg hi:arg => encode field _ (calendar_sender_matrix B M field rc book space mem hdr x h hi)
local notation "observed" => moverWindow B rc book space mem hdr x move hostAxis dimAxis cutAxis degreeAxis loadAxis fieldAxis
local notation:max "cmp" hi:arg a:arg b:arg => GroupStage.previousDigit B.frame.basis (B.frame.enough.trans (Nat.sub_le ..)) hi a b

open DescentSixParty.Chronology DescentKernelHistory DescentPrimitivePalette DescentLocalArchiveOrder DescentResetLocalNodes
open Reached.NodeCells DescentRotorWindowArchive DescentOrdinaryAtomFieldRAM
variable (history : Archive W) (early : Local history.bit)
variable (blocks : (v).blocks=2^k) (groups:(v).groups=S.groupCount i)
    (size:2^((v).high+(v).low)=(v).groups*(v).blocks) (fits:(v).cut≤(v).high+(v).low)
    (basis:DescentGL.Layout ((v).high+(v).low)) (won:HEq basis B.frame.basis)
    (token : NodeOrder.All history.bit→Cell (v).bits) (positive:∀u,(token u).val≠0)
    (nodeRoom : ∀u,Fintype.card (history.bit.recipe u).Node≤(v).previousNodes)
local notation "room" => (show Fintype.card input.V≤(v).hosts from (pad).trans_eq hostAxis.symm)
local notation "name" => input.vertex.trans (Fin.castLEEmb room)
local notation "old" => previousTokens input history.bit early (v) blocks groups token
local notation "allData" => move.oldStrips size fits basis old
local notation:max "pos" lo:arg => (finProdFinEquiv.symm (Fin.cast size lo):Fin (v).groups×Fin (v).blocks)
local notation:max "coarse" hi:arg => (Fin.cast (highEq).symm hi)
local notation "orig" => (Recorded.originalCell (reset:=B))
local notation "small" => B.frame.enough.trans (Nat.sub_le ..)
local notation:max "raw" hi:arg lo:arg => (rearrange B.frame.basis).symm (join small hi lo)
local notation:max "filled" u:arg => StarKeys.filled W.graph (A).pos (A).block digits u
local notation:max "code" t:arg => DescentFallbackShapeTable.cell r (DescentRelativeContacts.shortName cc ((T).code t)).2
variable (which : Fin move.shapes→Option ℕ) (tok:Fin move.shapes)
variable (packet : RootPacket B rc book space mem hdr src x nbits t)
    (short:t≤field) (active:0<field)

local notation:max "datum" j:arg v₀:arg hi:arg => move.targetInputs which observed allData (finProdFinEquiv (j,tok)) (name v₀) (coarse hi)
local notation "key" => (A).site input.vertex input.valid.coordinates
local notation:max "ord" u:arg => (early u).toEmbedding.trans Fin.valEmbedding

include packet short active in
private theorem mask_at (actor:input.V) (hi:Block cc) (wanted:ℕ) (seek:which tok=some wanted) :
    filter (D:=move.degree) (L:=(v).donors) («cap»:=move.cap) (which tok)
      (observed (name actor) (coarse hi))=
      vector (fun q=>decide (x.stencil (id_ actor) hi (q.cast lowEq)/2=wanted))
        (fun a b=>cmp hi (a.cast lowEq) (b.cast lowEq)):=by
  rw [seek]
  have same : (name actor).cast hostAxis=id_ actor:=Fin.ext rfl
  have atBlock : (coarse hi).cast highEq = hi := Fin.ext rfl
  have observedAt := mover_filter B rc book space mem hdr src x move hostAxis dimAxis cutAxis degreeAxis loadAxis fieldAxis packet short active wanted
      (name actor) (coarse hi)
  exact observedAt.trans (congrArg₂ (fun (h : Fin H) (g : Block cc) =>
    vector (fun q : Fin (v).donors => decide (x.stencil h g (q.cast lowEq)/2=wanted))
      (fun a b=>cmp g (a.cast lowEq) (b.cast lowEq))) same atBlock)

variable (term : (Z).Fallback)
local notation "actor" => B.frame.host.symm ((T).code term).1
local notation "hi" => (Z).rootBlock T (.inr term)
local notation "word" => x.stencil (id_ actor) hi
local notation "order" => ((Z).homeTicket T key term).trans Fin.valEmbedding

include won positive nodeRoom packet short active in
theorem actual_old_token (pick:which tok=some (code term))
    (pivot : DescentNamedContact.Fibre (T).home term) (node : (history.bit.recipe pivot.val).Node)
    (nx:Fin (v).nodes) (actual:nx.val=(oldOrder (fun u:DescentNamedContact.Fibre (T).home term=>(history.bit.recipe u.val).Node)
      order (fun u=>ord u.val) ⟨pivot,node⟩).val) : datum nx actor hi=token ⟨pivot.val,node⟩:=by
  apply calendar_old_primitive B history early move dimAxis cutAxis blocks groups size fits basis won room token positive nodeRoom term
    word tok which observed _ _ pivot node nx actual
  · exact mask_at B rc book space mem hdr src x move hostAxis dimAxis cutAxis degreeAxis loadAxis fieldAxis which tok
      packet short active actor hi (code term) pick
  · exact primary_original_stencil B x actor hi

include won positive nodeRoom packet short active in
theorem actual_old_zero (pick:which tok=some (code term)) (nx:Fin (v).nodes)
    (absent:(∑u:DescentNamedContact.Fibre (T).home term,Fintype.card (history.bit.recipe u.val).Node)≤nx.val) :
    datum nx actor hi=0:=by
  apply calendar_old_padding B history early move dimAxis cutAxis blocks groups size fits basis won room token positive nodeRoom term
    word tok which observed _ _ nx absent
  · exact mask_at B rc book space mem hdr src x move hostAxis dimAxis cutAxis degreeAxis loadAxis fieldAxis which tok packet short active
      actor hi (code term) pick
  · exact primary_original_stencil B x actor hi

include won positive nodeRoom packet short active in
theorem actual_vacant_token (v₀:input.V) (q₀:Block cc) (wanted:ℕ) (seek:which tok=some wanted)
    (empty:¬∃u:(Z).Fallback,((T).code u).1=B.frame.host v₀ ∧ (Z).rootBlock T (.inr u)=q₀ ∧ code u=wanted)
    (nx:Fin (v).nodes) : datum nx v₀ q₀=0:=by
  let amount:=fun u:W.graph.Site=>Fintype.card (history.bit.recipe u).Node
  apply vacancy_token B.frame _ _ _ _ _ _ _ _ _ _ (Recorded.old_roster (reset:=B)) v₀ q₀ wanted
    (x.stencil (id_ v₀) q₀) (primary_original_stencil B x v₀ q₀) empty move (finCongr lowEq)
    tok (name v₀) (coarse q₀) which observed allData nx amount
  · intro lo
    let oldDigit:=(rearrange basis).symm (join fits (coarse q₀) ((finCongr lowEq).symm lo))
    have loc:((pos oldDigit).1.cast groups,(pos oldDigit).2.cast blocks)=digits (raw q₀ lo):=by
      have hh:(coarse q₀).cast highEq=q₀:=Fin.ext rfl
      have hl:((finCongr lowEq).symm lo).cast lowEq=lo:=Fin.ext rfl
      simpa only [hh,hl] using moved_position S ctl.base ctl.radix
        dimAxis groups blocks size fits basis cutAxis B.frame.basis won small (coarse q₀) ((finCongr lowEq).symm lo)
    have xx:(pos oldDigit).2=((digits (raw q₀ lo)).2.cast blocks.symm):=Fin.ext (congrArg (fun y=>y.2.val) loc)
    have gg:(pos oldDigit).1=((digits (raw q₀ lo)).1.cast groups.symm):=Fin.ext (congrArg (fun y=>y.1.val) loc)
    apply move.previous_count size fits basis old (name v₀) (coarse q₀) ((finCongr lowEq).symm lo) _
      (population_bound input history.bit (v) digits v₀ (raw q₀ lo) nodeRoom)
    intro j
    change (ScalarOperand.take j (old (pos oldDigit).2 (name v₀) (pos oldDigit).1)).val≠0 ↔ _
    rw [xx,gg]
    exact previous_population input history.bit early (v) blocks groups token positive room digits v₀ (raw q₀ lo) j
  · exact mask_at B rc book space mem hdr src x move hostAxis dimAxis cutAxis degreeAxis loadAxis fieldAxis which tok packet short active
      v₀ q₀ wanted seek

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
