import OAI.Hierarchy.DescentCalendarCarriedOperand

namespace OAI
/-! # Original retained node and earlier signed grain at the reached primary terminal -/
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
set_option quotPrecheck false
local notation "unitAt" host => GrainPorts.Unit A ord C₀ host
local notation "faceAt" host:max u:max => Roster.face A ord C₀ host u
local notation "peerAt" host:max u:max => DescentResetWindowFields.neighbor A ord S B.next.valid names C₀ host (faceAt host u)
local notation "liveAt" host:max u:max => Stage.live A ord S B.next.valid names host (GrainPorts.port A ord C₀ host u)


open DescentIssuedFallbackPanel DescentOperandCandidateLookup
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "before" => input.order.trans Fin.valEmbedding
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "addr" j => localAddress (c:=(T).commonDepth) input.placement before S input.valid digitsIn B.frame.basis false (beforeStem B j)


local notation "oldHost" side:max edge:max => (blocks B).src (carriedParent B side edge)
local notation "actual" side:max edge:max => carriedUnit B side edge
local notation "land" edge => (T).home ((old).graph.dst edge)


open DescentOperandPriorIncidence DescentKernelHistory DescentResetTrunks DescentResetAttachments
local notation "prior" => input.placement
local notation "J₀" => Fin (S.groupCount i)
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "End" => (old).graph.Edge
local notation "rawEnd" e:max j:max => (⟨(e).val,j⟩:Stage.Grain (prior))
local notation "hOld" v => Stage.home (prior) v
local notation "tag" v:max e:max => originFace v e
local notation "atSlot" v:max e:max j:max => Stage.signed (prior) before S input.valid (hOld v).1 (hOld v).2 (originPort (prior) v e j)
local notation "sub" v => subcell (c:=(T).commonDepth) digitsIn B.frame.basis (hOld v)
local notation "same" => funext (fun e=>((Z).allWidths e).symm)
local notation "wires" => installedWireNames (old) (T).home (Z).placement.input (T).hub same (Z).bank (Z).tables

def oldEndOf (t : Stage.Grain (prior)) : End:=⟨t.1,t.2.cast (congrFun B.count_eq t.1).symm⟩

theorem oldEndOf_read (t : Stage.Grain (prior)) : beforeStem B (oldEndOf B t)=t:=by
  obtain ⟨e,j⟩:=t
  rfl

theorem primary_cell (side : Bool) (j : End) :
    (blocks B).src (carriedParent B side j)=
      Stage.home A (hop ((Z).oldOwner T (ends (old).graph side j))):=by
  change Stage.home A (hop ((coarse).graph.src (carriedParent B side j)))=_
  apply congrArg (fun a=>(Stage.home A (hop a)))
  apply ((Z).resetNames T).injective
  cases side with
  | false =>
    change (Z).resetNames T ((coarse).graph.src (stemParent B (false,j)))=_
    have read:=sourceFields_read (old) (T).home (Z).placement.input (T).hub same (Z).bank (Z).tables (stemParent B (false,j))
    change physicalFields _ _ _ _ _ _ _ _=sourceFields _ _ _ _ _ ((wires) ((wires).symm (.inl (false,j)))) at read
    rw [Equiv.apply_symm_apply] at read
    simp only [ResetInput.oldOwner,Equiv.apply_symm_apply]
    exact congrArg RawFields.src read
  | true =>
    change (Z).resetNames T ((coarse).graph.src (trunkParent B ((T).home ((old).graph.dst j))))=_
    have read:=sourceFields_read (old) (T).home (Z).placement.input (T).hub same (Z).bank (Z).tables (trunkParent B ((T).home ((old).graph.dst j)))
    change physicalFields _ _ _ _ _ _ _ _=sourceFields _ _ _ _ _ ((wires) ((wires).symm (.inr (.inl ((T).home ((old).graph.dst j)))))) at read
    rw [Equiv.apply_symm_apply] at read
    simp only [ResetInput.oldOwner,Equiv.apply_symm_apply]
    exact congrArg RawFields.src read

theorem origin_site (v : W.graph.Site) (e : Incident W.graph v) (j : Fin ((prior).grainCount e.val)) :
    let edge:=oldEndOf B (rawEnd e j)
    (blocks B).src (carriedParent B (tag v e) edge)=Stage.home A (hop ((Z).oldOwner T v)):=by
  intro edge
  rw [primary_cell]
  have term : ends (old).graph (tag v e) edge=v:=by
    by_cases home:W.graph.src e.val=v
    · rw [show originFace v e = false by simp [originFace, home]]
      exact home
    · rw [show originFace v e = true by simp [originFace, home]]
      exact e.property.resolve_left home
  rw [term]

/-- The retained marker's zero-based coordinate is the remixed old subcell.
Its signed port is precisely the other digit of the old reset stem address. -/
theorem origin_query (oldNames : Stage.Host J₀ input.V k↪ℕ) (v : W.graph.Site)
    (e : Incident W.graph v) (j : Fin ((prior).grainCount e.val))
    (shape : DescentResetRetainedCableLaw.Shape) (x : shape.Input)
    (degree : shape.degree=(prior).degree) (cap : shape.cap=(prior).cap) (donors : shape.donors=L)
    (peer first chunk : ℕ) (head : ∀f,(shape.header x f).val=(Pointer.cable peer first chunk).header f)
    (atDonor : (shape.donorCell x).val=(sub v).val+1)
    (rows : ∀s,HEq (shape.row x ((sub v).cast donors.symm) s) (DescentSignedCableCodec.encode
      (Stage.signedPanel (prior) before S input.valid oldNames (hOld v) (s.cast (congrArg (2*·) cap)))))
    (peerFit : peer<(prior).degree) (firstFit : first<(prior).cap) (within : chunk/shape.units=j.val)
    (label : peer*(prior).cap+first=(DescentTerminalPortChart.label (prior) before S input.valid oldNames v e (Nat.zero_lt_of_lt j.isLt)).val)
    (room : 2*totalLocal B<2^shape.queryBits) :
    let edge:=oldEndOf B (rawEnd e j)
    let z₀:=(sub v).cast donors.symm
    let slot:=(atSlot v e j).cast (congrArg (2*·) cap.symm)
    shape.found x=some (z₀,tag v e,slot) ∧
      shape.query x=code room (some (grainSlot B (oldHost (tag v e) edge) (actual (tag v e) edge))) :=by
  intro edge z₀ slot
  have found:=found_origin (prior) before S input.valid oldNames v shape degree cap x z₀ input.valid.coordinates
    e j peer first chunk head atDonor rows peerFit firstFit within label
  have numbers:=origin_local_address (prior) before S input.valid v (c:=(T).commonDepth) digitsIn B.frame.basis e j
  refine ⟨found,carried_operand_query B edge shape x z₀ (tag v e) slot found cap donors ?_ ?_ room⟩
  · intro out
    rw [out] at numbers
    change (sub v).val=(addr edge).1.val
    simpa only [edge,oldEndOf_read] using (congrArg (fun t=>t.1.val) numbers).symm
  · intro out
    rw [out] at numbers
    change (atSlot v e j).val=(addr edge).2.val
    simpa only [edge,oldEndOf_read] using (congrArg (fun t=>t.2.val) numbers).symm

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
