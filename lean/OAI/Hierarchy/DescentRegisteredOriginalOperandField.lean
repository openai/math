import OAI.Hierarchy.DescentRetainedOriginalLanding

namespace OAI
/-! The registered retained pointer at a reached primary host uses the actual old
terminal's four digits and signed incidence panel, and returns the chosen successor pointer. -/
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

theorem origin_operand_field (oldNames : Stage.Host J₀ input.V k↪ℕ) (v : W.graph.Site)
    (e : Incident W.graph v) (j : Fin ((prior).grainCount e.val))
    (shape : DescentResetRetainedCableLaw.Shape) (x : shape.Input)
    (degree : shape.degree=(prior).degree) (cap : shape.cap=(prior).cap) (donors : shape.donors=L)
    (peer first chunk : ℕ) (head : ∀f,(shape.header x f).val=(Pointer.cable peer first chunk).header f)
    (atDonor : (shape.donorCell x).val=(sub v).val+1)
    (rows : ∀s,HEq (shape.row x ((sub v).cast donors.symm) s) (DescentSignedCableCodec.encode
      (Stage.signedPanel (prior) before S input.valid oldNames (hOld v) (s.cast (congrArg (2*·) cap)))))
    (peerFit : peer<(prior).degree) (firstFit : first<(prior).cap) (within : chunk/shape.units=j.val)
    (label : peer*(prior).cap+first=(DescentTerminalPortChart.label (prior) before S input.valid oldNames v e (Nat.zero_lt_of_lt j.isLt)).val)

    (room : 2*totalLocal B<2^shape.queryBits) (pos : 0<shape.units)
    (ticket : tag v e=true → shape.ticket x ((sub v).cast donors.symm)
      ((atSlot v e j).cast (congrArg (2*·) cap.symm))=earlierIncoming B (oldEndOf B (rawEnd e j)))
    (hub : tag v e=true → decide ((shape.hubCell x).val=1)=(T).hub (land (oldEndOf B (rawEnd e j))))
    (small : shape.oldIndex x ((sub v).cast donors.symm) (tag v e)
      ((atSlot v e j).cast (congrArg (2*·) cap.symm))<2^shape.fieldBits)
    {labelBits H₀ G₀ candidates : ℕ} (earlier : Field→Cell shape.fieldBits) (alias_ : Cell labelBits)
    (span : Span) (signed coeff : ℕ)
    (archive : ∀f,(earlier f).val=(Pointer.cable peer first chunk).fields span f)
    (width : max ((A).degree+1) ((A).cap+1)≤2^signed) (f : Field)
    (count : candidates=totalLocal B) (nativeRoom : 2*candidates<2^shape.queryBits)
    (location : Fin H₀→Fin G₀→Option Host) (q₀ : Fin H₀→Fin G₀→Option (Fin (2*candidates)))
    (rh : Fin H₀) (rg : Fin G₀)
    (whereAt : location rh rg=some (Stage.home A (hop ((Z).oldOwner T v))))
    (query : code nativeRoom (q₀ rh rg)=shape.query x) :
    let edge:=oldEndOf B (rawEnd e j)
    let z₀:=(sub v).cast donors.symm
    let slot:=(atSlot v e j).cast (congrArg (2*·) cap.symm)
    let site:=oldHost (tag v e) edge
    let u:=actual (tag v e) edge
    let rs:=grainRecord B names site u
    let c₀:=liveAt site u
    let cursor:=shape.oldIndex x z₀ (tag v e) slot
    let value:=(Pointer.cable c₀.neighbor.val (c₀.wire.val-c₀.within.val)
      (if rs.marked then cursor%shape.units else cursor)).fields span f
    value<2^coeff →
    (((DescentResetRetainedPages.kept f (earlier 0) (earlier f) alias_).val+(shape.priceField f x).val:ℕ):Cell coeff).val+
      (DescentOperandCandidateLookup.selected q₀ (fun slot h g=>nativeCandidateField signed coeff f
        ((location h g).bind (fun site=>candidateRows B names site (slot.cast (congrArg (2*·) count)))) ) rh rg).val=value := by
  intro edge z₀ slot site u rs c₀ cursor value fits
  obtain ⟨found,slotAt⟩:=origin_query B oldNames v e j shape x degree cap donors peer first chunk head
    atDonor rows peerFit firstFit within label room
  have loc : location rh rg=some site := whereAt.trans (congrArg some (origin_site B v e j)).symm
  have hit:=selected_at_grain B names count site u location q₀ rh rg loc nativeRoom room (shape.query x)
    query slotAt signed coeff f
  have result:=carried_operand_value B names edge shape x z₀ (tag v e) slot found (head 0) pos ticket hub
    small earlier alias_ span peer first chunk signed coeff archive width f fits
  rw [grain_recorded] at result
  rw [hit]
  exact result

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
