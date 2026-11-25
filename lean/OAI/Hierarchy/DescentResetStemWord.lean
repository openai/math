import OAI.Hierarchy.DescentResetCompactSourceTicket
import OAI.Hierarchy.DescentResetStemGroupPlane
import OAI.Hierarchy.DescentIssuedGoodHeaders

namespace OAI
/-! # Producing the stem's compact parent code from the previous signed cable word -/
noncomputable section
namespace Hierarchy.DescentResetStemWord
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local.Gather DescentPackedFallbackTree.Image
open DescentResetParentCodec DescentSharedCableNames.Stage
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {b w H G field M : ℕ}

/-- Columns are the original signed word, its source group rank, its source
host rank, the previous block, the actual active bit and the coarse zero bit. -/
def render (D k r Y L cap links prog b : ℕ) (s : Bool) (x : Fin 6→Cell field) : Cell b :=
  let original : Cell (DescentSignedCableCodec.width D cap):=((x 0).val:ℕ)
  let src:=((x 1).val*(D+2)+(x 2).val)*2^k+(x 3).val
  if (x 4).val=0 then 0 else
    match DescentSignedCableCodec.decode D cap original with
    | none=>0
    | some live=>if lt:src<L then
        let tag : DescentResetCompactParent.Word (D+2) r Y L cap links prog:=
          .inl (finTwoEquiv.symm s,⟨src,lt⟩,live.sourceWire,live.within)
        ((number (decide ((x 5).val≠0)) tag:ℕ):Cell b)
      else 0

theorem inactive (D k r Y L cap links prog b : ℕ) (s : Bool) (x : Fin 6→Cell field) (zero : (x 4).val=0) :
    render D k r Y L cap links prog b s x=0:=by simp [render,zero]

/-- Every physical lane receives the emitted whole packed word with padding. -/
theorem run (D k r Y L cap links prog b : ℕ) (s : Bool) (tables : Fin 6→Tables) (reads : Fin 6→Expr)
    (menu : DescentSIMDLookup.Banks) (mid out : ℕ) (x : Fin H→Fin G→Fin 6→Cell field)
    (positive : 0<M) (mem : Memory w) (bounds : Bounds (w:=w) (d:=field) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=field) j) M mem)
    (sources : ∀j,Source (reads j) (fun a g=>x a g j) M mem) (room : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (field*6) b M H G w out)
    (rom : resident (render D k r Y L cap links prog b s ∘ (DescentSIMDLookup.encode field 6).symm) menu H G M mem)
    (dictLow : menu.dictionary.base+2^((field*6)*M)≤ mid) (maskLow : menu.mask.base+H*chunks G M≤ mid)
    (wire : menu.source.base=mid) :
    let op:=assembly tables reads
    let n:=H*chunks G M
    let dst:=imageBank H G M out menu (image mid n op mem)
    ((scan w mid n op).seq (DescentSIMDLookup.program menu out H G M w)).Exec mem dst
      ((4+n*(2*op.work+4))+(4+44*n)) ∧
    (∀p : Row H G M,dst (out+(row H G M p).val)=((data (fun a g=>render D k r Y L cap links prog b s (x a g)) p).val:Word w)) ∧
    (∀a g,digit b (lane g positive).val (dst (out+(row H G M (position a g positive)).val)).val=(render D k r Y L cap links prog b s (x a g)).val) ∧
    ∀addr,(addr< mid ∨ mid+n≤addr)→(addr<out ∨ out+n≤addr)→dst addr=mem addr :=
  DescentIssuedGoodHeaders.gathered_words _ tables reads menu mid out x positive mem bounds constants sources room fit rom dictLow maskLow wire

end Hierarchy.DescentResetStemWord
namespace Hierarchy.DescentSixParty.ClosedReset.Window
set_option quotPrecheck false
open DescentCompiler DescentColonies DescentSharedCableNames DescentParallelBase DescentChosenRouter
open DescentResetCompactParent DescentResetCableSlots DescentResetOrdinalDigits DescentResetWireTags
open DescentRouterSlots DescentPackedTicketChronology DescentOrderedReset
open DescentResetSourceTicketRAM DescentResetSourceTicketCompare
open DescentSIMDLookup DescentGL DescentResetStemCompactOrder DescentIssuedFallbackPanel
open scoped Classical BigOperators Fin.CommRing
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "R" => B.reset.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "U" => Fintype.card input.V
local notation "H" => input.placement.degree+2
local notation "Y" => (2^(Z).n:ℕ)
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "L" => (2^(S.groupWidth k tail i+k-(T).commonDepth)+1)*H*2^k
local notation "slots" => max Y (2^height)
local notation "pcCap" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))
local notation "okCode" => fun t=>((T).codeLegal t).2
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "Kind" => (Bool×(old).graph.Edge) ⊕ ((Z).Fallback ⊕ ((R).Contact ⊕ PrivateOccurrence B))
local notation "Short" => DescentResetCompactParent.Word H r Y L (A).cap slots pcCap

local notation "tape" => (Z).nativeResetEdges T vertex birth


local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation "fitBlock" => B.frame.enough.trans (Nat.sub_le ..)
local notation "previous" => input.order.trans Fin.valEmbedding
local notation "groupTable" => fun u : Host=>groupDomain digits B.frame.basis fitBlock (B.frame.host.symm (receiverRoot B u).1) (receiverRoot B u).2
local notation "halo" => fun u : Host=>hostDomain A input.vertex (B.frame.host.symm (receiverRoot B u).1)

theorem stem_word_read (u : Host) (s : Bool) (j : (old).graph.Edge)
    (names : Stage.Host (Fin (S.groupCount i)) input.V k↪ℕ)
    {field b : ℕ} (x : Fin 6→Cell field)
    (read : (x 0).val= (DescentSignedCableCodec.encode (Stage.signedPanel A previous S input.valid names
      (port A s (beforeStem B j)).1
      (Stage.signed A previous S input.valid (port A s (beforeStem B j)).1.1 (port A s (beforeStem B j)).1.2
      (port A s (beforeStem B j)).2))).val)
    (groupRead : (x 1).val=compress (groupTable u) ((A).pos (W.graph.src (beforeStem B j).1)).1.val)
    (haloRead : (x 2).val=compress (halo u) (input.vertex ((A).pos (W.graph.src (beforeStem B j).1)).2).val)
    (blockRead : (x 3).val=((A).block (W.graph.src (beforeStem B j).1)).val)
    (live : (x 4).val≠0) (zero : decide ((x 5).val≠0)=zeroCoarse B u) :
    DescentResetStemWord.render (A).degree k r Y L (A).cap slots pcCap b s x =
      ((wordNumber B u (stemParent B (s,j)):ℕ):Cell b) := by
  let e:=beforeStem B j
  let hp:=port A s e
  let honest:=Stage.live A previous S input.valid names hp.1 hp.2
  have got : (x 0).val=(DescentSignedCableCodec.encode (some honest)).val:=by
    rw [read,Stage.signed_read]
  have source : ((x 1).val*((A).degree+2)+(x 2).val)*2^k+(x 3).val=compactStemSource B u e:=by
    rw [groupRead,haloRead,blockRead];rfl
  have width:=compactStem_room B u e
  have oldWire : honest.sourceWire=outgoingSlot A S input.valid input.order e:=by cases s <;> rfl
  have within : honest.within.val=e.2.val:=by cases s <;> rfl
  have indexEq : honest.within=(⟨e.2.val,width.2.2⟩ : Fin (A).cap):=Fin.ext within
  unfold DescentResetStemWord.render
  simp only [ite_eq_right live,got,Fin.cast_val_eq_self,DescentSignedCableCodec.decode_encode,source,dite_eq_left width.1,zero]
  unfold wordNumber nativeWord stemParent
  rw [Equiv.apply_symm_apply]
  unfold namedWord
  rw [oldWire,indexEq]

end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
