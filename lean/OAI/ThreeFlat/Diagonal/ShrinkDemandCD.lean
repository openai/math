import OAI.ThreeFlat.Diagonal.CompressorBitIntervals
import OAI.ThreeFlat.Diagonal.CompressorDemandRank
import OAI.ThreeFlat.Diagonal.ShrinkDemandBitPath
import OAI.ThreeFlat.Diagonal.ShrinkBitResident
import OAI.ThreeFlat.Diagonal.ShrinkChildSend
import OAI.ThreeFlat.Diagonal.ShrinkNativeChild

namespace OAI
/-! # Native CD reads identify the exact original half and bit at the occupied party -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
open scoped Classical Fin.NatCast
variable {B H : Type} [AddCommGroup H] [Fintype B] [Fintype H] {N w c t l n : ℕ}
variable {S₀ : Graph.Stage}
set_option quotPrecheck false
local notation "cdStage" => ChildRows.withFree S₀ c
variable {P : PackingData B H (BitWord t) (BitWord l) S₀.degree (c+1)} {E : Codec B w (c+1) t l}
variable {b : B ≃ Fin N} {hc : 2≤c+1} {data : Param→Word w} {mem : Memory w} {vs : Fin n→Word w}
variable {ptr : Formula n} {prior : Arc B H (BitWord t) (BitWord l) S₀.degree (c+1)→ℕ}
local notation "V" => Formula.value data mem vs
local notation "g" => oldColumns (Demand.formulaOps n) ptr
local notation "key" => Demand.key P (baseNat b)
local notation "num" => motifNumbers P key hc
local notation "Q" => (3*(2^(c+1)*S₀.degree)/4)
variable (hQ : 0 < 3*(2^(c+1)*S₀.degree)/4)

private noncomputable abbrev requestWord {q : ℕ}
    (code : Arc B H (BitWord t) (BitWord l) S₀.degree (c+1) ↪ ℕ)
    (positive : 0 < q)
    (numbering : P.Motif ≃ (Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l) × Fin S₀.degree) × Fin q)
    (m : P.Motif) (side : Bool) (i : Fin 2) (bit : Fin (demandWidth P prior numbering m i))
    (bundled : ∀ a, (numbering a).1 = P.bundle a)
    (lay : Bool) (v : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l))
    (atSite : partySite P lay m (demandGraph.vertex i side) = v) (k : Fin 4) : ℕ :=
  ChildSend.words P prior lay v (ChildSend.request P code prior positive numbering m side i bit)
    ((ChildSend.request_owner P code prior positive numbering bundled lay m side i bit).trans atSite) k

private theorem request_cd {q : ℕ}
    (code : Arc B H (BitWord t) (BitWord l) S₀.degree (c+1) ↪ ℕ)
    (positive : 0 < q)
    (numbering : P.Motif ≃ (Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l) × Fin S₀.degree) × Fin q)
    (m : P.Motif) (side : Bool) (bit : Fin (demandWidth P prior numbering m 1)) :
    ChildSend.request P code prior positive numbering m side 1 bit =
      ⟨m.val, (if P.thick (sourcePosition m.val) then !side else side), bit⟩ := rfl

private theorem request_ab {q : ℕ}
    (code : Arc B H (BitWord t) (BitWord l) S₀.degree (c+1) ↪ ℕ)
    (positive : 0 < q)
    (numbering : P.Motif ≃ (Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l) × Fin S₀.degree) × Fin q)
    (m : P.Motif) (side : Bool) (bit : Fin (demandWidth P prior numbering m 0)) :
    let selectedBit := (oldBit P code prior (numbering m).1).symm
      (SlotEnergy.pieceIndex _ q positive ⟨(numbering m).2, bit⟩)
    ChildSend.request P code prior positive numbering m side 0 bit =
      ⟨selectedBit.1.val, side, selectedBit.2⟩ := rfl

set_option maxHeartbeats 800000 in
theorem demand_cd_native (R : ArcReads P E ((oldColumns (Demand.formulaOps n) ptr).map (Formula.value data mem vs)) mem) (M : MateReads (S:=cdStage) P E data mem vs ptr)
    (cw : c+1<w) (fit : 4≤2^w) (lay side : Bool) (m : P.Motif)
    (v : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l))
    (atSite : partySite P lay m (demandGraph.vertex 1 side)=v) (e : Ends (F n))
    (party edge j : F n) (bit : Fin (demandWidth P prior num m 1))
    (enc : e.map V=encodeEnds P E m.val) (partyVal : (V party).val=2+side.toNat)
    (edgeVal : (V edge).val=1) (bitVal : V j=(bit.val:Word w)) (k : Fin 4) :
    V (demandAddress ptr cdStage lay e party edge j k) =
      (requestWord (S₀:=S₀) (P:=P) (prior:=prior) (q:=Q) key hQ num m side 1 bit
        (motifNumbers_bundle P key hc) lay v atSite k : Word w) := by
  rw [demand_path ptr cdStage lay e party edge j 1 side k fit (by simpa using partyVal) (by simpa using edgeVal),
    ite_eq_right (by decide : (1:Fin 2)≠0)]
  refine ChildSend.native_words (S:=cdStage) R M rfl cw lay v (ChildSend.request P key prior hQ num m side 1 bit)
    ((ChildSend.request_owner P key prior hQ num (motifNumbers_bundle P key hc) lay m side 1 bit).trans atSite)
    e (cdSide ptr e party) j ?_ ?_ ?_ k
  · simpa only [request_cd] using enc
  · rw [request_cd]
    have sideWord := cdSide_word (S:=cdStage) ptr e m.val enc R party side partyVal fit
    by_cases thick : P.thick (sourcePosition m.val) <;> simpa only [thick,ite_true,ite_false] using sideWord
  · simpa only [request_cd] using bitVal

omit [Fintype B] [Fintype H] in
private theorem interval_ends (R : ArcReads P E ((oldColumns (Demand.formulaOps n) ptr).map (Formula.value data mem vs)) mem)
    (p : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l) × Fin S₀.degree)
    (s : Placement.Site (F n)) (port : F n) (hs : s.map V=siteCode E p.1)
    (hp : V port=(p.2.val:Word w)) (a : ThickAt P p) :
    (sourceInterval ptr cdStage s port (P.slotLabel a.val.2.2) (tagOrdinal (c+1) a.val.2.1)).map V =
      encodeEnds P E a.val := by
  let x : Placement.Position (F n) := ⟨s,.lit (tagOrdinal (c+1) a.val.2.1).val,.lit (P.slotLabel a.val.2.2).val⟩
  have hd : s.map V = siteCode E a.val.1.1 := hs.trans (congrArg (fun z => siteCode E z.1) a.property.1.symm)
  have hport : V port=(a.val.1.2.val:Word w) :=
    hp.trans (congrArg (fun z => (z.2.val:Word w)) a.property.1.symm)
  have hx : x.map V=posCode P E (sourcePosition a.val) := by
    simp only [x,sourcePosition,posCode,Placement.Position.map,hd,Formula.value,Fin.ofNat_eq_cast,Demand.tag_cast E.colors]
  exact Demand.ends_code g R false x port (sourcePosition a.val) a.val.1.2 hx hport

set_option maxHeartbeats 800000 in
/-- The four native AB demand-address words identify the physical source of the individual
bit on its six-party request, including the local offset within a sliced TT lane. -/
theorem demand_ab_native (R : ArcReads P E ((oldColumns (Demand.formulaOps n) ptr).map (Formula.value data mem vs)) mem) (M : MateReads (S:=cdStage) P E data mem vs ptr)
    (Wd : Demand.WidthReads P E (baseNat b) data mem vs (layout ptr cdStage).table
      (layout ptr cdStage).tagCount (layout ptr cdStage).laneCount prior)
    (cw : c+1<w) (fit : 4≤2^w) (lay side : Bool) (m : P.Motif)
    (v : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l))
    (atSite : partySite P lay m (demandGraph.vertex 0 side)=v) (e : Ends (F n))
    (party edge j : F n) (bit : Fin (demandWidth P prior num m 0))
    (enc : e.map V=encodeEnds P E m.val) (partyVal : (V party).val=side.toNat)
    (edgeVal : (V edge).val=0) (bitVal : V j=(bit.val:Word w))
    (widthFit : ∀ a,prior a<2^w) (totalFit : CompressorPacking.thickWidth P prior (P.bundle m)<2^w)
    (qFit : Q<2^w) (k : Fin 4) :
    V (demandAddress ptr cdStage lay e party edge j k) =
      (requestWord (S₀:=S₀) (P:=P) (prior:=prior) (q:=Q) key hQ num m side 0 bit
        (motifNumbers_bundle P key hc) lay v atSite k : Word w) := by
  rw [demand_path ptr cdStage lay e party edge j 0 side k fit (by simpa using partyVal) (by simpa using edgeVal),
    ite_eq_left rfl]
  let o := Demand.formulaOps n
  let mark := thickBit o (g).toColumns e.source
  let chosen := Position.select o mark e.target e.source
  let site := toggle o (g).toColumns chosen.site
  let keyF := Demand.physical (layout ptr cdStage) e.source e.originalSlot
  let total := Demand.thickWidth g (layout ptr cdStage) site chosen.slot
  let rank := Demand.bundleNumber g (layout ptr cdStage) site chosen.slot keyF
  have hsource : e.source.map V = posCode P E (sourcePosition m.val) := congrArg Ends.source enc
  have htarget : e.target.map V = posCode P E (sourcePosition (P.actual m.val)) := congrArg Ends.target enc
  have hslot : V e.originalSlot=(m.val.1.2.val : Word w) := congrArg Ends.originalSlot enc
  have hb : V mark=1 ↔ P.thick (sourcePosition m.val) := Demand.bit_code g R _ _ hsource
  have pick : chosen.map V = posCode P E (P.C m) := by
    apply (Demand.eval_select data mem vs mark e.target e.source).trans
    by_cases hf : P.thick (sourcePosition m.val)
    · rw [ite_eq_left (hb.mpr hf)]
      simpa only [PackingData.C,ite_eq_left hf] using htarget
    · rw [ite_eq_right (fun yes => hf (hb.mp yes))]
      simpa only [PackingData.C,ite_eq_right hf] using hsource
  have hs : site.map V = siteCode E (P.bundle m).1 := by
    rw [show site.map V = _ from Demand.eval_toggle data mem vs g chosen.site,
      show chosen.site.map V = _ from congrArg Placement.Position.site pick]
    exact toggle_site R.toGraphReads _
  have hp : V chosen.slot=((P.bundle m).2.val:Word w) := congrArg Placement.Position.slot pick
  have hkey : V keyF = (key m.val : Word w) := Demand.address_code Wd _ _ _ hsource hslot
  have ht : V total = (CompressorPacking.thickWidth P prior (P.bundle m):Word w) :=
    Demand.total_code R Wd (P.bundle m) site chosen.slot hs hp
  have hr : V rank = ((num m).2.val:Word w) := Demand.rank_code R Wd hc m site chosen.slot keyF hs hp hkey
  apply thickBlocks_piece_word ptr cdStage lay site chosen.slot party R Wd (P.bundle m) hs hp widthFit
    Q hQ (num m).2 bit total rank j totalFit qFit ht hr bitVal k
  intro y hy
  let selectedBit := (oldBit P key prior (P.bundle m)).symm
    (SlotEnergy.pieceIndex _ Q hQ ⟨(num m).2, bit⟩)
  let source := sourceInterval ptr cdStage site chosen.slot (P.slotLabel selectedBit.1.val.2.2)
    (tagOrdinal (c+1) selectedBit.1.val.2.1)
  refine ChildSend.native_words (S:=cdStage) R M rfl cw lay v
    (ChildSend.request P key prior hQ num m side 0 bit)
    ((ChildSend.request_owner P key prior hQ num (motifNumbers_bundle P key hc) lay m side 0 bit).trans atSite)
    source party y ?_ ?_ ?_ k
  · rw [request_ab]
    exact interval_ends R (P.bundle m) site chosen.slot hs hp selectedBit.1
  · rw [request_ab]
    exact (Fin.cast_val_eq_self (V party)).symm.trans (congrArg (fun z : ℕ => (z:Word w)) partyVal)
  · rw [request_ab]
    exact (Fin.cast_val_eq_self (V y)).symm.trans (congrArg (fun z : ℕ => (z:Word w)) hy)

set_option maxHeartbeats 800000 in
/-- Gather from either genuine local demand port at the selected occupied party. -/
theorem demand_port_native (R : ArcReads P E ((oldColumns (Demand.formulaOps n) ptr).map (Formula.value data mem vs)) mem) (M : MateReads (S := cdStage) P E data mem vs ptr)
    (Wd : Demand.WidthReads P E (baseNat b) data mem vs (layout ptr cdStage).table
      (layout ptr cdStage).tagCount (layout ptr cdStage).laneCount prior)
    (cw : c+1<w) (fit : 4≤2^w) (lay : Bool) (m : P.Motif)
    (partyId : Fin 6) (port : demandGraph.Port partyId) (e : Ends (F n))
    (party edge j : F n) (bit : Fin (demandWidth P prior num m port.val.1))
    (enc : e.map V=encodeEnds P E m.val) (partyVal : (V party).val=partyId.val)
    (edgeVal : (V edge).val=port.val.1.val) (bitVal : V j=(bit.val:Word w))
    (widthFit : ∀ a,prior a<2^w) (totalFit : CompressorPacking.thickWidth P prior (P.bundle m)<2^w)
    (qFit : Q<2^w) (k : Fin 4) :
    V (demandAddress ptr cdStage lay e party edge j k) =
      (requestWord (S₀:=S₀) (P:=P) (prior:=prior) (q:=Q) key hQ num m port.val.2 port.val.1 bit
        (motifNumbers_bundle P key hc) lay (partySite P lay m partyId)
        (congrArg (partySite P lay m) port.property) k : Word w) := by
  rcases port with ⟨⟨idx,side⟩,atParty⟩
  have number : partyId.val=2*idx.val+side.toNat := by
    rw [←atParty];fin_cases idx <;> cases side <;> rfl
  fin_cases idx
  · apply demand_ab_native hQ R M Wd cw fit lay side m _ (congrArg (partySite P lay m) atParty) e party edge j bit enc
    · simpa using partyVal.trans number
    · exact edgeVal
    · exact bitVal
    · exact widthFit
    · exact totalFit
    · exact qFit
  · apply demand_cd_native hQ R M cw fit lay side m _ (congrArg (partySite P lay m) atParty) e party edge j bit enc
    · simpa using partyVal.trans number
    · exact edgeVal
    · exact bitVal

set_option maxHeartbeats 800000 in
/-- The native gather term reads the original shrink stage through register zero,
the absolute old arc from the incident row, and the exact requested old bit. -/
theorem selected_demand (p : Pointers) (lay : Bool) (issued : P.Motif→Fin 8→ℕ)
    (regs : Fin 13→Word w) (m : P.Motif) (partyId : Fin 6) (port : demandGraph.Port partyId)
    (bit : Fin (demandWidth P prior num m port.val.1)) (k : Fin 4)
    (I : Resident.Input cdStage P b hc lay p (regs 0) prior issued mem)
    (number : ∀u,E.base u=((b u).val:Word w))
    (add : ∀u v,slotCode (w:=w) P (u+v)=BinaryOp.bitXor.eval (slotCode P u) (slotCode P v))
    (sub : ∀u v,slotCode (w:=w) P (u-v)=BinaryOp.bitXor.eval (slotCode P u) (slotCode P v))
    (graphRoom : p.oldGraph+6*(N*(cdStage).degree)≤2^w)
    (row : mem (regs 2).val=(key m.val:Word w)) (size : (cdStage).degree<2^w ∧ 2^t<2^w ∧ 2^l<2^w)
    (cw : c+1<w) (fit : 4≤2^w) (partyVal : (regs 3).val=partyId.val)
    (edgeVal : (regs 4).val=port.val.1.val) (bitVal : regs 5=(bit.val:Word w))
    (widthFit : ∀ a,prior a<2^w) (totalFit : CompressorPacking.thickWidth P prior (P.bundle m)<2^w)
    (qFit : Q<2^w) :
    (((lookup cdStage false (.reg 0) (.reg 2) (.reg 3) (.reg 4) (.reg 5) (.lit k.val) : Formula 13).compile
      (fun _=>(0:Fin 1))).eval (fun _=>0) mem regs) =
      (requestWord (S₀:=S₀) (P:=P) (prior:=prior) (q:=Q) key hQ num m port.val.2 port.val.1 bit
        (motifNumbers_bundle P key hc) lay (partySite P lay m partyId)
        (congrArg (partySite P lay m) port.property) k : Word w) := by
  let ptr' := Formula.reg (0:Fin 13)
  let eval:=Formula.value (fun _=>0) mem regs
  have atCell : eval ptr'=regs 0 := rfl
  let f:=atField (Demand.formulaOps 13) ptr'
  have mode : eval (f selected)=(if lay then 1 else 0) := by
    have z:=I.hdr.viewField ptr' atCell 27
    cases lay <;> simpa [Resident.value,selected] using z
  rw [lookup_compiled cdStage false lay k mem regs fit mode]
  have R:=I.viewArc ptr' E atCell number add sub
  have M:=mate_from_stored (S := cdStage) P E (fun _=>0) mem regs ptr' b (Resident.incoming cdStage N p) _
    I.graph number (I.hdr.viewField ptr' atCell 11) (I.hdr.viewField ptr' atCell 12) graphRoom
  have Wd:=I.viewWidths ptr' E atCell number
  have enc:=I.viewOldArc ptr' E atCell number add sub m (.reg 2) row size
    (Nat.pow_lt_pow_right (by decide : 1<2) cw)
  exact demand_port_native hQ R M Wd cw fit lay m partyId port
    (oldArc ptr' cdStage (.load (.reg 2))) (.reg 3) (.reg 4) (.reg 5) bit enc
    partyVal edgeVal bitVal widthFit totalFit qFit k


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins

end OAI
