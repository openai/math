import OAI.Hierarchy.DescentOrdinaryPrimitivePrior
import OAI.Hierarchy.DescentDatedTicketPreparationTotal

namespace OAI
/-! The returned W census is retained across the remaining instructions of the ordinary date. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentOrdinaryOriginMask
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentPackedZip
open DescentOrdinaryAtomFieldRAM DescentPackedColony DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage.Chooser
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F I : Type} [Field F] (v : PhysicalOrdinary F I)
variable (floor w : ℕ) (c : v.SignedChart) (A : v.ArgumentEntry) (mat : A.Match v floor)
    (shape : v.VectorShape) (blocks : v.resolver.blocks=v.material.blocks) (pg : Fin (7*v.vector.operands))
    (admission : v.TicketAdmission floor w c A mat pg)
    (total : v.origin.preparationWords=v.originControlWords+v.originMouthWords+v.rootSourceSize)
    (donor : (A.chipBank v floor).Fits w (v.refsStart floor)) (fit : v.endAddress floor<2^w)
    (wide : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2)
    (paid : NativePhase w) (charge : Span paid (v.endAddress floor) (v.rasterEnd floor))
    (columns : StageVenueTail.Sources) (survivors : v.ResultRoom floor columns w) (m : Memory w)
local notation "route" => v.routedStart floor
local notation "C" => (A.directory v floor mat).refs
local notation "prep" => v.nativeTicketPreparation floor w c A mat shape blocks pg
local notation "src" => v.nativeTicketExpr floor c A mat shape blocks
local notation "installed" => v.mountImage floor (A.chipBank v floor) ((A.inlet v floor w).image m)
local notation "gathered" => ((C).phase w (v.vectorStart floor)).image installed
local notation "earlier" => v.originChart.image ((C) pg) route gathered
local notation "args_" => (v.argumentPhaseAfterSigned floor A mat src prep donor shape fit wide).image m
local notation "final_" => (v.returnPhase floor columns w survivors).image (paid.image args_)

include admission total charge in
theorem primitive_origin_frame (i : ℕ) (early : i<v.originPortFloor floor) : final_ i=earlier i:=by
  obtain ⟨_,_,raw,normalized,last⟩:=v.routed_order floor
  obtain ⟨_,a,b,c₁,d,e,f,g,h⟩:=v.ticket_source_order floor
  have mid:=a.trans (b.trans (c₁.trans (d.trans (e.trans (f.trans (g.trans h))))))
  have equal:=v.grain_after_sources floor total
  have onset : i<v.origin.grainBase route:=equal.symm ▸ early.trans_le mid
  have cap:=raw.trans (normalized.trans last)
  have prepFit : v.preparedUntil floor<2^w:=equal ▸ cap.trans_lt fit
  have trace:=v.ticket_preparation_trace floor w c A mat shape blocks pg admission prepFit gathered
  let a₀:=(prep).image gathered
  let a₁:=(v.grainPhase floor w).image a₀
  let a₂:=(v.rasterPhase floor src w).image a₁
  have source : ∀j f,(src j f).Fits w (v.origin.outputBase route):=fun j f=>
    ProtocolRAMGeneratedWrite.fits_mono _ (equal ▸ raw) (trace.1.2 j f)
  have page:=v.origin.publish src route a₁ (last.trans_lt fit) source
  have addresses:=v.origin.ports_fit route w (last.trans_lt fit)
  have resolve:=v.operand_any_from_vector floor _ _ a₂ shape addresses.1 addresses.2 fit wide
  have readGrain:=DescentDatedPublicGrain.frame v.resolver _ v.chosenGrain a₀ i (.inl onset)
  have tail:=(v.returnPhase_run floor columns w survivors (paid.image args_)).2 i
    (.inl (((onset.trans_le cap).trans_le charge.1)))
  exact tail.trans (((charge.2 args_).2 i (.inl (onset.trans_le cap))).trans
    ((resolve.2.1 i (.inl ((onset.trans_le raw).trans_le normalized))).trans
      ((page.2.2.1 i (.inl (onset.trans_le raw))).trans (readGrain.trans (trace.2 i early)))))

include total fit in
private theorem primitive_origin_fit : v.originPortFloor floor<2^w:=by
  obtain ⟨_,a,b,c₁,d,e,f,g,h⟩:=v.ticket_source_order floor
  obtain ⟨_,_,r,s,t⟩:=v.routed_order floor
  exact (a.trans (b.trans (c₁.trans (d.trans (e.trans (f.trans (g.trans h))))))).trans_lt
      ((v.grain_after_sources floor total) ▸ (r.trans (s.trans t)).trans_lt fit)

include admission total charge in
theorem primitive_origin {a nb mb : ℕ}
    (V : Fin v.vector.lows→Values v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity
      v.vector.hosts (v.vector.groups*v.vector.radix) a nb mb)
    (measured : ∀i,Measured ((C) pg i) (V i) v.resolver.nodes (v.vector.lanes*v.vector.radix) route gathered)
    (x : Fin v.vector.radix) :
    Reads (v.originBank floor x)
      (DescentScalarBookReshape.book (fun l h g=>selection v.originCandidates v.resolver.nodes v.originBits
        (marked (V l) h g)) x) v.vector.lanes final_:=by
  have hi:=v.primitive_origin_fit floor w total fit
  have read:=v.originChart.originReturned ((C) pg) route gathered admission.lanes admission.radix V measured hi x
  have placed:=v.originChart.grid.returned_fits (v.originChart.rowsAt route) x hi
  exact reads_before _ _ earlier _ read
    (v.primitive_origin_frame floor w c A mat shape blocks pg admission total donor fit wide paid charge columns survivors m)
    placed.1 placed.2

include admission total charge in
/-- The earlier W measurements can be taken on the actual mounted bank before the seven
argument-page gather. Only the packed occupied mask is read by the subsequent origin lookup. -/
theorem primitive_origin_from_W {a nb mb : ℕ}
    (gatherRoom : (C).Room w (v.vectorStart floor))
    (V : Fin v.vector.lows→Values v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity
      v.vector.hosts (v.vector.groups*v.vector.radix) a nb mb)
    (measured : ∀i,Measured ((C) pg i) (V i) v.resolver.nodes (v.vector.lanes*v.vector.radix)
      (v.vectorStart floor) installed)
    (x : Fin v.vector.radix) :
    Reads (v.originBank floor x)
      (DescentScalarBookReshape.book (fun l h g=>selection v.originCandidates v.resolver.nodes v.originBits
        (marked (V l) h g)) x) v.vector.lanes final_:=by
  let R:=v.originChart
  let n:=v.originCandidates
  let oldM:=v.vector.lanes*v.vector.radix
  have hi:=v.primitive_origin_fit floor w total fit
  have issued:=((C).any (v.vectorStart floor) installed gatherRoom)
  have earlierMask (l : Fin v.vector.lows) :
      (mask ((C) pg l)).Fits w route ∧ Source (mask ((C) pg l)) (marked (V l)) oldM gathered:=by
    have initial:=read_mask ((C) pg l) (V l) (measured l)
    refine ⟨ProtocolRAMGeneratedWrite.fits_mono _ (v.vector_before floor) initial.1,fun row=>?_⟩
    exact (ProtocolRAM.eval_below _ _ installed gathered initial.1 (fun u hu=>issued.2 u (.inl hu))).trans
      (initial.2 row)
  have got (l : Fin v.vector.lows):=
    DescentOperandFamilyBook.issued R.law (dead n v.resolver.nodes v.originBits) oldM route 0
      (fun _ : Fin 1=>mask ((C) pg l)) gathered (fun h g (_:Fin 1)=>marked (V l) h g)
      (fun _=>(earlierMask l).1) (fun _=>(earlierMask l).2) (R.table_before route hi)
  have read:=R.grid.originReturned (R.rowsAt route) (R.expr ((C) pg) route) _
    (fun l=>(got l).1) hi admission.lanes admission.radix _ (fun l=>(got l).2) x
  have placed:=R.grid.returned_fits (R.rowsAt route) x hi
  exact reads_before _ _ earlier _ read
    (v.primitive_origin_frame floor w c A mat shape blocks pg admission total donor fit wide paid charge columns survivors m)
    placed.1 placed.2

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
