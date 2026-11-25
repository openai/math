import OAI.Hierarchy.DescentResetRetainedResidents

namespace OAI
/-! # Genuine selected source, raw donor, and retained field reads in the issued memory -/
namespace Hierarchy.DescentResetRetainedSetup.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOrdinaryAtomFieldRAM DescentPacking.PackedMatch.Local
open DescentSixParty.Chronology Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ} (v : Layout)

theorem function_zero (i : Fin v.outputs) : v.function i 0=0 :=by
  unfold function
  split
  · exact v.decode_zero ..
  · simp [donorDigit,v.root_zero]

abbrev Strips := Fin v.channels→Fin v.hosts→Fin v.grouped→Cell v.stripWord
def site (x : v.Strips) (h : Fin v.hosts) (g : Fin v.grouped) :=encode v.stripWord v.channels (fun j=>x j h g)

/-- Every lane of the final retile comes from a native lookup of the complete
local donor strip that was written by the preceding chosen-matrix program. -/
theorem reads (base : ℕ) (old : Fin v.sources→Bank) (saved : Bank) (m : Memory w) (space : v.endAddress base<2^w)
    (positive : 0<v.decodedLanes) (x : v.Strips)
    (incoming : ∀j,Reads (v.hostBank base j) (x j) v.decodedLanes (v.movedImage base old saved m)) (i : Fin v.outputs) :
    Reads (v.bank base i) (fun h g=>v.function i (v.site x h g)) v.emitLanes (v.image base old saved m) :=by
  obtain ⟨_,_,_,_,_,lo,hi,done_,end_⟩:=v.order base
  let src:=v.movedImage base old saved m
  let middle:=v.joinedImage base src
  let dict:=v.looked base src
  have outRoom:= (done_.trans end_).trans_lt space
  have guard :=lo.trans hi
  have before (z : ℕ) (below:z<v.tables base) : dict z=src z :=
    (ROM.frame _ _ _ _ _ (.inl (below.trans_le lo))).trans (ROM.frame _ _ _ _ _ (.inl below))
  have oldFit (j : Fin v.channels) :=Strip.fits (w:=w) (v.mixed base) v.hosts v.grouped v.matrixLanes
    v.decodedLanes v.stripWord j (guard.trans_lt outRoom)
  have seen (j : Fin v.channels) : Source (.lookup (v.hostBank base j) .row) (x j) v.decodedLanes dict:=by
    apply source_column _ _ ((v.joinBounds base outRoom j).1.1) dict _ (oldFit j).2
    intro p
    have b:=(Nat.add_lt_add_left ((row _ _ _ p).isLt.trans_le (oldFit j).2) _).trans_le (oldFit j).1.2.2
    exact (before _ b).trans (incoming j p)
  have table (j : Fin v.channels) : Static (v.joinTables base j) (Gather.setField (d:=v.stripWord) j) v.decodedLanes dict:=by
    let T:=v.joinTables base j
    have fixed:=DescentResetNodeBooks.static (v.tables base) v.channels v.stripWord v.decodedLanes src j
    have shelf (z : Fin (v.channels+1)):=ROM.bank_room (DescentResetNodeBooks.page v.stripWord v.channels v.decodedLanes)
      ((v.siteWord+v.stripWord)*v.decodedLanes) (v.tables base) (v.decode base) z (DescentResetNodeBooks.page_bits ..) le_rfl
      (hi.trans_lt outRoom)
    constructor
    · intro t
      have e:= (Nat.add_lt_add_left t.isLt T.shift.base).trans_le (shelf 0).2.2
      exact (ROM.frame _ _ _ _ _ (.inl e)).trans (fixed.1 t)
    · intro t
      have e:= (Nat.add_lt_add_left t.isLt T.apply.base).trans_le (shelf j.succ).2.2
      exact (ROM.frame _ _ _ _ _ (.inl e)).trans (fixed.2 t)
  have got:=Gather.collected (v.joinTables base) _ (v.out base) (v.joinBounds base outRoom)
    dict table (fun h g j=>x j h g) seen (List.finRange v.channels)
  have whole : Source (v.oldSite base) (v.site x) v.decodedLanes dict:=by
    unfold site
    simpa only [oldSite,Gather.assembly,List.mem_finRange,ite_true] using got
  have print (p : Row v.hosts v.grouped v.decodedLanes) :
      (v.readTerm base i.val).eval dict ((row _ _ _ p).val:Word w)=
        ((data (fun h g=>v.function i (v.site x h g)) p).val:Word w):=by
    let bank_:=v.dictionary base i
    have safe:=ROM.bank_room v.wordPages (v.siteWord*v.decodedLanes) (v.decode base) (v.out base) i le_rfl le_rfl outRoom
    rw [readTerm,dite_eq_left i.isLt]
    change bank_.read dict ((v.oldSite base).eval dict _)=_
    rw [whole]
    refine (bank_read bank_ dict (data (v.site x) p).isLt safe).trans ?_
    have lut:=ROM.read v.wordPages (v.siteWord*v.decodedLanes) (v.decode base) middle i le_rfl (data (v.site x) p)
    apply lut.trans
    apply congrArg (fun u : Cell (v.bits*v.decodedLanes)=>(u.val:Word w))
    simp only [DescentSIMDLookup.table,data,Equiv.symm_apply_apply]
    apply congrArg (encode _ _);funext j
    by_cases live:p.2.val*v.decodedLanes+j.val<v.grouped <;> simp [live,v.function_zero]
  have finite : v.out base+v.outputs*v.rows≤v.reissue base:=Nat.le_add_right ..
  have last:=DescentPackedFlowBatch.execute (v.out base) v.rows v.rows v.outputs (v.readTerm base) dict
    (fun j hj=>v.readFits base j hj outRoom) ((finite.trans end_).trans_lt space) le_rfl
  apply Strip.read (v.reissue base) v.hosts v.grouped v.decodedLanes v.emitLanes v.bits (v.originalOutput base)
    (v.writeImage base src) (fun j=>(v.validOutput base j (end_.trans_lt space)).1) space i _ positive
    (v.validOutput base i (end_.trans_lt space)).2
  intro p
  exact (last.2.1 i (row _ _ _ p)).trans (print p)

end
end Hierarchy.DescentResetRetainedSetup.Layout

end OAI
