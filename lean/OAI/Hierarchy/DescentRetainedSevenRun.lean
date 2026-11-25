import OAI.Hierarchy.DescentRetainedSeven

namespace OAI
namespace Hierarchy.DescentRetainedSeven.Chart
open DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM DescentPackedColony
open DescentPacking.PackedMatch.Local DescentSixParty.Chronology DescentResetRetainedSetup
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
variable {w : ℕ} (c : DescentRetainedSeven.Chart)
local notation "L" => c.retained

theorem intervals (floor : ℕ) : floor≤c.seen floor ∧ c.seen floor≤c.tabs floor ∧
    c.tabs floor≤c.lookup floor ∧ c.lookup floor≤c.place floor ∧ c.place floor≤c.endAddress floor:=by
  obtain ⟨a,b,d,e,f,_,_,_,_⟩:=(L).order floor
  obtain ⟨i,j,k,l⟩:=c.control.order (c.seen floor)
  refine ⟨(((a.trans b).trans d).trans e).trans f,i.trans ((Nat.le_add_right ..).trans (j.trans (k.trans l))),
    Nat.le_add_right ..,Nat.le_add_right ..,?_⟩
  rw [endAddress,DescentRetainedTargetPlacement.Chart.affine];exact Nat.le_add_right ..

def joinTables (floor : ℕ) :=DescentResetNodeBooks.tabs (c.tabs floor) (L).stripWord (L).channels (L).decodedLanes
def feeds (floor : ℕ) (which : c.control.Targets) (t : Fin c.placement.shapes) (j : Fin (L).channels) : Expr:=
  c.control.targetStream which (c.seen floor) t (.lookup ((L).hostBank floor j) .row)

theorem join_bounds (floor : ℕ) (which : c.control.Targets) (t : Fin c.placement.shapes)
    (room : c.place floor<2^w) : Gather.Bounds (w:=w) (d:=(L).stripWord) (M:=(L).decodedLanes)
      (c.joinTables floor) (c.feeds floor which t) (c.place floor):=by
  obtain ⟨_,ac,cd,de,_⟩:=c.intervals floor
  let out:=c.place floor
  have big:=cd.trans de
  have reads (j : Fin (L).channels) : (Expr.lookup ((L).hostBank floor j) .row).Fits w (c.tabs floor):=by
    have h:=(Strip.fits (w:=w) ((L).mixed floor) (L).hosts (L).grouped (L).matrixLanes (L).decodedLanes
      (L).stripWord j (ac.trans_lt (big.trans_lt room))).1
    exact ⟨⟨h.1,h.2.1,h.2.2.trans ac⟩,trivial⟩
  have address (i : Fin ((L).channels+1)):=ROM.bank_room
    (DescentResetNodeBooks.page (L).stripWord (L).channels (L).decodedLanes)
    (((L).siteWord+(L).stripWord)*(L).decodedLanes) (c.tabs floor) out i
    (DescentResetNodeBooks.page_bits ..) de room
  intro j
  have fit:=c.control.paths_fit which (c.seen floor) (.lookup ((L).hostBank floor j) .row) (.lit 0) t
    (reads j) trivial (big.trans_lt room)
  exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ big fit.1,address 0,address j.succ,rfl,rfl⟩

theorem lookup_fit (floor : ℕ) (which : c.control.Targets) (t : Fin c.placement.shapes) (o : Fin (L).outputs)
    (room : c.place floor<2^w) :
    (Expr.lookup (c.dictionary floor o) (c.joined floor which t)).Fits w (c.place floor):=by
  exact ⟨ROM.bank_room (L).wordPages ((L).siteWord*(L).decodedLanes) (c.lookup floor) (c.place floor) o le_rfl le_rfl room,
    Gather.fits _ _ _ (c.join_bounds floor which t room) _⟩

theorem term_fits (floor : ℕ) (which : c.control.Targets) (t : Fin c.placement.shapes) (o : Fin (L).outputs)
    (room : c.place floor<2^w) : (c.query floor which o t).Fits w (c.place floor):=by
  obtain ⟨_,_,cd,de,_⟩:=c.intervals floor
  have big:=cd.trans de
  have vfit:=c.lookup_fit floor which t o room
  unfold query
  split
  · exact vfit
  · have template:=ProtocolRAMGeneratedWrite.fits_mono _ big
      (c.control.paths_fit (w:=w) which (c.seen floor) (.lit 0) (.lit 0) t trivial trivial (big.trans_lt room)).2
    exact ⟨template.1,template.2.1,template.2.2.1,vfit⟩

theorem any (floor : ℕ) (which : c.control.Targets) (keep : Fin c.placement.shapes→Bool)
    (old : Fin (L).sources→Bank) (saved : Bank) (packet : Expr) (cnt inv : Bank) (m : Memory w)
    (orig : ∀i,(old i).Fits w floor) (key : saved.Fits w floor) (view : packet.Fits w floor)
    (ct : cnt.Fits w floor) (iv : inv.Fits w floor) (lanes : 0<c.placement.lanes) (blocks : 0<c.placement.blocks)
    (room : c.endAddress floor<2^w) :
    (c.program floor w which keep old saved packet cnt inv).Exec m (c.image floor which keep old saved packet cnt inv m)
      (c.ticks floor w which old saved packet cnt inv) ∧
      (∀z,z<floor ∨ c.endAddress floor≤z→c.image floor which keep old saved packet cnt inv m z=m z) ∧
      CheapCode (c.program floor w which keep old saved packet cnt inv):=by
  obtain ⟨a,b,d,e,f⟩:=c.intervals floor
  have R4:=f.trans_lt room
  have R3:=e.trans_lt R4
  have R2:=d.trans_lt R3
  have R1:=b.trans_lt R2
  have start : floor≤c.place floor:=((a.trans b).trans d).trans e
  have one:=(L).moved_any floor old saved m orig key R1
  have two:=c.control.any which (c.seen floor) packet ((L).movedImage floor old saved m)
    (ProtocolRAMGeneratedWrite.fits_mono _ a view) R2
  let m2:=c.selected which floor old saved packet m
  let m3:=c.joinMem floor m2
  have three:=ROM.run (DescentResetNodeBooks.page (L).stripWord (L).channels (L).decodedLanes)
    (((L).siteWord+(L).stripWord)*(L).decodedLanes) (c.tabs floor) m2 R3
  have four:=ROM.run (L).wordPages ((L).siteWord*(L).decodedLanes) (c.lookup floor) m3 R4
  have five:=DescentRetainedTargetPlacement.Chart.any c.placement c.batch (c.place floor) keep (c.terms floor which) cnt inv
    (c.prepared which floor old saved packet m) lanes blocks
    (fun j=>c.term_fits floor which (finProdFinEquiv.symm j).2 (finProdFinEquiv.symm j).1 R4)
    ⟨ct.1,ct.2.1,ct.2.2.trans start⟩ ⟨iv.1,iv.2.1,iv.2.2.trans start⟩ room
  refine ⟨?_,?_,cheap_seq (cheap_seq (cheap_seq (cheap_seq one.2.2 two.2.1) (ROM.cheap _ _ _ _)) (ROM.cheap _ _ _ _)) five.2.2⟩
  · unfold ticks
    simp only [Nat.mul_assoc]
    exact Procedure.Exec.then
      (Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then one.1 two.1) three.1) four.1)
      five.1
  · intro z hz
    apply (five.2.1 z (hz.imp_left (·.trans_le start))).trans
    apply (ROM.frame _ _ _ _ z (hz.imp (·.trans_le ((a.trans b).trans d)) (f.trans ·))).trans
    apply (ROM.frame _ _ _ _ z (hz.imp (·.trans_le (a.trans b)) ((e.trans f).trans ·))).trans
    apply (two.2.2 z (hz.imp (·.trans_le a) (((d.trans e).trans f).trans ·))).trans
    exact one.2.1 z (hz.imp_right ((((b.trans d).trans e).trans f).trans ·))

end
end Hierarchy.DescentRetainedSeven.Chart

end OAI
