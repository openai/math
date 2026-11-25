import OAI.Hierarchy.DescentResetSignedHaloDate
import OAI.Hierarchy.ProtocolRAMRowChoiceWork
import OAI.Hierarchy.DescentRosterExpressionPrice

namespace OAI
/-! # Price of the one signed old-halo matrix and all of its lookup expressions -/
namespace Hierarchy.DescentResetSignedHaloMatrix
open DescentPackedChildNeighbor.SIMD DescentSIMDLookup DescentSortedRoster DescentResetOriginHaloRAM
open DescentFallbackRankRAM DescentFallbackLeafScan ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical
noncomputable section

private theorem sums (xs : List Expr) (lim : ℕ) (small : ∀a∈xs,a.work≤lim) :
    (foldSum xs).work≤1+xs.length*(lim+1):=by
  induction xs with
  | nil=>simp [foldSum,Expr.work]
  | cons x xs ih=>
    have first:=small x (by simp)
    have rest:=ih (fun a ha=>small a (List.mem_cons_of_mem _ ha))
    change x.work+(foldSum xs).work+1≤_
    rw [List.length_cons,Nat.succ_mul]
    omega

def measuredWork (D : ℕ):=let b:=8+3*D;let n:=D+1
  1+n*(3*b+10+n*(2*b+2))

theorem measure_work {D : ℕ} (H : ℕ) (R : Bank) (v : Fin (D+1)) : (op H R v).work≤ measuredWork D:=by
  let b:=8+3*D
  let n:=D+1
  let src:=columns R (D:=D)
  have small (j : Fin n) : (src j).work≤b:=by
    induction j using Fin.lastCases with
    | last=>simp only [src,columns,Fin.lastCases_last,Expr.work,b]; omega
    | cast j=>simp [src,columns,opened,Expr.work,ProtocolRAM.scale_work,b];omega
  let test:=asked H (src v)
  have ask : test.work≤2*b+4:=by
    have:=small v
    change (src v).work+1+(src v).work+2+1≤_
    omega
  let bound:=3*b+9+n*(2*b+2)
  have guard (j : Fin n) (e : Expr) (xs : List (Fin n)) :
      (unlessSeen (src j) e (xs.map src)).work≤e.work+xs.length*(2*b+2):=by
    induction xs with
    | nil=>simp [unlessSeen]
    | cons i is ih=>
      change (src i).work+(src j).work+1+(unlessSeen (src j) e (is.map src)).work+1≤_
      rw [List.length_cons,Nat.succ_mul]
      have:=small i;have:=small j;omega
  have bits (j : Fin n) : (rankBit src test j).work≤bound:=by
    have h:=guard j (.branch .lt (src j) test (.lit 1) (.lit 0)) (prior j)
    have len : (prior j).length≤n:=by
      simpa [prior,Finset.length_toList] using (Finset.card_filter_le (s:=Finset.univ) (fun i : Fin n=>i<j))
    have length:=Nat.mul_le_mul_right (2*b+2) len
    change (rankBit src test j).work≤(src j).work+test.work+1+1+1+(prior j).length*(2*b+2) at h
    have:=small j
    dsimp [bound]
    omega
  have calculation:=sums ((Finset.univ:Finset (Fin n)).toList.map (rankBit src test)) bound (by
    intro z member
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp member
    exact bits j)
  have step : bound+1=3*b+10+n*(2*b+2) := by dsimp only [bound]; omega
  change (calculate src test).work≤1+n*(3*b+10+n*(2*b+2))
  simpa only [calculate,List.length_map,Finset.length_toList,Finset.card_univ,Fintype.card_fin,step] using calculation

def termWork (D : ℕ):=19+(D+1)*(9+13*measuredWork D)

theorem term_work (H D S base : ℕ) (cnt own near : Bank) : (term H D S base cnt own near).work≤termWork D:=by
  let point:=Expr.lookup own (key H D base 0)
  let choice:=fun j : Fin (D+1)=>(op S near j).atRow point
  have input (j : Fin (D+1)) : (choice j).work≤13*measuredWork D:=by
    have hi:=Calendar.CatalogueRows.substitute_work (op S near j) point
    exact hi.trans (by simpa only [point,key,Expr.work,Nat.mul_comm] using Nat.mul_le_mul_right 13 (measure_work S near j))
  have choose:=BoughtSockets.choose_work_bound (D+1) 0 (13*measuredWork D) choice (key H D base 1) input
  change 7+6+((chooseField (D+1) 0 choice (key H D base 1)).work+1+1)+1+1≤_
  change (chooseField (D+1) 0 choice (key H D base 1)).work≤1+(D+1)*(7+13*measuredWork D+2) at choose
  rw [show 7+13*measuredWork D+2=9+13*measuredWork D by omega] at choose
  dsimp only [termWork]
  omega

theorem Shelf.port_work (C : Shelf) (q : Expr) : (C.port q).work=1+(C.degree+1)*(q.work+48):=by
  have decoderWork : (query C.degree C.cap C.signedBits C.queryBits C.lanes C.decodeAt q).work=q.work+12 := by
    simp only [query,DescentPackedZip.Tables.read,Expr.work]
    omega
  simp only [Shelf.port,DescentPackedChildNeighbor.SIMD.work,List.length_finRange,decoderWork,Nat.add_assoc]

theorem Shelf.tariff (C : Shelf) : C.ticks≤4+10*cells C.hosts C.degree+
    (4+C.hosts*(C.degree+1)*(2*termWork C.degree+4))+
    (4+10*C.delta)+(4+10*C.count):=by
  have limit:=term_work C.hosts C.degree C.oldHosts C.root C.oldCount C.owner C.oldRoster
  dsimp only [Shelf.ticks,clock]
  gcongr

theorem Shelf.hardware (C : Shelf) (w : ℕ) :
    DescentStaticWordColumn.names (C.cpu w)≤15*(cells C.hosts C.degree+1)+
      (11+4*termWork C.degree)+15*(C.delta+1)+15*(C.count+1):=by
  have limit:=term_work C.hosts C.degree C.oldHosts C.root C.oldCount C.owner C.oldRoster
  simp only [Shelf.cpu,program,DescentOrdinaryAtomFieldRAM.ROM.mount,DescentPackedChildNeighbor.SIMD.ROM.program,
    DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_scan,DescentStaticWordColumn.names_mount]
  change 15*(cells C.hosts C.degree+1)+(11+4*_)+15*(C.delta+1)+15*(C.count+1)≤_
  omega

end
end Hierarchy.DescentResetSignedHaloMatrix

end OAI
