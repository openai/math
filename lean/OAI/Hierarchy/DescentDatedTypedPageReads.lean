import OAI.Hierarchy.DescentOrdinaryPageMarks
import OAI.Hierarchy.DescentCompactedOperandHeaders
import OAI.Hierarchy.DescentDatedPreviousHeaderWords

namespace OAI
/-! # All four measured operand pages in a W gather use the same occupied row and old host -/
namespace Hierarchy.DescentOrdinaryReferenceInputs.Directory
open DescentPackedZip DescentSIMDLookup DescentPackedColony DescentHaloWalkRAM DescentOperandVectorArena
open DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOrdinaryOriginMask DescentOperandStateBanks
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

private theorem equal_host {H w : ℕ} (limit : H<2^w) (a b : Option (Fin H))
    (value : (DescentPackedColony.target a:Word w)=(DescentPackedColony.target b:Word w)) : a=b :=by
  have small (u : Option (Fin H)) : DescentPackedColony.target u<2^w:=by
    cases u with
    | none=>exact limit
    | some j=>exact j.isLt.trans limit
  have same:=congrArg Fin.val value
  rw [Fin.val_cast_of_lt (small a),Fin.val_cast_of_lt (small b)] at same
  cases a with
  | none=>
    cases b with
    | none=>rfl
    | some j=>exact False.elim (j.isLt.ne same.symm)
  | some i=>
    cases b with
    | none=>exact False.elim (i.isLt.ne same)
    | some j=>exact congrArg some (Fin.ext same)

variable {C : DescentOrdinaryRefsROM.Chart} {L : Layout} (dir : Directory C L)
    {H G n width nb mb M base w : ℕ} {m : Memory w}
local notation "P" => breadth C.degree
local notation "nodes" => DescentPackedActorMask.nodes (P*2^C.k) C.oldNodes C.capacity
variable (key : Fin 4 → Fin L.pageCount) (low : Fin L.lows) (rows : Fin L.pageCount → Fin L.lows → Values C.degree C.k C.oldNodes C.capacity H G width nb mb)
    (pages : ∀f,Measured (dir.refs (key f) low) (rows (key f) low) n M base m)
local notation "baseRow" => rows (key 0) low

include pages in
theorem indexed_pages (f : Fin 4) : DescentSortedRoster.indexed (rows (key f) low).walks=
    DescentSortedRoster.indexed (baseRow).walks :=by
  funext h p
  have off:=(pages 0).fromOld (0:Fin (2^C.k))
  apply equal_host (off.offRoom.trans_lt off.offsets.2.1)
  exact ((pages f).mounted.roster h p).symm.trans ((pages 0).mounted.roster h p)

include pages in
theorem typed_book_at (pitch : 0<M) (h : Fin H) (g : Fin G) (j : Fin n)
    (typed : ∀(u : Fin nodes) (site : Fin H),
      (encode 1 nodes).symm (marked baseRow h g) u≠0 →
      DescentSortedRoster.indexed (baseRow).walks h (bookRoot C.degree C.k C.oldNodes C.capacity u)=some site →
      TypedHeader (fun f=>item (rows (key f) low).old (rows (key f) low).born
        (bookBlock C.degree C.k C.oldNodes C.capacity u) (bookItem C.degree C.k C.oldNodes C.capacity u) site g)) :
    TypedHeader (fun f=>take j ((rows (key f) low).book n h g)) :=by
  let mask:=marked baseRow h g
  let records:=fun (f : Fin 4) (u : Fin nodes)=>
    (DescentSortedRoster.indexed (baseRow).walks h (bookRoot C.degree C.k C.oldNodes C.capacity u)).elim 0 (fun site=>
      item (rows (key f) low).old (rows (key f) low).born (bookBlock C.degree C.k C.oldNodes C.capacity u)
        (bookItem C.degree C.k C.oldNodes C.capacity u) site g)
  have same (f : Fin 4) : (rows (key f) low).book n h g=DescentPackedLocalAtoms.pack width nodes n mask
      (encode width nodes (records f)):=by
    have markedEq:=dir.marked_pages pitch (key f) (key 0) low (rows (key f) low) baseRow (pages f) (pages 0)
    have route:=dir.indexed_pages key low rows pages f
    unfold Values.book
    change DescentPackedLocalAtoms.pack width nodes n (marked (rows (key f) low) h g) _=_
    rw [markedEq,route]
  obtain ⟨u,hit,read⟩|miss:=packed_donor mask records j
  · have asRows : (fun f=>take j ((rows (key f) low).book n h g))=(fun f=>records f u):=by
      funext f
      rw [same]
      exact read f
    rw [asRows]
    cases located : DescentSortedRoster.indexed (baseRow).walks h (bookRoot C.degree C.k C.oldNodes C.capacity u) with
    | none=>simpa only [records,located,Option.elim_none] using (typed_zero (width:=width))
    | some s=>simpa only [records,located,Option.elim_some] using typed u s hit.1 located
  · have zero : (fun f=>take j ((rows (key f) low).book n h g))=(fun _ : Fin 4=>(0:Cell width)):=by
      funext f
      rw [same]
      exact miss f
    rw [zero]
    exact typed_zero

end
end Hierarchy.DescentOrdinaryReferenceInputs.Directory

end OAI
