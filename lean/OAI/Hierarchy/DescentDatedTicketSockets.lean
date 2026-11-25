import OAI.Hierarchy.DescentDatedTicketSocketCore
import OAI.Hierarchy.DescentOrdinaryRawObservedWords

namespace OAI
/-! # The retained and newborn tickets read from the six emitted raw material columns -/
namespace Hierarchy.DescentDatedOperandCoordinates.Ticket
open DescentSIMDLookup DescentRawCablePanel DescentRawCablePanel.DepotRAM
open DescentRawCablePanel.DepotRAM.Material
open scoped Fin.CommRing
noncomputable section
variable {s : DepotRAM.Shape} {P d : ℕ}

/-- Each column is the material read at that path and seat. Its enumeration is
the one used by the physical one-based choice table. -/
def rawHead (u : Setup) (state : Fin P→Parts s) (rev : Fin P→Cell (chartBits s)) (f : Fin 6)
    (j : Fin (P*(s.blocks*(s.cap*11)))) : Cell u.fieldBits :=
  let pos:=finProdFinEquiv.symm j
  let cell:=finProdFinEquiv.symm pos.2
  rawObserved s u (state pos.1) (rev pos.1) (cell.1,finProdFinEquiv.symm cell.2) f

theorem selected_raw (p : Fin P) (birth : Bool) (z : Seat s) (q : Cell d)
    (u : Setup) (state : Fin P→Parts s) (rev : Fin P→Cell (chartBits s))
    (present : q.val=socket p birth z) (f : Fin 6) :
    DescentResetStemMux.pick q (rawHead u state rev f)=rawObserved s u (state p) (rev p) z f := by
  rw [DescentResetStemMux.pick_actor q _ (finProdFinEquiv (p,seatNo z))
    (present.trans (socket_at p birth z))]
  simp only [rawHead,seatNo,Equiv.symm_apply_apply]

def current (u : Setup) (state : Fin P→Parts s) (rev : Fin P→Cell (chartBits s))
    (birth : Bool) (z : Seat s) (q : Cell d) (rank block start peer : ℕ) :=
  fields s.blocks (if birth then 2 else 1) 1 rank block q.val start peer z.2.2.val
    (anchor birth z) (fun f=>(DescentResetStemMux.pick q (rawHead u state rev f)).val)

variable (p : Fin P) (birth : Bool) (z : Seat s) (q : Cell d) (u : Setup)
    (state : Fin P→Parts s) (rev : Fin P→Cell (chartBits s)) (rank block start peer : ℕ)
local notation "measured" => rawObserved s u (state p) (rev p) z
local notation "word" => current u state rev birth z q rank block start peer

/-- The two capture arms store the reached donor and its original block.
A retained actor reads its role from the matcher, a birth from its mouth. -/
theorem at_socket (present : q.val=socket p birth z) :
    let got:=(measured 2).val≠0 ∨ (measured 3).val≠0
    word= ![if got then (measured 4).val*s.blocks+z.1.val else 0,(measured 2).val,
      (measured 3).val,if z.2.2.val=0 then (measured 5).val else 1,
      if got then 0 else start,if got then 0 else peer,z.2.1.val,z.2.2.val] := by
  unfold current
  rw [seat_fields p birth z q.val rank block start peer _ present]
  simp only [selected_raw p birth z q u state rev present]

theorem capture_at (present : q.val=socket p birth z) (hit : (measured 2).val≠0 ∨ (measured 3).val≠0) :
    word= ![(measured 4).val*s.blocks+z.1.val,(measured 2).val,(measured 3).val,
      if z.2.2.val=0 then (measured 5).val else 1,0,0,z.2.1.val,z.2.2.val] := by
  simpa only [ite_eq_left hit] using at_socket p birth z q u state rev rank block start peer present

theorem survivor_at (present : q.val=socket p birth z) (first : (measured 2).val=0) (second : (measured 3).val=0) :
    word= ![0,0,0,if z.2.2.val=0 then (measured 5).val else 1,start,peer,z.2.1.val,z.2.2.val] := by
  simpa [first,second] using at_socket p birth z q u state rev rank block start peer present

/-- Expand both flags into the old donor's actual before/after comparisons.
The second comparison contributes only when the first quotient did not capture. -/
theorem reported (present : q.val=socket p birth z) (flagRoom : 1<2^u.fieldBits) :
    let row:=report u.oldBits u.gain u.slots (seatDonor s u.profile u.motifWidth u.slots (state p) z.1 z.2.1) z.2.2
    let one:=(samePre row).toNat
    let two:=(!samePre row && samePost row).toNat
    let got:=one≠0 ∨ two≠0
    word= ![if got then (measured 4).val*s.blocks+z.1.val else 0,one,two,
      if z.2.2.val=0 then (rawAnchorMark s (state p) z.1 z.2.1).toNat else 1,
      if got then 0 else start,if got then 0 else peer,z.2.1.val,z.2.2.val] := by
  have bit (v : Bool) : (v.toNat : Cell u.fieldBits).val=v.toNat :=
    Fin.val_cast_of_lt (by cases v <;> simp_all)
  rw [at_socket p birth z q u state rev rank block start peer present]
  obtain ⟨first,second⟩:=raw_flags s u (state p) (rev p) z
  simp only [first,second,raw_mark,bit]

/-- A missing or padded socket has no capture, donor, continuation, or role. -/
theorem padding (absent : q.val=0) : word=fun _=>0 := by
  unfold current
  rw [absent]
  apply no_socket

end
end Hierarchy.DescentDatedOperandCoordinates.Ticket

end OAI
