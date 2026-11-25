import OAI.Hierarchy.DescentTerminalHeaderGroups

namespace OAI
/-! # A static cable-width scan and its two genuine EOF cells -/
namespace Hierarchy.DescentTerminalHeaderGroups
open DescentTerminalDenseWindow DescentTerminalDenseHeader DescentTerminalCableOrder
open DescentTerminalGraphPositions DescentTerminalDenseCableFetch
open ThreeFlat.Routing Computability.BorderVNP.Crossing Computability.VPVNP.BurstRAM
open scoped BigOperators Classical
open scoped Fin.CommRing
noncomputable section

def padded {q p n : ℕ} (t : List (Profile q p)) (i : Fin n) : Profile q p :=
  if live : i.val<t.length then t.get ⟨_,live⟩ else fun _=>0

theorem zero_mass (q p : ℕ) : mass (fun _ : Fin q=>(0:Fin (p+1)))=0 := by
  unfold mass slotPrefix
  have h (k : ℕ) : pref (fun _ : Fin q=>0) k=0 := by
    induction k with
    | zero=>rfl
    | succ k ih=>simp [pref,ih,lengthAt]
  exact h q

theorem prior_padded {q p n : ℕ} (t : List (Profile q p)) (room : t.length ≤ n) (k : ℕ) :
    priorBits (padded (n:=n) t) k=priorBits t.get k := by
  induction k with
  | zero=>rfl
  | succ k ih=>
    change priorBits _ k+lengthAt _ k=priorBits _ k+lengthAt _ k
    rw [ih]
    congr 1
    by_cases live : k<t.length
    · simp [lengthAt,padded,live,live.trans_le room]
    · by_cases inBand : k<n <;> simp [lengthAt,padded,live,inBand,zero_mass]

theorem fixed_scan {bitsW n q p : ℕ} (layout : DescentTerminalDenseHeaderRAM.Layout)
    (t : List (Profile q p)) (room : t.length ≤ n) (pos : 0<q*p) (m : Memory bitsW)
    (fit : DescentTerminalDenseHeaderRAM.Fits layout bitsW n)
    (inputs : DescentTerminalDenseHeaderRAM.Reads layout (padded (n:=n) t) m) :
    ∃after,(DescentTerminalDenseHeaderRAM.program bitsW n layout).Exec m after (DescentTerminalDenseHeaderRAM.cost n layout) ∧
      (DescentTerminalDenseHeaderRAM.eof after layout.whole n=((listMass t/(q*p):ℕ):Word bitsW) ∧
       DescentTerminalDenseHeaderRAM.eof after layout.rem n=((listMass t%(q*p):ℕ):Word bitsW)) ∧
      ∀i : Fin t.length, after (layout.index.base+i.val)=DescentTerminalDenseHeaderRAM.wholeVal t.get i.val ∧
        after (layout.control.base+i.val)=DescentTerminalDenseHeaderRAM.Header t.get pos i := by
  obtain ⟨after,run,state,writes⟩:=DescentTerminalDenseHeaderRAM.exec_state layout (padded t) pos m fit inputs
  have full : priorBits (padded (n:=n) t) n=listMass t := by
    rw [prior_padded t room]
    change pref (fun i=>mass (t.get i)) n=_
    rw [pref_ended _ n room]
    simpa only [priorBits,List.take_length] using prior_list t t.length le_rfl
  have eofW:=DescentTerminalDenseHeaderRAM.eof_read after layout.whole
    (DescentTerminalDenseHeaderRAM.wholeVal (bits:=bitsW) (padded (n:=n) t))
    (by simp [DescentTerminalDenseHeaderRAM.wholeVal,prior_zero]) (fun i=>(state i).2)
  have eofR:=DescentTerminalDenseHeaderRAM.eof_read after layout.rem
    (DescentTerminalDenseHeaderRAM.remVal (bits:=bitsW) (padded (n:=n) t))
    (by simp [DescentTerminalDenseHeaderRAM.remVal,prior_zero]) (fun i=>(state i).1)
  refine ⟨after,run,⟨by simpa [DescentTerminalDenseHeaderRAM.wholeVal,full] using eofW,
    by simpa [DescentTerminalDenseHeaderRAM.remVal,full] using eofR⟩,fun i=>?_⟩
  simpa [DescentTerminalDenseHeaderRAM.Header,DescentTerminalDenseHeaderRAM.wholeVal,padded,i.isLt,
    prior_padded t room] using writes (i.castLE room)

variable {q p : ℕ}
variable {D S : ℕ} {P : Type} [Fintype P] {bits : P→ℕ} (N : Network D P bits)
    (home : N.Site→Fin S) (native : N.Edge ↪ Fin (Fintype.card N.Edge))
    (external : P ↪ ℕ) (nodes : N.Site ↪ ℕ) (ops : ∀v,DescentKernelHistory.Boundary N v ↪ ℕ)
local notation "L" => order N home native p external nodes ops
theorem native_headers_eof_fixed {bitsW nFixed : ℕ} (layout : DescentTerminalDenseHeaderRAM.Layout) (m : Memory bitsW)
    (hq : 0<q) (hp : 0<p) (limit : ℕ) (room : (stream N home native external nodes ops q hp limit).length ≤ nFixed)
    (fits : DescentTerminalDenseHeaderRAM.Fits layout bitsW nFixed)
    (reads : DescentTerminalDenseHeaderRAM.Reads layout (padded (n:=nFixed) (stream N home native external nodes ops q hp limit)) m) :
    let _tape:=stream N home native external nodes ops q hp limit
    ∃after,(DescentTerminalDenseHeaderRAM.program bitsW nFixed layout).Exec m after
      (DescentTerminalDenseHeaderRAM.cost nFixed layout) ∧
      (DescentTerminalDenseHeaderRAM.eof after layout.whole nFixed=
          ((beforePair N home limit/(q*p):ℕ):Word bitsW) ∧
       DescentTerminalDenseHeaderRAM.eof after layout.rem nFixed=
          ((beforePair N home limit%(q*p):ℕ):Word bitsW)) ∧
      ∀(t : ℕ) (_less : t<limit) (positive : 0<pairMass N home t),
      let g:=selected N home native external nodes ops hp t positive
      let pre:=stream N home native external nodes ops q hp t
      ∀r : Fin (poolBatchCount (Fintype.card (Order.At L g.site g.group)) q),
        let request : Packet N L q:=⟨g.site,g.other,g.group,g.near,r⟩
        after (layout.index.base+(pre.length+r.val))=(index N home native external nodes ops request:Word bitsW) ∧
          after (layout.control.base+(pre.length+r.val))=
            ((formatIndex q p (fmt N home native external nodes ops (Nat.mul_pos hq hp) request)).val:Word bitsW) := by
  intro tape
  have pos:=Nat.mul_pos hq hp
  obtain ⟨after,run,state,rowReads⟩:=fixed_scan layout tape room pos m fits reads
  have total : listMass tape=beforePair N home limit:=stream_mass N home native external nodes ops hq hp limit
  refine ⟨after,run,by simpa [total] using state,?_⟩
  intro t less positive g pre r packet
  obtain ⟨post,cut⟩:=stream_split N home native external nodes ops hq hp t limit less positive
  obtain ⟨start,profile⟩:=within N home native external nodes ops hq hp t positive post r.val r.isLt
  have tapeEq : tape=pre++g.rows q++post:=cut
  rw [←tapeEq] at start profile
  let i : Fin tape.length:=⟨pre.length+r.val,by
    have h : r.val<(g.rows q).length:=by simp [GroupBlock.rows]
    rw [tapeEq,List.length_append,List.length_append];omega⟩
  have pick : tape.get i=rowProfile g.lengths g.small r.val := by
    rw [List.getElem?_eq_getElem i.isLt] at profile
    exact Option.some.inj profile
  obtain ⟨a,b⟩:=rowReads i
  have startAt : priorBits tape.get i.val=first g.lengths q (pairBase N home g.site g.other) r.val := start
  constructor
  · exact a.trans (congrArg (fun k : ℕ=>((k/(q*p):ℕ):Word bitsW)) startAt)
  · have datum:=control_row g.lengths g.small pos (pairBase N home g.site g.other) r.val
    have residue : (⟨priorBits tape.get i.val%(q*p),Nat.mod_lt _ pos⟩:Fin (q*p))=
        ⟨first g.lengths q (pairBase N home g.site g.other) r.val%(q*p),Nat.mod_lt _ pos⟩ :=
      Fin.ext (congrArg (fun k : ℕ=>k%(q*p)) startAt)
    change after (layout.control.base+i.val)=((formatIndex q p (format g.lengths pos g.small
      (pairBase N home g.site g.other) r.val)).val:Word bitsW)
    rw [b,DescentTerminalDenseHeaderRAM.Header,pick,residue,datum]

end
end Hierarchy.DescentTerminalHeaderGroups

end OAI
