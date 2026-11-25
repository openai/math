import OAI.Hierarchy.DescentOrdinaryCompactRack
import OAI.Hierarchy.DescentOrdinaryCompactPeer

namespace OAI
/-! # Install the immutable shape header of the eight-hop peer conversion -/
namespace Hierarchy.DescentOrdinaryCompactPeer.ROM
open DescentPackedChildNeighbor DescentHaloWalkRAM DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {N H L Q D w : ℕ}
local notation "rows" => H*(L*Q)

def field (N D pitch : ℕ) (q : DescentOrdinaryCompactPeer.Key H L Q) : Fin 5→ℕ :=
  ![(rack N pitch q.1).isSome.toNat,(q.1.val/pitch)*L,q.2.1.val,q.2.2.val,q.1.val*D]

def place (base H L Q i : ℕ) :=base+i*(H*(L*Q))
def shapes (base H L Q i : ℕ) : Bank := ⟨place base H L Q i,Nat.clog 2 (H*(L*Q)+1)⟩
def layout (base N H L Q : ℕ) (ranks ends neighbors : Bank) : DescentPackedChildNeighbor.Banks :=
  ⟨ranks,ends,neighbors,⟨place base H L Q 5,Nat.clog 2 (N+1)⟩,
    shapes base H L Q 1,shapes base H L Q 2,shapes base H L Q 3,shapes base H L Q 4⟩

def count (N H L Q : ℕ) :=5*(H*(L*Q))+N
def contents (N H L Q D pitch j : ℕ) :=
  let n:=H*(L*Q)
  if inRows : j<5*n then
    let z:Fin 5×Fin n:=finProdFinEquiv.symm ⟨j,inRows⟩
    field N D pitch ((DescentOrdinaryCompactPeer.index H L Q).symm z.2) z.1
  else (j-5*n)*pitch

def program (base N H L Q D pitch w : ℕ) :=DescentStaticWordColumn.program w base (contents N H L Q D pitch) (count N H L Q)
def after (base N H L Q D pitch : ℕ) (m : Memory w) :=DescentStaticWordColumn.image base (contents N H L Q D pitch) m (count N H L Q)

theorem code_names (base N H L Q D pitch w : ℕ) : DescentStaticWordColumn.names (program base N H L Q D pitch w)=15*(count N H L Q+1) :=DescentStaticWordColumn.names_mount ..

theorem query_read (base N D pitch : ℕ) (m : Memory w) (q : DescentOrdinaryCompactPeer.Key H L Q) (i : Fin 5) :
    after base N H L Q D pitch m (place base H L Q i.val+(DescentOrdinaryCompactPeer.index H L Q q).val)=(field N D pitch q i:Word w) :=by
  let j : Fin (5*rows):=finProdFinEquiv (i,DescentOrdinaryCompactPeer.index H L Q q)
  have ix : j.val=i.val*rows+(DescentOrdinaryCompactPeer.index H L Q q).val:=by simp [j,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  have room : j.val<count N H L Q:=j.isLt.trans_le (Nat.le_add_right ..)
  rw [place,Nat.add_assoc,←ix,after,DescentStaticWordColumn.read _ _ _ _ room]
  simp only [contents,dite_eq_left j.isLt]
  let unpair : Fin (5*rows) ≃ Fin 5 × Fin rows := finProdFinEquiv.symm
  change (field N D pitch ((DescentOrdinaryCompactPeer.index H L Q).symm (unpair j).2)
    (unpair j).1 : Word w) = _
  have unpack : unpair j = (i,DescentOrdinaryCompactPeer.index H L Q q) :=
    finProdFinEquiv.symm_apply_apply _
  rw [unpack,Equiv.symm_apply_apply]

theorem scale_read (base D pitch : ℕ) (m : Memory w) (v : Fin N) :
    after base N H L Q D pitch m (place base H L Q 5+v.val)=((v.val*pitch:ℕ):Word w) :=by
  have room : 5*rows+v.val<count N H L Q:=Nat.add_lt_add_left v.isLt _
  rw [place,Nat.add_assoc,after,DescentStaticWordColumn.read _ _ _ _ room]
  simp only [contents,dite_eq_right (Nat.not_lt.mpr (Nat.le_add_right ..)),Nat.add_sub_cancel_left]

theorem mounted (ranks ends neighbors : Bank) (base pitch : ℕ) (m : Memory w) (old : Fin N→Fin L→Option (Fin N))
    (next : Fin H→Fin D→Option (Fin H))
    (pr : ranks.base+N*L≤base) (pe : ends.base+N*L≤base) (pn : neighbors.base+H*D≤base)
    (rk : ∀v j,m (ranks.base+(v.val*L+j.val))=(rank old v j:Word w))
    (en : ∀v j,m (ends.base+(v.val*L+j.val))=(number (old v j):Word w))
    (sorted : ∀v j,m (neighbors.base+(v.val*D+j.val))=(number (next v j):Word w)) :
    DescentOrdinaryCompactPeer.Mounted (Q:=Q) (layout base N H L Q ranks ends neighbors) (shapes base H L Q 0) pitch (rack N pitch) old next (after base N H L Q D pitch m) := by
  have range_ {a b : ℕ} (i : Fin a) (j : Fin b) : i.val*b+j.val<a*b := (Nat.add_lt_add_left j.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ i.isLt)
  have below (j : ℕ) (lt : j<base) : after base N H L Q D pitch m j=m j :=DescentStaticWordColumn.frame _ _ _ _ j (.inl lt)
  refine ⟨fun z=>query_read base N D pitch m z 0,?_,fun z=>query_read base N D pitch m z 2,
    fun z=>query_read base N D pitch m z 3,fun z=>query_read base N D pitch m z 4,scale_read base D pitch m,?_,?_,?_⟩
  · intro z v hr
    have eqn : v.val=z.1.val/pitch := by
      unfold rack at hr
      split at hr
      · cases hr
        rfl
      · contradiction
    simpa [layout, shapes, field, eqn] using query_read base N D pitch m z 1
  · intro v j;exact (below _ ((Nat.add_lt_add_left (range_ v j) _).trans_le pr)).trans (rk v j)
  · intro v j;exact (below _ ((Nat.add_lt_add_left (range_ v j) _).trans_le pe)).trans (en v j)
  · intro v j;exact (below _ ((Nat.add_lt_add_left (range_ v j) _).trans_le pn)).trans (sorted v j)

/-- Read the same public words when a shared chronological dispatcher, rather than
the standalone mount, issued them in the current memory. -/
theorem mounted_on (ranks ends neighbors : Bank) (base pitch : ℕ) (m : Memory w)
    (old : Fin N→Fin L→Option (Fin N)) (next : Fin H→Fin D→Option (Fin H))
    (words : ∀j : Fin (count N H L Q),m (base+j.val)=(contents N H L Q D pitch j.val:Word w))
    (rk : ∀v j,m (ranks.base+(v.val*L+j.val))=(rank old v j:Word w))
    (en : ∀v j,m (ends.base+(v.val*L+j.val))=(number (old v j):Word w))
    (sorted : ∀v j,m (neighbors.base+(v.val*D+j.val))=(number (next v j):Word w)) :
    DescentOrdinaryCompactPeer.Mounted (Q:=Q) (layout base N H L Q ranks ends neighbors) (shapes base H L Q 0) pitch
      (rack N pitch) old next m := by
  have equal (n : ℕ) (lt : n<count N H L Q) :
      m (base+n)=after base N H L Q D pitch m (base+n) :=
    (words ⟨n,lt⟩).trans (DescentStaticWordColumn.read _ _ _ _ lt).symm
  have shape (q : DescentOrdinaryCompactPeer.Key H L Q) (i : Fin 5) :
      m (place base H L Q i.val+(DescentOrdinaryCompactPeer.index H L Q q).val)=(field N D pitch q i:Word w) := by
    let ix:=DescentOrdinaryCompactPeer.index H L Q q
    have lt : i.val*rows+ix.val<count N H L Q := by
      have a := Nat.mul_le_mul_right rows i.isLt
      rw [Nat.succ_mul] at a
      have b:=ix.isLt
      unfold count
      omega
    have same:=equal _ lt
    simpa only [place,Nat.add_assoc,ix] using same.trans (by simpa only [place,Nat.add_assoc,ix] using query_read base N D pitch m q i)
  refine ⟨fun q=>shape q 0,?_,fun q=>shape q 2,fun q=>shape q 3,fun q=>shape q 4,?_,rk,en,sorted⟩
  · intro q v hr
    have loc : v.val=q.1.val/pitch := by
      unfold rack at hr
      split at hr
      · cases hr
        rfl
      · contradiction
    simpa [layout, shapes, field, loc] using shape q 1
  · intro v
    have lt : 5*rows+v.val<count N H L Q := Nat.add_lt_add_left v.isLt _
    have same:=equal _ lt
    change m (place base H L Q 5 + v.val) = _
    simpa only [place,Nat.add_assoc] using same.trans (by simpa only [place,Nat.add_assoc] using scale_read (H:=H) (L:=L) (Q:=Q) base D pitch m v)

theorem execute (ranks ends neighbors : Bank) (base out pitch : ℕ) (m : Memory w) (old : Fin N→Fin L→Option (Fin N))
    (next : Fin H→Fin D→Option (Fin H)) (ok : DescentOrdinaryCompactPeer.Room (layout base N H L Q ranks ends neighbors) (shapes base H L Q 0) N H L Q D pitch w out)
    (space : base+count N H L Q≤out)
    (pr : ranks.base+N*L≤base) (pe : ends.base+N*L≤base) (pn : neighbors.base+H*D≤base)
    (rk : ∀v j,m (ranks.base+(v.val*L+j.val))=(rank old v j:Word w))
    (en : ∀v j,m (ends.base+(v.val*L+j.val))=(number (old v j):Word w))
    (sorted : ∀v j,m (neighbors.base+(v.val*D+j.val))=(number (next v j):Word w)) :
    let op:=expr (layout base N H L Q ranks ends neighbors) (shapes base H L Q 0) N L D;let first:=after base N H L Q D pitch m;let last:=image out rows op first
    ((program base N H L Q D pitch w).seq (scan w out rows op)).Exec m last ((4+10*count N H L Q)+(4+rows*(2*op.work+4))) ∧
      (∀q,last (out+(DescentOrdinaryCompactPeer.index H L Q q).val)=(((rack N pitch q.1).elim D (fun v=>value old next pitch v q.1 q.2.1 q.2.2):ℕ):Word w)) ∧
      ∀x,x<base ∨ out+rows≤x→last x=m x :=by
  intro op first last
  have lead : (program base N H L Q D pitch w).Exec m first (4+10*count N H L Q) := by
    intro labels regs slots machine
    exact DescentStaticWordColumn.mount base (count N H L Q) (contents N H L Q D pitch) m
      (space.trans_lt ((Nat.le_add_right out rows).trans_lt ok.last)) machine
  have issued := DescentOrdinaryCompactPeer.run (layout base N H L Q ranks ends neighbors)
    (shapes base H L Q 0) pitch out (rack N pitch) ok old next first
    (mounted ranks ends neighbors base pitch m old next pr pe pn rk en sorted)
  refine ⟨@Procedure.Exec.then w (program base N H L Q D pitch w) (scan w out rows op)
    m first last (4+10*count N H L Q) (4+rows*(2*op.work+4)) (@lead) issued.1,?_,?_⟩
  · intro q
    cases occupied : rack N pitch q.1 <;> simpa [occupied] using issued.2.1 q
  have unchanged := issued.2.2.1
  intro x h;rcases h with low|high
  · exact (unchanged x (.inl (low.trans_le ((Nat.le_add_right ..).trans space)))).trans (DescentStaticWordColumn.frame _ _ _ _ x (.inl low))
  · exact (unchanged x (.inr high)).trans (DescentStaticWordColumn.frame _ _ _ _ x (.inr (space.trans ((Nat.le_add_right ..).trans high))))

def output (base N H L Q : ℕ) :=
  base+count N H L Q+2^(Nat.clog 2 (H*(L*Q)+1))+2^(Nat.clog 2 (N+1))

theorem arranged (ranks ends neighbors : Bank) (base pitch : ℕ)
    (ranksFit : ranks.Fits w base ∧ N*L≤ranks.size)
    (endsFit : ends.Fits w base ∧ N*L≤ends.size)
    (rosterFit : neighbors.Fits w base ∧ H*D≤neighbors.size)
    (oldFit : N<2^w) (limitH : H<2^w) (limitL : L<2^w)
    (targetFit : ∀u : Fin N,∀g : Fin Q,u.val*pitch+g.val<2^w) (width : 0<w)
    (last : output base N H L Q+rows<2^w) :
    base+count N H L Q≤output base N H L Q ∧
      DescentOrdinaryCompactPeer.Room (layout base N H L Q ranks ends neighbors) (shapes base H L Q 0)
        N H L Q D pitch w (output base N H L Q) := by
  let out:=output base N H L Q
  let page := 2^(Nat.clog 2 (rows+1))
  let scale := 2^(Nat.clog 2 (N+1))
  have sep : base+count N H L Q≤out :=
    (Nat.le_add_right (base+count N H L Q) page).trans (Nat.le_add_right _ scale)
  have end_ : out<2^w := (Nat.le_add_right ..).trans_lt last
  have move (B : Bank) (h : B.Fits w base) : B.Fits w out := ⟨h.1,h.2.1,h.2.2.trans ((Nat.le_add_right ..).trans sep)⟩
  have fit (B : Bank) (ext : B.base+B.size≤out) : B.Fits w out :=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (ext.trans_lt end_),ext⟩
  have wrap (i : Fin 5) : (shapes base H L Q i.val).Fits w out ∧ rows≤(shapes base H L Q i.val).size := by
    have ibound := Nat.mul_le_mul_right rows i.isLt.le
    refine ⟨fit _ ?_,(Nat.le_succ rows).trans (Nat.le_pow_clog (b:=2) (by decide) (rows+1))⟩
    change base+i.val*rows+page≤base+(5*rows+N)+page+scale
    exact (Nat.add_le_add_right (Nat.add_le_add_left
      (ibound.trans (Nat.le_add_right (5*rows) N)) base) page).trans (Nat.le_add_right _ scale)
  refine ⟨sep,?_,⟨move _ ranksFit.1,ranksFit.2⟩,⟨move _ endsFit.1,endsFit.2⟩,⟨move _ rosterFit.1,rosterFit.2⟩,
    ⟨fit _ ?_,(Nat.le_succ N).trans (Nat.le_pow_clog (b:=2) (by decide) (N+1))⟩,oldFit,limitH,limitL,targetFit,last,width⟩
  · intro bank mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl
    exacts [wrap 0,wrap 1,wrap 2,wrap 3,wrap 4]
  · change base+5*rows+scale≤base+(5*rows+N)+page+scale
    exact Nat.add_le_add_right ((Nat.add_le_add_left
      (Nat.le_add_right (5*rows) N) base).trans (Nat.le_add_right _ page)) scale

end
end Hierarchy.DescentOrdinaryCompactPeer.ROM

end OAI
