import OAI.Hierarchy.DescentSignedTableDimensions
import OAI.Hierarchy.DescentPackedHostLookup
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Shared integer ROM and issued header for a packed successor-neighbor pass -/
namespace Hierarchy.DescentPackedChildNeighbor.SIMD.ROM
open DescentSIMDLookup DescentPackedZip Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H G T a b M w : ℕ}

abbrev Index (T a b M H G : ℕ) := Cell (a*M) ⊕ ((Fin T×Cell (a*M+b)) ⊕ (Cell (b*M) ⊕ (Cell ((b+b)*M) ⊕ Fin (H*chunks G M))))

def index (T a b M H G : ℕ) : Index T a b M H G ≃ Fin (cells T a b M H G) :=
  let suffix:=finSumFinEquiv (m:=2^((b+b)*M)) (n:=H*chunks G M)
  let joins:=((Equiv.refl (Cell (b*M))).sumCongr suffix).trans finSumFinEquiv
  let picks:=((finProdFinEquiv (m:=T) (n:=2^(a*M+b))).sumCongr joins).trans finSumFinEquiv
  ((Equiv.refl (Cell (a*M))).sumCongr picks).trans finSumFinEquiv

def word : Index T a b M H G→ℕ
  | .inl n=>2^b*n.val
  | .inr (.inl (j,n))=>(page (M:=M) (b:=b) (a:=a) j n).val
  | .inr (.inr (.inl n))=>2^(b*M)*n.val
  | .inr (.inr (.inr (.inl n)))=>(DescentPackedZip.table (M:=M) (merge (b:=b)) n).val
  | .inr (.inr (.inr (.inr n)))=>((row H G M).symm n).1.val*T

def numbers (T a b M H G i : ℕ) :=if yes:i<cells T a b M H G then word ((index T a b M H G).symm ⟨i,yes⟩) else 0

def pageBase (base a M : ℕ) :=base+2^(a*M)
def joinBase (base T a b M : ℕ) :=pageBase base a M+T*2^(a*M+b)
def applyBase (base T a b M : ℕ) :=joinBase base T a b M+2^(b*M)
def offsetBase (base T a b M : ℕ) :=applyBase base T a b M+2^((b+b)*M)

def layout (base T a b M rowBits : ℕ) (dir : Bank) : Chart T where
  header:=dir
  shift:=⟨base,a*M⟩
  pages j:=⟨pageBase base a M+j.val*2^(a*M+b),a*M+b⟩
  join:=⟨⟨joinBase base T a b M,b*M⟩,⟨applyBase base T a b M,(b+b)*M⟩⟩
  offset:=⟨offsetBase base T a b M,rowBits⟩

def address (base : ℕ) : Index T a b M H G→ℕ
  | .inl n=>base+n.val
  | .inr (.inl (j,n))=>pageBase base a M+j.val*2^(a*M+b)+n.val
  | .inr (.inr (.inl n))=>joinBase base T a b M+n.val
  | .inr (.inr (.inr (.inl n)))=>applyBase base T a b M+n.val
  | .inr (.inr (.inr (.inr n)))=>offsetBase base T a b M+n.val

theorem address_eq (base : ℕ) (i : Index T a b M H G) : address base i=base+(index T a b M H G i).val :=by
  let sh := 2^(a*M)
  let tab := 2^(a*M+b)
  let left := 2^(b*M)
  let join := 2^((b+b)*M)
  rcases i with n|⟨j,n⟩|n|n|n
  · rfl
  · change base+sh+j.val*tab+n.val=base+(sh+(n.val+tab*j.val))
    ac_rfl
  · change base+sh+T*tab+n.val=base+(sh+(T*tab+n.val))
    ac_rfl
  · change base+sh+T*tab+left+n.val=base+(sh+(T*tab+(left+n.val)))
    ac_rfl
  · change base+sh+T*tab+left+join+n.val=base+(sh+(T*tab+(left+(join+n.val))))
    ac_rfl

def program (base T a b M H G w : ℕ) :=DescentStaticWordColumn.program w base (numbers T a b M H G) (cells T a b M H G)
def after (base T a b M H G : ℕ) (m : Memory w) :=DescentStaticWordColumn.image base (numbers T a b M H G) m (cells T a b M H G)

theorem read (base : ℕ) (m : Memory w) (i : Index T a b M H G) : after base T a b M H G m (address base i)=(word i:Word w) :=by
  rw [address_eq,after,DescentStaticWordColumn.read _ _ _ _ (index T a b M H G i).isLt]
  simp only [numbers,dite_eq_left (index T a b M H G i).isLt]
  change (word ((index T a b M H G).symm (index T a b M H G i)):Word w)=(word i:Word w)
  rw [Equiv.symm_apply_apply]

theorem hardware (base T a b M H G w : ℕ) : DescentStaticWordColumn.names (program base T a b M H G w)=15*(cells T a b M H G+1) :=DescentStaticWordColumn.names_mount ..

/-- Every header in a family uses the same prepared shift, mask, join,
and offset words. The typed header itself can be a distinct older bank. -/
theorem stored (dir : Bank) (base rowBits : ℕ) (v : Fin H→Fin T→Cell b) (m : Memory w)
    (hDir : dir.base+H*T≤base) (header : ∀h j,m (dir.base+(h.val*T+j.val))=((v h j).val:Word w)) :
    Stored (layout base T a b M rowBits dir) H G a b M v (after base T a b M H G m):=by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro h j
    have span:h.val*T+j.val<H*T:=(Nat.add_lt_add_left j.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ h.isLt)
    exact (DescentStaticWordColumn.frame _ _ _ _ _ (.inl ((Nat.add_lt_add_left span _).trans_le hDir))).trans (header h j)
  · intro p;exact (read base m (.inr (.inr (.inr (.inr (row H G M p)))) : Index T a b M H G)).trans (by simp [word])
  · intro i;exact read base m (.inl i : Index T a b M H G)
  · intro j i;exact read base m (.inr (.inl (j,i)) : Index T a b M H G)
  · intro i;exact read base m (.inr (.inr (.inl i)) : Index T a b M H G)
  · intro i;exact read base m (.inr (.inr (.inr (.inl i))) : Index T a b M H G)

/-- Start from actual header and packed query banks, with every finite lookup
and row offset physically installed by this phase. -/
theorem execute (dir query : Bank) (base out rowBits : ℕ) (v : Fin H→Fin T→Cell b) (x : Fin H→Fin G→Cell a) (m : Memory w)
    (fit : Room (layout base T a b M rowBits dir) (.lookup query .row) H G a b M w out)
    (fits : base+cells T a b M H G≤out) (hDir : dir.base+H*T≤base) (hQuery : query.base+H*chunks G M≤base) (capacity : H*chunks G M≤query.size)
    (header : ∀h j,m (dir.base+(h.val*T+j.val))=((v h j).val:Word w))
    (queries : ∀p : Row H G M,m (query.base+(row H G M p).val)=((data x p).val:Word w)) :
    let C:=layout base T a b M rowBits dir;let q:=Expr.lookup query .row;let n:=H*chunks G M;let e:=body C q (List.finRange T)
    let mid:=after base T a b M H G m;let done:=image out n e mid
    ((program base T a b M H G w).seq (code C q out H G M w)).Exec m done ((4+10*cells T a b M H G)+(4+n*(2*e.work+4))) ∧
      (∀p : Row H G M,done (out+(row H G M p).val)=((data (fun h g=>lookup (v h) (x h g) (List.finRange T)) p).val:Word w)) ∧
      (∀u,u<base ∨ out+n≤u→done u=m u) :=by
  intro C q n e mid done
  have below (u : ℕ) (early:u<base):mid u=m u:=DescentStaticWordColumn.frame _ _ _ _ _ (.inl early)
  have data_ : Stored C H G a b M v mid :=stored dir base rowBits v m hDir header
  have seen : Source q x M mid :=source_column query out fit.qFits.1 mid x capacity (fun p=>(below _ ((Nat.add_lt_add_left (row H G M p).isLt _).trans_le hQuery)).trans (queries p))
  obtain ⟨ran,final,frame,_⟩:=run C q out fit v mid data_ x seen
  refine ⟨Procedure.Exec.then (DescentStaticWordColumn.mount base (cells T a b M H G)
    (numbers T a b M H G) m (fits.trans_lt ((Nat.le_add_right ..).trans_lt fit.endFits))) ran,final,?_⟩
  intro u safe;rcases safe with low|high
  · exact (frame _ (.inl (low.trans_le ((Nat.le_add_right ..).trans fits)))).trans (below _ low)
  · exact (frame _ (.inr high)).trans (DescentStaticWordColumn.frame _ _ _ _ _ (.inr (fits.trans ((Nat.le_add_right ..).trans high))))

def rowBits (H G M : ℕ) :=Nat.clog 2 (H*chunks G M+1)
def output (base T a b M H G : ℕ) :=base+cells T a b M H G+2^(rowBits H G M)

theorem arranged_expr (dir : Bank) (q : Expr) (base : ℕ)
    (header : dir.Fits w base ∧ H*T≤dir.size) (query : q.Fits w (output base T a b M H G))
    (last : output base T a b M H G+H*chunks G M<2^w) :
    base+cells T a b M H G≤output base T a b M H G ∧ Room (layout base T a b M (rowBits H G M) dir)
      q H G a b M w (output base T a b M H G) :=by
  let out:=output base T a b M H G;let rowWidth:=rowBits H G M
  let sh:=2^(a*M);let tab:=2^(a*M+b);let left:=2^(b*M);let join:=2^((b+b)*M);let n:=H*chunks G M
  have extent:out=base+sh+T*tab+left+join+n+2^rowWidth:=by dsimp [out,output,cells,sh,tab,left,join,rowWidth,n];omega
  have space:base+cells T a b M H G≤out:=Nat.le_add_right ..
  have end_:out<2^w:=(Nat.le_add_right ..).trans_lt last
  have sep:base≤out:=(Nat.le_add_right ..).trans space
  have move (B:Bank) (old:B.Fits w base):B.Fits w out:=⟨old.1,old.2.1,old.2.2.trans sep⟩
  have fits (B:Bank) (top:B.base+B.size≤out):B.Fits w out:=⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (top.trans_lt end_),top⟩
  have joinEnd : base+sh+T*tab+left+join≤out := by
    rw [extent]
    exact (Nat.le_add_right _ n).trans (Nat.le_add_right _ _)
  have leftEnd : base+sh+T*tab+left≤out := (Nat.le_add_right _ join).trans joinEnd
  have pageEnd : base+sh+T*tab≤out := (Nat.le_add_right _ left).trans leftEnd
  refine ⟨space,⟨query,move dir header.1,fits _ ?_,fits _ ?_,?_,fits _ ?_,fits _ ?_,header.2,
      (Nat.le_succ n).trans (Nat.le_pow_clog (by decide) _),rfl,fun _=>rfl,rfl,rfl,last⟩⟩
  · change base+sh+T*tab+left+join+2^rowWidth≤out
    rw [extent]
    exact Nat.add_le_add_right (Nat.le_add_right _ n) _
  · exact (Nat.le_add_right (base+sh) (T*tab)).trans pageEnd
  · intro j;apply fits
    have span:=Nat.mul_le_mul_right tab j.isLt;rw [Nat.succ_mul] at span
    change base+sh+j.val*tab+tab≤out
    rw [Nat.add_assoc (base+sh)]
    exact (Nat.add_le_add_left span _).trans pageEnd
  · exact leftEnd
  · exact joinEnd

theorem arranged (dir query : Bank) (base : ℕ)
    (header : dir.Fits w base ∧ H*T≤dir.size) (queries : query.Fits w base ∧ H*chunks G M≤query.size)
    (last : output base T a b M H G+H*chunks G M<2^w) :
    base+cells T a b M H G≤output base T a b M H G ∧ Room (layout base T a b M (rowBits H G M) dir)
      (.lookup query .row) H G a b M w (output base T a b M H G) :=by
  have before:base≤output base T a b M H G:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  exact arranged_expr dir (.lookup query .row) base header ⟨⟨queries.1.1,queries.1.2.1,queries.1.2.2.trans before⟩,trivial⟩ last

end
end Hierarchy.DescentPackedChildNeighbor.SIMD.ROM

end OAI
