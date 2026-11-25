import OAI.Hierarchy.DescentScalarBookReshape

namespace OAI
/-! # Transposing all operand fields into the successor's block banks

Each page consists of the same rectangle of local keys, hosts, and packed groups.
The two address columns depend on the rectangular dimensions. All pages read the
same dictionary and one scan traverses the complete output.
-/
namespace Hierarchy.DescentVectorBookReshape
open DescentSIMDLookup DescentPackedZip Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentScalarBookReshape (Seat ordinal origin low book project page_read Chart expression)
open scoped Classical Fin.CommRing
noncomputable section
variable {N H Q J r a M w : ℕ}

def sourceWords (H Q J M : ℕ) := Q*(H*chunks J M)
def rows (H Q J r M : ℕ) := r*((H*Q)*chunks J M)
def dictionaryWords (r a M : ℕ) := r*2^((a*r)*M)
def cells (N H Q J r a M : ℕ) := dictionaryWords r a M + 2*(N*rows H Q J r M)

abbrev Index (N H Q J r a M : ℕ) :=
  (Fin r × Cell ((a*r)*M)) ⊕ (Fin 2 × Fin (N*rows H Q J r M))

def seat (N H Q J r M : ℕ) : (Fin N × Seat H Q J r M) ≃ Fin (N*rows H Q J r M) :=
  ((Equiv.refl _).prodCongr (ordinal H Q J r M)).trans finProdFinEquiv

def index (N H Q J r a M : ℕ) : Index N H Q J r a M ≃ Fin (cells N H Q J r a M) :=
  (finProdFinEquiv.sumCongr finProdFinEquiv).trans finSumFinEquiv

def sourceOffset (page : Fin N) (z : Seat H Q J r M) :=
  page.val*sourceWords H Q J M + DescentScalarBookReshape.sourceOffset z

def value : Index N H Q J r a M → ℕ
  | .inl (b,x) => (DescentSIMDLookup.table (M:=M) (project (a:=a) b) x).val
  | .inr (role,j) =>
    let z := (seat N H Q J r M).symm j
    if role.val=0 then sourceOffset z.1 z.2 else z.2.1.val*2^((a*r)*M)

def words (N H Q J r a M j : ℕ) :=
  if inside : j < cells N H Q J r a M then value ((index N H Q J r a M).symm ⟨j,inside⟩) else 0

def address (base : ℕ) : Index N H Q J r a M → ℕ
  | .inl (b,x) => base+(b.val*2^((a*r)*M)+x.val)
  | .inr (role,j) => base+dictionaryWords r a M+role.val*(N*rows H Q J r M)+j.val

def mounted (base N H Q J r a M : ℕ) (m : Memory w) :=
  DescentStaticWordColumn.image base (words N H Q J r a M) m (cells N H Q J r a M)

theorem statics (base : ℕ) (m : Memory w) (j : Index N H Q J r a M) :
    mounted base N H Q J r a M m (address base j)=(value j:Word w) := by
  have addr : address base j=base+(index N H Q J r a M j).val := by
    rcases j with ⟨b,x⟩|⟨role,i⟩
    · change base+(b.val*2^((a*r)*M)+x.val)=base+(x.val+2^((a*r)*M)*b.val)
      ac_rfl
    · change base+dictionaryWords r a M+role.val*(N*rows H Q J r M)+i.val=
        base+(dictionaryWords r a M+(i.val+(N*rows H Q J r M)*role.val))
      ac_rfl
  rw [addr,mounted,DescentStaticWordColumn.read _ _ _ _ (index N H Q J r a M j).isLt]
  simp only [words,dite_eq_left (index N H Q J r a M j).isLt]
  change (value ((index N H Q J r a M).symm (index N H Q J r a M j)):Word w)=_
  rw [Equiv.symm_apply_apply]

def layout (N H Q J r a M base : ℕ) (old : Bank) : Chart :=
  let n := N*rows H Q J r M
  let bits := Nat.clog 2 (n+1)
  let begin_ := base+dictionaryWords r a M
  ⟨old,⟨base,Nat.clog 2 (dictionaryWords r a M+1)⟩,⟨begin_,bits⟩,⟨begin_+n,bits⟩⟩

def program (N H Q J r a M base out w : ℕ) (old : Bank) :=
  (DescentStaticWordColumn.program w base (words N H Q J r a M) (cells N H Q J r a M)).seq
    (scan w out (N*rows H Q J r M) (expression (layout N H Q J r a M base old)))

structure Room (N H Q J r a M w base out : ℕ) (old : Bank) : Prop where
  banks : (expression (layout N H Q J r a M base old)).Fits w out
  sourceEnd : old.base+N*sourceWords H Q J M ≤ base
  capacity : N*sourceWords H Q J M ≤ old.size
  early : base+cells N H Q J r a M ≤ out
  end_ : out+N*rows H Q J r M < 2^w

def result (N H Q J r a M base out : ℕ) (old : Bank) (m : Memory w) :=
  image out (N*rows H Q J r M) (expression (layout N H Q J r a M base old)) (mounted base N H Q J r a M m)

def sourceBase (old : Bank) (H Q J M : ℕ) (page : Fin N) := old.base+page.val*sourceWords H Q J M

def destBase (out H Q J r M : ℕ) (page : Fin N) := out+page.val*rows H Q J r M

/-- Reading a page's block at the next date uses an ordinary contiguous row bank. -/
def blockBank (out H Q J r M : ℕ) (p : Fin N) (b : Fin r) : Bank :=
  ⟨DescentScalarBookReshape.dest H Q J M (destBase out H Q J r M p) b,Nat.clog 2 ((H*Q)*chunks J M+1)⟩

theorem blockBank_capacity (out H Q J r M : ℕ) (p : Fin N) (b : Fin r) :
    (H*Q)*chunks J M ≤ (blockBank out H Q J r M p b).size :=
  (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)

def ticks (N H Q J r a M : ℕ) := (4+10*cells N H Q J r a M)+(4+N*rows H Q J r M*54)

private theorem offset_lt {c l : ℕ} (p : Fin c) {i : ℕ} (hi : i < l) : p.val*l+i < c*l :=
  (Nat.add_lt_add_left hi _).trans_le (by rw [←Nat.succ_mul]; exact Nat.mul_le_mul_right _ p.isLt)

theorem run (base out : ℕ) (old : Bank) (m : Memory w)
    (x : Fin N → Fin Q → Fin H → Fin (J*r) → Cell a) (hm : 0 < M) (hr : 0 < r)
    (fit : Room N H Q J r a M w base out old)
    (source : ∀page l (p : Row H (J*r) (M*r)),
      m (sourceBase old H Q J M page+l.val*(H*chunks J M)+(row H (J*r) (M*r) p).val)=
        ((data (x page l) p).val:Word w)) :
    let done := result N H Q J r a M base out old m
    (program N H Q J r a M base out w old).Exec m done (ticks N H Q J r a M) ∧
    (∀page b (p : Row (H*Q) J M),done (DescentScalarBookReshape.dest H Q J M
      (destBase out H Q J r M page) b+(row (H*Q) J M p).val)=((data (book (x page) b) p).val:Word w)) ∧
    ∀u,u < base ∨ out+N*rows H Q J r M ≤ u → done u=m u := by
  intro done
  let C := layout N H Q J r a M base old
  let mid := mounted base N H Q J r a M m
  let n := N*rows H Q J r M
  have ds : C.dictionary.Fits w out := fit.banks.1
  have off : C.offset.Fits w out := fit.banks.2.1.1
  have rd : C.srcRow.Fits w out := fit.banks.2.2.2.1
  have orig : old.Fits w out := fit.banks.2.2.1
  have rowCap : n ≤ C.offset.size := (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have dictCap : dictionaryWords r a M ≤ C.dictionary.size := (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have before (u : ℕ) (earlier : u < base) : mid u=m u := DescentStaticWordColumn.frame _ _ _ _ _ (.inl earlier)
  have head : (DescentStaticWordColumn.program w base (words N H Q J r a M) (cells N H Q J r a M)).Exec m mid (4+10*cells N H Q J r a M) := DescentStaticWordColumn.mount base (cells N H Q J r a M) (words N H Q J r a M) m
    (fit.early.trans_lt ((Nat.le_add_right ..).trans_lt fit.end_))
  have ran : (scan w out n (expression C)).Exec mid done (4+n*54) := scan_exec out n (expression C) mid fit.banks fit.end_
  refine ⟨(by intro P R K machine;exact Procedure.Exec.then head ran machine),?_,?_⟩
  · intro page b p
    let z : Seat H Q J r M := (b,p)
    let j := seat N H Q J r M (page,z)
    let t := data (groupedRows (x page (low z))) (origin z)
    have dest_ : DescentScalarBookReshape.dest H Q J M (destBase out H Q J r M page) b+
        (row (H*Q) J M p).val=out+j.val := by
      change out+page.val*rows H Q J r M+b.val*((H*Q)*chunks J M)+(row (H*Q) J M p).val=
        out+((row (H*Q) J M p).val+((H*Q)*chunks J M)*b.val+rows H Q J r M*page.val)
      ac_rfl
    have inner : DescentScalarBookReshape.sourceOffset z < sourceWords H Q J M :=
      offset_lt (low z) (row H J M (origin z)).isLt
    have oldSmall : sourceOffset page z < N*sourceWords H Q J M := offset_lt page inner
    have key : b.val*2^((a*r)*M)+t.val < C.dictionary.size := (offset_lt b t.isLt).trans_le dictCap
    have atOld : m (old.base+sourceOffset page z)=(t.val:Word w) := by
      simpa only [sourceBase,sourceOffset,DescentScalarBookReshape.sourceOffset,Nat.add_assoc,t] using
        regroup_read hm hr (sourceBase old H Q J M page+(low z).val*(H*chunks J M)) m
          (x page (low z)) (source page (low z)) (origin z)
    have get : C.srcRow.read mid (j.val:Word w)=(sourceOffset page z:Word w) := by
      rw [bank_read C.srcRow mid (show j.val<C.srcRow.size from j.isLt.trans_le rowCap) rd]
      simpa [C,layout,address,value,j,z] using statics base m (.inr ((0:Fin 2),j) : Index N H Q J r a M)
    have bias : C.offset.read mid (j.val:Word w)=((b.val*2^((a*r)*M):ℕ):Word w) := by
      rw [bank_read C.offset mid (j.isLt.trans_le rowCap) off]
      simpa [C,layout,address,value,j,z] using statics base m (.inr ((1:Fin 2),j) : Index N H Q J r a M)
    rw [dest_]
    apply (ProtocolRAMGeneratedWrite.read_image out n (expression C) mid j).trans
    change C.dictionary.read mid (C.offset.read mid (j.val:Word w)+old.read mid (C.srcRow.read mid (j.val:Word w)))=_
    rw [get,bias,bank_read _ _ (oldSmall.trans_le fit.capacity) orig,
      before _ ((Nat.add_lt_add_left oldSmall _).trans_le fit.sourceEnd),atOld,←Nat.cast_add,bank_read _ _ key ds]
    exact (statics base m (.inl (b,t) : Index N H Q J r a M)).trans
      (congrArg (fun q : Cell (a*M)=>(q.val:Word w)) (page_read (x page) z))
  · intro u safe
    rcases safe with low|high
    · exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ u
        (.inl (low.trans_le ((Nat.le_add_right ..).trans fit.early)))).trans (before _ low)
    · exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ u (.inr high)).trans
        (DescentStaticWordColumn.frame _ _ _ _ _ (.inr (fit.early.trans ((Nat.le_add_right ..).trans high))))

/-- A concrete aligned destination beyond both rounded lookup banks. -/
def output (base N H Q J r a M : ℕ) :=
  base+cells N H Q J r a M+2^Nat.clog 2 (dictionaryWords r a M+1)+2^Nat.clog 2 (N*rows H Q J r M+1)

theorem arranged (base : ℕ) (old : Bank) (early : old.Fits w base)
    (area : N*sourceWords H Q J M ≤ old.size)
    (space : output base N H Q J r a M+N*rows H Q J r M < 2^w) :
    Room N H Q J r a M w base (output base N H Q J r a M) old := by
  let n:=N*rows H Q J r M
  let d:=dictionaryWords r a M
  let first:=(2:ℕ)^Nat.clog 2 (d+1)
  let second:=(2:ℕ)^Nat.clog 2 (n+1)
  let out:=output base N H Q J r a M
  have length_ : out=base+d+2*n+first+second := by dsimp [out,output,cells,d,n,first,second]; omega
  obtain ⟨baseOut,dictEnd,srcEnd,offEnd,cellsEnd⟩ := DescentScalarBookReshape.allocation_bounds base d n first second
  rw [← length_] at baseOut dictEnd srcEnd offEnd cellsEnd
  have inside : out < 2^w := (Nat.le_add_right ..).trans_lt space
  have earlier : old.Fits w out := ⟨early.1,early.2.1,early.2.2.trans baseOut⟩
  have bank (B : Bank) (valid : B.base+B.size ≤ out) : B.Fits w out :=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (valid.trans_lt inside),valid⟩
  let C:=layout N H Q J r a M base old
  have dictionary : C.dictionary.Fits w out := bank _ dictEnd
  have ix : C.srcRow.Fits w out := bank _ srcEnd
  have bias : C.offset.Fits w out := bank _ offEnd
  refine ⟨?_,(Nat.add_le_add_left area _).trans early.2.2,area,?_,space⟩
  · exact ⟨dictionary,⟨bias,trivial⟩,earlier,ix,trivial⟩
  · exact cellsEnd

theorem exec (base out : ℕ) (old : Bank) (m : Memory w) (room : Room N H Q J r a M w base out old) :
    (program N H Q J r a M base out w old).Exec m (result N H Q J r a M base out old m) (ticks N H Q J r a M) := by
  have first : (DescentStaticWordColumn.program w base (words N H Q J r a M) (cells N H Q J r a M)).Exec m (mounted base N H Q J r a M m) (4+10*cells N H Q J r a M) := DescentStaticWordColumn.mount base (cells N H Q J r a M) (words N H Q J r a M) m
    (room.early.trans_lt ((Nat.le_add_right ..).trans_lt room.end_))
  intro P R K machine
  exact Procedure.Exec.then first (scan_exec out _ (expression (layout N H Q J r a M base old)) _ room.banks room.end_) machine

theorem ticks_eq (N H Q J r a M : ℕ) : ticks N H Q J r a M =
    8+10*dictionaryWords r a M+74*(N*rows H Q J r M) := by
  unfold ticks cells
  ring

theorem names (base out : ℕ) (old : Bank) :
    DescentStaticWordColumn.names (program N H Q J r a M base out w old)=15*(cells N H Q J r a M+1)+111 := by
  unfold program
  rw [DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_mount,DescentStaticWordColumn.names_scan]
  rfl

/-- The scratch columns and rectangle are the only two modified intervals. -/
theorem frame {base out : ℕ} {old : Bank} (m : Memory w) (u : ℕ)
    (static : u < base ∨ base+cells N H Q J r a M ≤ u)
    (output : u < out ∨ out+N*rows H Q J r M ≤ u) :
    result N H Q J r a M base out old m u = m u :=
  (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ u output).trans
    (DescentStaticWordColumn.frame _ _ _ _ _ static)

end
end Hierarchy.DescentVectorBookReshape

end OAI
