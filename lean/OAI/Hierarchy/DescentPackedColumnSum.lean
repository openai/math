import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.DescentStaticWordColumn
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # Native sums of fixed bit fields from heterogeneous packed input columns -/
namespace Hierarchy.DescentPackedColumnSum
open DescentSIMDLookup DescentPackedZip DescentPackedColony ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {n H G M w out : ℕ}

def piece (width : ℕ) {b M : ℕ} (value : Cell b→ℕ) (key : Cell (b*M)) : ℕ :=
  ∑j : Fin M,value ((encode b M).symm key j)*(2^width)^j.val

def packed (width : ℕ) (x : Fin H→Fin G→ℕ) (p : Row H G M) : ℕ :=
  ∑j : Fin M,(if live : p.2.val*M+j.val<G then x p.1 ⟨_,live⟩ else 0)*(2^width)^j.val

theorem piece_data {b width : ℕ} (f : Cell b→ℕ) (zero : f 0=0) (x : Fin H→Fin G→Cell b) (p : Row H G M) :
    piece width f (data x p)=packed width (fun h g=>f (x h g)) p := by
  unfold piece packed
  apply Finset.sum_congr rfl
  intro j _
  simp only [data,Equiv.symm_apply_apply]
  split <;> simp_all

theorem packed_sum (width : ℕ) (f : Fin n→Fin H→Fin G→ℕ) (p : Row H G M) :
    (∑i,packed width (f i) p)=packed width (fun h g=>∑i,f i h g) p := by
  unfold packed
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases live : p.2.val*M+j.val<G
  · simp only [dite_eq_left live,Finset.sum_mul]
  · simp [live]

theorem packed_data (width : ℕ) (x : Fin H→Fin G→Cell width) (p : Row H G M) :
    packed width (fun h g=>(x h g).val) p=(data x p).val := by
  change _=(finFunctionFinEquiv (fun i : Fin M=>if live : p.2.val*M+i.val<G then x p.1 ⟨_,live⟩ else 0)).val
  rw [finFunctionFinEquiv_apply]
  apply Finset.sum_congr rfl
  intro i _
  split <;> rfl

def expr (field : Fin n→Expr) : List (Fin n)→Expr
  | []=>.lit 0
  | i::is=>.op .add (field i) (expr field is)

private theorem expr_fits (field : Fin n→Expr) (old : ∀i,(field i).Fits w out) (list : List (Fin n)) :
    (expr field list).Fits w out := by
  induction list with
  | nil=>trivial
  | cons i is ih=>exact ⟨old i,ih⟩

private theorem expr_eval (field : Fin n→Expr) (m : Memory w) (input : Word w) (list : List (Fin n)) :
    (expr field list).eval m input=(list.map (fun i=>(field i).eval m input)).sum := by
  induction list with
  | nil=>rfl
  | cons i is ih=>simp [expr,Expr.eval,RowOp.opcode,Computability.VPVNP.BurstRAM.PrivateRAM.BinaryOp.eval,ih]

def bank (base u M : ℕ) (b : Fin n→ℕ) (i : Fin n) : Bank :=
  ⟨base+i.val*2^(u*M),b i*M⟩

private def entry (M width : ℕ) (b : Fin n→ℕ) (f : ∀i,Cell (b i)→ℕ) (i : Fin n) (v : ℕ) :=
  if k : v<2^(b i*M) then piece width (f i) ⟨v,k⟩ else 0

def literals (u M width : ℕ) (b : Fin n→ℕ) (f : ∀i,Cell (b i)→ℕ) (j : ℕ) :=
  if a : j/2^(u*M)<n then entry M width b f ⟨_,a⟩ (j%2^(u*M)) else 0

def finish (base n u M : ℕ) := base+n*2^(u*M)

def reads (base u M : ℕ) (b : Fin n→ℕ) (src : Fin n→Expr) :=
  expr (fun i=>.lookup (bank base u M b i) (src i)) (List.finRange n)

theorem lit_read (base u M width : ℕ) (b : Fin n→ℕ) (f : ∀i,Cell (b i)→ℕ) (m : Memory w)
    (small : ∀i,b i≤u) (i : Fin n) (key : Cell (b i*M)) :
    DescentStaticWordColumn.image base (literals u M width b f) m (n*2^(u*M)) ((bank base u M b i).base+key.val)=
      (piece width (f i) key : Word w) := by
  let pitch:=(2:ℕ)^(u*M)
  have pos : 0<pitch:=Nat.two_pow_pos _
  have keyFit : key.val<pitch:=key.isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right M (small i)))
  have page : i.val*pitch+key.val<n*pitch:=calc
    _ < i.val*pitch+pitch:=Nat.add_lt_add_left keyFit _
    _ = (i.val+1)*pitch:=(Nat.succ_mul ..).symm
    _ ≤ _:=Nat.mul_le_mul_right pitch i.isLt
  change DescentStaticWordColumn.image base _ m _ ((base+i.val*pitch)+key.val)=_
  rw [Nat.add_assoc,DescentStaticWordColumn.read base _ _ m page]
  have quotient : (i.val*pitch+key.val)/pitch=i.val := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ pos,Nat.div_eq_of_lt keyFit,Nat.zero_add]
  have offset : (i.val*pitch+key.val)%pitch=key.val := by simp [Nat.add_mod,Nat.mod_eq_of_lt keyFit]
  have exactValue : literals u M width b f (i.val*pitch+key.val)=piece width (f i) key := by
    have inRange : (i.val*pitch+key.val)/pitch<n:=quotient.trans_lt i.isLt
    have slot : (⟨(i.val*pitch+key.val)/pitch,inRange⟩ : Fin n)=i:=Fin.ext quotient
    change (if h : (i.val*pitch+key.val)/pitch<n then
      entry M width b f ⟨_,h⟩ ((i.val*pitch+key.val)%pitch) else 0)=_
    rw [dite_eq_left inRange,slot,offset]
    simp only [entry,dite_eq_left key.isLt]
  exact congrArg (fun x : ℕ=>(x:Word w)) exactValue

def program (w base out u M width H G : ℕ) (b : Fin n→ℕ) (f : ∀i,Cell (b i)→ℕ) (src : Fin n→Expr) :=
  (DescentStaticWordColumn.program w base (literals u M width b f) (n*2^(u*M))).seq
    (scan w out (H*chunks G M) (reads base u M b src))

def after (base out u M width H G : ℕ) (b : Fin n→ℕ) (f : ∀i,Cell (b i)→ℕ) (src : Fin n→Expr) (m : Memory w) :=
  ProtocolRAM.image out (H*chunks G M) (reads base u M b src)
    (DescentStaticWordColumn.image base (literals u M width b f) m (n*2^(u*M)))

def ticks (base u M H G : ℕ) (b : Fin n→ℕ) (src : Fin n→Expr) :=
  (4+10*(n*2^(u*M)))+(4+(H*chunks G M)*(2*(reads base u M b src).work+4))

theorem mount_cheap (w base : ℕ) (values : ℕ→ℕ) (count : ℕ) :
    CheapCode (DescentStaticWordColumn.program w base values count) := by
  induction count with
  | zero=>exact scan_cheap w base 0 (.lit 0)
  | succ count ih=>exact cheap_seq ih (scan_cheap w (base+count) 1 (.lit (values count)))

theorem program_cheap (w base out u M width H G : ℕ) (b : Fin n→ℕ) (f : ∀i,Cell (b i)→ℕ) (src : Fin n→Expr) :
    CheapCode (program w base out u M width H G b f src) :=
  cheap_seq (mount_cheap w base (literals u M width b f) (n*2^(u*M)))
    (scan_cheap w out (H*chunks G M) (reads base u M b src))

private theorem bank_fits (base out u M H G : ℕ) (b : Fin n→ℕ) (small : ∀i,b i≤u)
    (sep : finish base n u M≤out) (room : out+H*chunks G M<2^w) (i : Fin n) :
    (bank base u M b i).Fits w out := by
  let pitch:=(2:ℕ)^(u*M)
  have within : 2^(b i*M)≤pitch:=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right M (small i))
  have top : i.val*pitch+2^(b i*M)≤n*pitch:=calc
    _ ≤ i.val*pitch+pitch:=Nat.add_le_add_left within _
    _ = (i.val+1)*pitch:=(Nat.succ_mul ..).symm
    _ ≤ _:=Nat.mul_le_mul_right pitch i.isLt
  have last : base+i.val*pitch+2^(b i*M)≤out:=(Nat.add_assoc ..).le.trans ((Nat.add_le_add_left top base).trans sep)
  exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (last.trans_lt ((Nat.le_add_right ..).trans_lt room)),last⟩

/-- The order of all writes is fixed, including when a source chip holds
arbitrary data or a malformed selector indexes an unused table entry. -/
theorem any (base out u M width H G : ℕ) (b : Fin n→ℕ) (f : ∀i,Cell (b i)→ℕ) (src : Fin n→Expr)
    (m : Memory w) (small : ∀i,b i≤u) (bounds : ∀i,(src i).Fits w base)
    (sep : finish base n u M≤out) (room : out+H*chunks G M<2^w) :
    (program w base out u M width H G b f src).Exec m (after base out u M width H G b f src m) (ticks base u M H G b src) := by
  let mid:=DescentStaticWordColumn.image base (literals u M width b f) m (n*2^(u*M))
  have start : base≤out:=(Nat.le_add_right ..).trans sep
  have end_ : base+n*2^(u*M)<2^w := sep.trans_lt ((Nat.le_add_right ..).trans_lt room)
  have safe : (reads base u M b src).Fits w out :=
    expr_fits (fun i=>.lookup (bank base u M b i) (src i)) (fun i=>⟨bank_fits base out u M H G b small sep room i,
      ProtocolRAMGeneratedWrite.fits_mono _ start (bounds i)⟩) _
  intro P R K machine
  exact Procedure.Exec.then (DescentStaticWordColumn.mount base (n*2^(u*M)) (literals u M width b f) m end_)
    (scan_exec out (H*chunks G M) (reads base u M b src) mid safe room) machine

theorem run (base out u M width H G : ℕ) (b : Fin n→ℕ) (f : ∀i,Cell (b i)→ℕ) (src : Fin n→Expr)
    (x : ∀i,Fin H→Fin G→Cell (b i)) (y : Fin H→Fin G→Cell width) (m : Memory w)
    (zero : ∀i,f i 0=0) (value : ∀h g,∑i,f i (x i h g)=(y h g).val)
    (small : ∀i,b i≤u) (bounds : ∀i,(src i).Fits w base)
    (old : ∀i,Source (src i) (x i) M m) (sep : finish base n u M≤out) (room : out+H*chunks G M<2^w) :
    let cpu:=program w base out u M width H G b f src
    let o:=after base out u M width H G b f src m
    cpu.Exec m o (ticks base u M H G b src) ∧ (∀p : Row H G M,o (out+(row H G M p).val)=((data y p).val:Word w)) ∧
      (∀a,a<base ∨ out+H*chunks G M≤a → o a=m a) ∧ CheapCode cpu := by
  let len:=n*2^(u*M)
  let e:=reads base u M b src
  let mid:=DescentStaticWordColumn.image base (literals u M width b f) m len
  have fits:=bank_fits base out u M H G b small sep room
  have lookup (p : Row H G M) (i : Fin n) :
      (Expr.lookup (bank base u M b i) (src i)).eval mid ((row H G M p).val:Word w)=
      (packed width (fun h g=>f i (x i h g)) p:Word w) := by
    have frame (a : ℕ) (ha : a<base) : mid a=m a:=DescentStaticWordColumn.frame base len _ m a (.inl ha)
    simp only [Expr.eval,eval_below (src i) _ m mid (bounds i) frame,old i p]
    rw [bank_read _ _ (data (x i) p).isLt (fits i)]
    dsimp only [mid,len]
    rw [lit_read base u M width b f m small i (data (x i) p),
      piece_data (f i) (zero i) (x i) p]
  have output (p : Row H G M) : e.eval mid ((row H G M p).val:Word w)=((data y p).val:Word w) := by
    dsimp only [e,reads]
    rw [expr_eval,← List.ofFn_eq_map,List.sum_ofFn]
    simp only [lookup p,← Nat.cast_sum,packed_sum,value,packed_data]
  refine ⟨?_,fun p=>(ProtocolRAMGeneratedWrite.read_image out _ e mid (row H G M p)).trans (output p),?_,
    program_cheap w base out u M width H G b f src⟩
  · exact any base out u M width H G b f src m small bounds sep room
  · intro a h
    have start : base≤out := (Nat.le_add_right base (n*2^(u*M))).trans sep
    exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ a (by rcases h with h|h <;> omega)).trans
      (DescentStaticWordColumn.frame _ _ _ _ a (by rcases h with h|h <;> dsimp [finish] at sep <;> omega))

theorem work_le (base u M : ℕ) (b : Fin n→ℕ) (src : Fin n→Expr) (price : ℕ) (cost : ∀i,(src i).work≤price) :
    (reads base u M b src).work≤1+n*(price+6) := by
  have bound (is : List (Fin n)) :
      (expr (fun i=>.lookup (bank base u M b i) (src i)) is).work≤1+is.length*(price+6) := by
    induction is with
    | nil=>simp [expr,Expr.work]
    | cons i is ih=>
      simp only [expr,Expr.work,List.length_cons,Nat.succ_mul]
      have small:=cost i
      omega
  simpa only [reads,List.length_finRange] using bound (List.finRange n)

end
end Hierarchy.DescentPackedColumnSum

end OAI
