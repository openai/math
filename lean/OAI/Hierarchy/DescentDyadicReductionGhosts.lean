import OAI.Hierarchy.DescentDyadicReductionTotal
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Zero-initialize the missing host rows before the complete binary reduction -/
namespace Hierarchy.DescentPackedWalshReduction.Plan
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable (P : Plan)

def ghostRows := (P.hosts 0-P.sites)*P.chunks 0
def ghostBase (first : ℕ) := first+P.sites*P.chunks 0
def pad {w : ℕ} (first : ℕ) (m : Memory w) := image (P.ghostBase first) P.ghostRows (.lit 0) m
def padProgram (w first : ℕ) := scan w (P.ghostBase first) P.ghostRows (.lit 0)
def padTicks := 4+6*P.ghostRows

theorem real_le : P.sites≤P.hosts 0 := by simpa only [hosts,depth,Nat.sub_zero] using Nat.le_pow_clog (by decide : 1<2) P.sites
theorem pad_end (first : ℕ) : P.ghostBase first+P.ghostRows=P.dataAt first 1 := by
  have all : P.sites+(P.hosts 0-P.sites)=P.hosts 0:=Nat.add_sub_of_le P.real_le
  change first+P.sites*P.chunks 0+(P.hosts 0-P.sites)*P.chunks 0=first+P.hosts 0*P.chunks 0
  rw [Nat.add_assoc,←Nat.add_mul,all]

private theorem zero_pack (s L : ℕ) : packNat s L (fun _=>0)=0 := by
  simp [packNat,encode]

def Seed (x : Fin P.sites→Fin (2^P.axis)→ℕ) {w : ℕ} (first : ℕ) (m : Memory w) : Prop :=
  ∀(v : Fin P.sites) (i : Fin (P.chunks 0)),m (first+v.val*P.chunks 0+i.val)=
    ((packNat P.bits (P.lanes 0) (fun j=>x v ((i.val*P.lanes 0+j) : Fin (2^P.axis)))):Word w)

theorem padded (x : Fin P.sites→Fin (2^P.axis)→ℕ) {w : ℕ} (first : ℕ) (m : Memory w)
    (last : P.dataAt first 1<2^w) (sample : P.Seed x first m) :
    (P.padProgram w first).Exec m (P.pad first m) P.padTicks ∧
      Stored first (P.hosts 0) (P.chunks 0) (P.lanes 0) P.bits
        (fun v d=>DescentWalshDyadicSums.sample x v (d : Fin (2^P.axis))) (P.pad first m) ∧
      (∀i<P.ghostBase first,P.pad first m i=m i) ∧ ∀i,P.dataAt first 1 ≤ i→P.pad first m i=m i := by
  have bound : P.ghostBase first+P.ghostRows<2^w:=(P.pad_end first).trans_lt last
  have exec : (P.padProgram w first).Exec m (P.pad first m) P.padTicks := by
    change (scan w _ _ (.lit 0)).Exec m (image _ _ (.lit 0) m) (4+6*P.ghostRows)
    rw [Nat.mul_comm 6]
    exact @scan_exec w _ _ (.lit 0) m trivial bound
  have lower (i : ℕ) (hi : i<P.ghostBase first) : P.pad first m i=m i:=ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl hi)
  have upper (i : ℕ) (hi : P.dataAt first 1 ≤ i) : P.pad first m i=m i:=ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inr ((P.pad_end first).le.trans hi))
  refine ⟨exec,?_,lower,upper⟩
  intro v hv k hk
  have before {n : ℕ} (less : v<n) : v*P.chunks 0+k<n*P.chunks 0 := by
    have pay:=Nat.mul_le_mul_right (P.chunks 0) less
    rw [Nat.succ_mul] at pay
    omega
  by_cases active : v<P.sites
  · have old:=sample ⟨v,active⟩ ⟨k,hk⟩
    have address : first+v*P.chunks 0+k<P.ghostBase first := by have lt:=before active;unfold ghostBase;omega
    simpa only [lower _ address,DescentWalshDyadicSums.sample,dite_eq_left active,
      Nat.cast_add,Nat.cast_mul] using old
  · have endOf : first+v*P.chunks 0+k<P.ghostBase first+P.ghostRows := by
      rw [P.pad_end]
      change _<first+P.hosts 0*P.chunks 0
      have lt:=before hv;omega
    have older:=Nat.mul_le_mul_right (P.chunks 0) (Nat.le_of_not_gt active)
    have after : P.ghostBase first≤first+v*P.chunks 0+k := by unfold ghostBase;omega
    let i:Fin P.ghostRows:=⟨first+v*P.chunks 0+k-P.ghostBase first,by omega⟩
    have addr : P.ghostBase first+i.val=first+v*P.chunks 0+k := by dsimp [i];omega
    have got := ProtocolRAMGeneratedWrite.read_image (P.ghostBase first) P.ghostRows (.lit 0) m i
    rw [addr] at got
    simpa only [pad,Expr.eval,DescentWalshDyadicSums.sample,dite_eq_right active,zero_pack,Nat.cast_zero] using got

theorem from_real (x : Fin P.sites→Fin (2^P.axis)→ℕ) (hx : ∀i d,x i d<2^P.bits)
    {w : ℕ} (root first : ℕ) (old : Memory w) (stat : P.headerAt root P.depth≤first)
    (space : P.dataAt first (P.depth+1)<2^w) (width : P.height≤w) (prec : P.bits+P.depth≤w)
    (base : P.Seed x first old) :
    let initial:=P.mount root old P.depth
    let padded:=P.pad first initial
    let dst:=P.state root first padded P.depth
    ((P.padProgram w first).seq (P.code w root first P.depth)).Exec initial dst (P.padTicks+P.duration P.depth) ∧
      (∀d : Fin (2^P.axis),let L:=P.lanes P.depth
        digit (P.bits+P.depth) (d.val%L) (dst (P.dataAt first P.depth+d.val/L)).val=∑v,x v d) ∧
      (∀j<first,dst j=initial j) ∧ ∀j,P.dataAt first (P.depth+1)≤j→dst j=old j := by
  let mem:=P.mount root old P.depth
  have seed : P.Seed x first mem:=by
    intro v i
    exact (P.mount_high root old P.depth _ (by omega)).trans (base v i)
  have dur : P.dataAt first 1≤P.dataAt first (P.depth+1):=P.data_mono first (by omega)
  obtain ⟨pad,loaded,lo,hi⟩:=P.padded x first mem (dur.trans_lt space) seed
  have cfg (j : ℕ) (hj : j<first) : P.pad first mem j=mem j:=
    lo j (hj.trans_le (Nat.le_add_right ..))
  obtain ⟨run,digits,low,high⟩:=P.full x hx root first _ old stat space width prec cfg loaded
  refine ⟨@Procedure.Exec.then w (P.padProgram w first) (P.code w root first P.depth)
    mem (P.pad first mem) (P.state root first (P.pad first mem) P.depth)
    P.padTicks (P.duration P.depth) (@pad) (@run),digits,fun j hj=>(low j hj).trans (cfg j hj),?_⟩
  intro j hj
  exact (high j hj).trans ((hi j (dur.trans hj)).trans
    (P.mount_high root old P.depth j (stat.trans ((P.data_mono first (Nat.zero_le _)).trans hj))))

theorem mount_low {w : ℕ} (root : ℕ) (m : Memory w) (n a : ℕ) (lo : a<root) :
    P.mount root m n a=m a := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    rw [mount]
    split
    · exact ih
    · exact ((P.tile n).before _ _ (lo.trans_le (P.header_mono root (Nat.zero_le n)))).trans ih

theorem mount_inside {w : ℕ} (root : ℕ) (m r : Memory w) (n a : ℕ)
    (low : root≤a) (high : a<P.headerAt root n) : P.mount root m n a=P.mount root r n a := by
  induction n with
  | zero=>change a<root at high;omega
  | succ n ih=>
    by_cases scalar : P.scalar n
    · simp only [mount,ite_eq_left scalar]
      apply ih
      simpa only [headerAt,headerSize,ite_eq_left scalar,Nat.add_zero] using high
    · simp only [mount,ite_eq_right scalar]
      by_cases before : a<P.headerAt root n
      · rw [Tile.before _ _ _ before,Tile.before _ _ _ before]
        exact ih before
      · have inTile : P.headerAt root n≤a ∧ a<P.headerAt root n+(P.tile n).span :=
          ⟨Nat.le_of_not_gt before,by simpa only [headerAt,headerSize,ite_eq_right scalar] using high⟩
        simp only [Tile.mount,ite_eq_left inTile]

/-- A previously installed header is a fixed point of the literal mount.
No frame condition is imposed on the dynamic input or later scratch banks. -/
theorem mount_eq_of_resident {w : ℕ} (root : ℕ) (m romSource : Memory w) (n : ℕ)
    (resident : ∀a,root≤a→a<P.headerAt root n→m a=P.mount root romSource n a) :
    P.mount root m n=m := by
  funext a
  by_cases lower : a<root
  · exact P.mount_low root m n a lower
  by_cases upper : a<P.headerAt root n
  · have lo:=Nat.le_of_not_gt lower
    exact (P.mount_inside root m romSource n a lo upper).trans (resident a lo upper).symm
  exact P.mount_high root m n a (Nat.le_of_not_gt upper)

theorem from_resident (x : Fin P.sites→Fin (2^P.axis)→ℕ) (hx : ∀i d,x i d<2^P.bits)
    {w : ℕ} (root first : ℕ) (m romSource : Memory w) (stat : P.headerAt root P.depth≤first)
    (space : P.dataAt first (P.depth+1)<2^w) (width : P.height≤w) (prec : P.bits+P.depth≤w)
    (resident : ∀a,root≤a→a<P.headerAt root P.depth→m a=P.mount root romSource P.depth a)
    (base : P.Seed x first m) :
    let dst:=P.state root first (P.pad first m) P.depth
    ((P.padProgram w first).seq (P.code w root first P.depth)).Exec m dst (P.padTicks+P.duration P.depth) ∧
      (∀d : Fin (2^P.axis),let L:=P.lanes P.depth
        digit (P.bits+P.depth) (d.val%L) (dst (P.dataAt first P.depth+d.val/L)).val=∑v,x v d) ∧
      (∀j<first,dst j=m j) ∧ ∀j,P.dataAt first (P.depth+1)≤j→dst j=m j := by
  simpa only [P.mount_eq_of_resident root m romSource P.depth resident] using
    P.from_real x hx root first m stat space width prec base

theorem resident_words (x : Fin P.sites→Fin (2^P.axis)→ℕ) (hx : ∀i d,x i d<2^P.bits)
    {w : ℕ} (root first : ℕ) (m romSource : Memory w) (stat : P.headerAt root P.depth≤first)
    (space : P.dataAt first (P.depth+1)<2^w) (width : P.height≤w) (prec : P.bits+P.depth≤w)
    (resident : ∀a,root≤a→a<P.headerAt root P.depth→m a=P.mount root romSource P.depth a)
    (base : P.Seed x first m) (i : Fin (P.chunks P.depth)) :
    let dst:=P.state root first (P.pad first m) P.depth
    let loc:=P.dataAt first P.depth+i.val
    let s:=P.bits+P.depth
    let L:=P.lanes P.depth
    (dst loc).val=packNat s L (fun j=>∑v,x v ((i.val*L+j):Fin (2^P.axis))) ∧
      (dst loc).val<2^(s*L) := by
  have front : P.dataAt first 1<2^w:=(P.data_mono first (show 1≤P.depth+1 by omega)).trans_lt space
  obtain ⟨_,src,keep,_⟩:=P.padded x first m front base
  have fixed:=P.mount_eq_of_resident root m romSource P.depth resident
  have «prefix» (j : ℕ) (hj : j<first) : P.pad first m j=P.mount root m P.depth j := by
    rw [fixed]
    exact keep j (hj.trans_le (Nat.le_add_right ..))
  have atZero : P.values x 0 =
      (fun (v d : ℕ) => DescentWalshDyadicSums.sample x v (d : Fin (2^P.axis))) := by
    funext v d
    exact DescentWalshDyadicSums.value_zero x v _
  obtain ⟨_,dst,_,_⟩:=P.runTo x hx root first _ m P.depth le_rfl stat space «prefix»
    (by simpa only [atZero] using src)
  exact P.final_word x first _ width prec dst i

theorem cheap (root first w : ℕ) :
    CheapCode ((P.padProgram w first).seq (P.code w root first P.depth)) := by
  have one (t : ℕ) : CheapCode (P.codeStep w root first t) := by
    unfold codeStep
    split <;> exact @scan_cheap w _ _ _
  have many (t : ℕ) : CheapCode (P.code w root first t) := by
    induction t with
    | zero=>exact @scan_cheap w first 0 .row
    | succ t ih=>exact cheap_seq ih (one t)
  intro l r k pc reg pub exit i
  exact @cheap_seq w (P.padProgram w first) (P.code w root first P.depth)
    (@scan_cheap w (P.ghostBase first) P.ghostRows (.lit 0)) (many P.depth)
    l r k pc reg pub exit i

theorem padding_bill (W K : ℕ) (scale : W≤K*P.height) :
    P.padTicks*W≤4*W+6*(P.sites+1)*(W+16*K*P.bits*2^P.axis) := by
  have ratio : P.lanes 0=2^P.axis ∨ P.height≤16*P.bits*P.lanes 0 := by
    simpa only [lanes,laneBits,Nat.add_zero,DescentPackedWalsh.laneBits] using
      DescentWalshDyadicBudget.laneBits_median P.axis P.height P.bits P.positive
  have block:=DescentWalshDyadicBudget.lanes (2^P.axis) (P.lanes 0) P.bits W P.height K
    (Nat.two_pow_pos _) scale ratio
  rw [show ThreeFlat.Routing.poolBatchCount (2^P.axis) (P.lanes 0)=P.chunks 0 from
    DescentWalshDyadicBudget.exact_batch P.axis (P.laneBits 0) (Nat.min_le_left ..)] at block
  have top:=DescentWalshDyadicBudget.padded_le P.sites
  have top' : P.hosts 0≤2*P.sites+1:=by simpa only [hosts,depth,Nat.sub_zero] using top
  have copies : P.hosts 0-P.sites≤P.sites+1:=by omega
  calc
    P.padTicks*W=4*W+6*(P.hosts 0-P.sites)*(W*P.chunks 0):=by unfold padTicks ghostRows;ring
    _≤_:=Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul_left 6 copies) block) _

/-- Exact labels, registers and public slots of the real instruction stream
are bounded by a constant for each host-pair level. -/
theorem program_text (w root first : ℕ) :
    DescentStaticWordColumn.names ((P.padProgram w first).seq (P.code w root first P.depth))≤
      34+183*P.depth := by
  have one (t : ℕ) : DescentStaticWordColumn.names (P.codeStep w root first t)≤183 := by
    unfold codeStep
    split
    · rw [DescentWalshScalarReduction.program,DescentStaticWordColumn.names_scan]
      change 143≤183
      decide
    · rw [DescentStaticWordColumn.names_scan]
      exact le_rfl
  have stages (t : ℕ) : DescentStaticWordColumn.names (P.code w root first t)≤19+183*t := by
    induction t with
    | zero=>rw [code,DescentStaticWordColumn.names_scan];decide
    | succ t ih=>
      rw [code,DescentStaticWordColumn.names_seq,Nat.mul_succ]
      have h:=one t
      omega
  rw [DescentStaticWordColumn.names_seq,padProgram,DescentStaticWordColumn.names_scan]
  change 15+_≤_
  have h:=stages P.depth
  omega

/-- The data bank for every level fits in two copies of the initial padded
scalar rectangle, even when the digit width changes at every level. -/
theorem data_extent (first : ℕ) :
    P.dataAt first (P.depth+1)≤first+2*(P.hosts 0*2^P.axis) := by
  let Q:=2^P.axis
  have room (t : ℕ) : P.hosts t*P.chunks t≤P.hosts t*Q :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 0<2) (Nat.sub_le ..))
  have sum (t : ℕ) (ht : t≤P.depth) :
      P.dataAt first (t+1)+P.hosts t*Q≤first+2*(P.hosts 0*Q) := by
    induction t with
    | zero=>
      change first+P.hosts 0*P.chunks 0+P.hosts 0*Q≤_
      have next:=room 0
      omega
    | succ t ih=>
      have prev:=ih (by omega)
      have host : P.hosts (t+1)*2=P.hosts t:=P.old_hosts (show t<P.depth from ht)
      have pairSize : 2*(P.hosts (t+1)*Q)=P.hosts t*Q := by
        rw [←Nat.mul_assoc,Nat.mul_comm 2,host]
      change P.dataAt first (t+1)+P.hosts (t+1)*P.chunks (t+1)+P.hosts (t+1)*Q≤_
      have next:=room (t+1)
      omega
  exact (Nat.le_add_right ..).trans (sum P.depth le_rfl)

/-- Start the input immediately after the last immutable header. This bound
includes every dynamic page and both genuine lookup tables at every age. -/
theorem buffer_end (root : ℕ) :
    P.dataAt (P.headerAt root P.depth) (P.depth+1) ≤
      root+8*(P.hosts 0*2^P.axis)+2*P.depth*2^(P.height/2) := by
  have heads:=P.static_extent root 0 P.depth
  have dyn:=P.data_extent 0
  have run:=P.data_extent (P.headerAt root P.depth)
  omega

theorem buffer_room (root w : ℕ)
    (fit : root+8*(P.hosts 0*2^P.axis)+2*P.depth*2^(P.height/2)<2^w) :
    P.dataAt (P.headerAt root P.depth) (P.depth+1)<2^w :=
  (P.buffer_end root).trans_lt fit

/-- A word holds the entire concrete contiguous realization whenever the
two aggregate widths and the incoming cursor each use at most w−2 bits. -/
theorem buffer_room_bits (root w e : ℕ) (address : e+2≤w)
    (start : root≤2^e) (rectangle : 3+P.depth+P.axis≤e)
    (tables : 1+Nat.clog 2 (P.depth+1)+P.height/2≤e) :
    P.dataAt (P.headerAt root P.depth) (P.depth+1)<2^w := by
  have left : 8*(P.hosts 0*2^P.axis)≤2^e := by
    calc
      _ = 2^(3+P.depth+P.axis) := by simp only [hosts,Nat.sub_zero,pow_add];ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) rectangle
  have depth : P.depth≤2^Nat.clog 2 (P.depth+1) :=
    (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have right : 2*P.depth*2^(P.height/2)≤2^e := by
    calc
      _ ≤ 2*(2^Nat.clog 2 (P.depth+1))*2^(P.height/2) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 depth)
      _ = 2^(1+Nat.clog 2 (P.depth+1)+P.height/2) := by simp only [pow_add,pow_one]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) tables
  have reserve : 2^(e+2)≤2^w:=Nat.pow_le_pow_right (by decide) address
  rw [pow_add] at reserve
  have positive:=Nat.two_pow_pos e
  apply P.buffer_room
  omega

theorem header_offset (root n : ℕ) : P.headerAt root n=root+P.headerAt 0 n := by
  induction n with
  | zero=>simp [headerAt]
  | succ n ih=>simp only [headerAt,ih,Nat.add_assoc]

theorem data_offset (first n : ℕ) : P.dataAt first n=first+P.dataAt 0 n := by
  induction n with
  | zero=>simp [dataAt]
  | succ n ih=>simp only [dataAt,ih,Nat.add_assoc]

/-- The same footprint covers globally grouped static sections followed by
globally grouped dynamic sections. Sections may choose different public axes. -/
theorem calendar_extent {n : ℕ} (plans : Fin n→Plan) (root k area level half : ℕ)
    (count : n≤k+1)
    (sizes : ∀i,(plans i).hosts 0*2^(plans i).axis≤area ∧
      (plans i).depth≤level ∧ (plans i).height/2≤half) :
    root+(∑ i,(plans i).headerAt 0 (plans i).depth)+(∑ i,(plans i).dataAt 0 ((plans i).depth+1))≤
      root+(k+1)*(8*area+2*level*2^half) := by
  have sectionSize (i : Fin n) : (plans i).headerAt 0 (plans i).depth+
      (plans i).dataAt 0 ((plans i).depth+1)≤8*area+2*level*2^half := by
    have h:=(plans i).buffer_end 0
    rw [(plans i).data_offset] at h
    simp only [Nat.zero_add] at h
    obtain ⟨box,depth,width⟩:=sizes i
    exact h.trans (Nat.add_le_add (Nat.mul_le_mul_left 8 box)
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 depth) (Nat.pow_le_pow_right (by decide : 0<2) width)))
  rw [Nat.add_assoc,←Finset.sum_add_distrib]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _ : Fin n, (8*area+2*level*2^half) := Finset.sum_le_sum (fun i _=>sectionSize i)
    _ = n*(8*area+2*level*2^half) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ count

/-- Sum the literal stream sizes of any calendar of at most k+1 reductions;
each selected plan may have its own digit width, address range and cut. -/
theorem calendar_text {n : ℕ} (plans : Fin n→Plan) (root first : Fin n→ℕ) (w k d : ℕ)
    (count : n≤k+1) (height : ∀i,(plans i).depth≤d) :
    (∑ i,DescentStaticWordColumn.names (((plans i).padProgram w (first i)).seq
      ((plans i).code w (root i) (first i) (plans i).depth)))≤(k+1)*(34+183*d) := by
  calc
    _ ≤ ∑ _ : Fin n,(34+183*d) := Finset.sum_le_sum (fun i _=>
      ((plans i).program_text w (root i) (first i)).trans
        (Nat.add_le_add_left (Nat.mul_le_mul_left 183 (height i)) 34))
    _ = n*(34+183*d) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ count

/-- Every pointer column is charged by the scan which reads it. Only the
two short tables per level have an additional literal ROM tariff. -/
theorem header_clock (root t W : ℕ) :
    (P.headerAt root t-root)*W ≤ P.duration t*W+2*t*2^(P.height/2)*W := by
  have paid (n : ℕ) : P.headerAt root n ≤ root+P.duration n+2*n*2^(P.height/2) := by
    induction n with
    | zero=>simp [headerAt,duration]
    | succ n ih=>
      have header:=P.step_header_bound n
      have charge : 3*(P.hosts (n+1)*P.chunks (n+1))≤P.ticks n := by
        change _≤4+(if P.scalar n then 70 else 90)*(P.hosts (n+1)*P.chunks (n+1))
        split <;> omega
      change P.headerAt root n+P.headerSize n≤root+(P.duration n+P.ticks n)+
        2*(n+1)*2^(P.height/2)
      rw [Nat.mul_succ,Nat.add_mul]
      omega
  have amount : P.headerAt root t-root≤P.duration t+2*t*2^(P.height/2):=by
    have h:=paid t
    omega
  simpa only [Nat.add_mul] using Nat.mul_le_mul_right W amount

theorem header_bill (root W K : ℕ) (scale : W≤K*P.height) (host : P.sites≤2^W)
    (precision : P.bits≤W+1) :
    (P.headerAt root P.depth-root)*W ≤ 4*W+2008*(P.sites+1)*W+
      25600*K*(P.sites+1)*2^P.axis*(P.bits+1)+12800*K*2^P.axis*(W+1)^2+
        2*P.depth*2^(P.height/2)*W :=
  (P.header_clock root P.depth W).trans (Nat.add_le_add_right (P.clock W K scale host precision) _)

/-- Combined clock of the authentic ghost fill and complete reduction,
measured in word-bit operations. -/
def wordBill (H m b W K : ℕ) :=
  (4*W+6*(H+1)*(W+16*K*b*2^m))+
  (4*W+2008*(H+1)*W+25600*K*(H+1)*2^m*(b+1)+12800*K*2^m*(W+1)^2)

theorem program_bill (W K : ℕ) (scale : W≤K*P.height) (host : P.sites≤2^W)
    (precision : P.bits≤W+1) :
    (P.padTicks+P.duration P.depth)*W≤wordBill P.sites P.axis P.bits W K := by
  rw [Nat.add_mul]
  exact Nat.add_le_add (P.padding_bill W K scale) (P.clock W K scale host precision)

/-- Public calendar columns can select different bit precisions and
packing shapes. Each stage keeps its literal charged time. -/
theorem calendar_bill {n : ℕ} (plans : Fin n→Plan) (k H m b W K : ℕ)
    (count : n≤k+1) (host : H≤2^W) (digits : b≤W+1)
    (shape : ∀i,(plans i).sites≤H ∧ (plans i).axis≤ m ∧ (plans i).bits≤b ∧ W≤K*(plans i).height) :
    (∑ i,((plans i).padTicks+(plans i).duration (plans i).depth)*W)≤
      (k+1)*wordBill H m b W K := by
  have upper (i : Fin n) : ((plans i).padTicks+(plans i).duration (plans i).depth)*W≤wordBill H m b W K := by
    obtain ⟨sites,axis,bits,scaled⟩:=shape i
    apply ((plans i).program_bill W K scaled (sites.trans host) (bits.trans digits)).trans
    unfold wordBill
    gcongr
  calc
    _ ≤ ∑ _ : Fin n, wordBill H m b W K := Finset.sum_le_sum (fun i _=>upper i)
    _ = n*wordBill H m b W K := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ count

theorem calendar_header_bill {n : ℕ} (plans : Fin n→Plan) (roots : Fin n→ℕ)
    (k H m b W K level half : ℕ) (count : n≤k+1) (host : H≤2^W) (digits : b≤W+1)
    (shape : ∀i,(plans i).sites≤H ∧ (plans i).axis≤ m ∧ (plans i).bits≤b ∧ W≤K*(plans i).height)
    (layers : ∀i,(plans i).depth≤level ∧ (plans i).height/2≤half) :
    (∑ i,((plans i).headerAt (roots i) (plans i).depth-roots i)*W)≤
      (k+1)*(wordBill H m b W K+2*level*2^half*W) := by
  have each (i : Fin n) : ((plans i).headerAt (roots i) (plans i).depth-roots i)*W≤
      ((plans i).padTicks+(plans i).duration (plans i).depth)*W+2*level*2^half*W := by
    apply ((plans i).header_clock (roots i) (plans i).depth W).trans
    apply Nat.add_le_add
    · exact Nat.mul_le_mul_right _ (Nat.le_add_left ..)
    · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (layers i).1)
        (Nat.pow_le_pow_right (by decide : 0<2) (layers i).2))
  calc
    _ ≤ ∑ i, (((plans i).padTicks+(plans i).duration (plans i).depth)*W+2*level*2^half*W) :=
      Finset.sum_le_sum (fun i _=>each i)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib,Nat.mul_add]
      apply Nat.add_le_add (calendar_bill plans k H m b W K count host digits shape)
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using
        Nat.mul_le_mul_right (2*level*2^half*W) count

end
end Hierarchy.DescentPackedWalshReduction.Plan

end OAI
