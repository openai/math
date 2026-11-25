import OAI.ThreeFlat.Diagonal.PhysicalNodeProgram
import OAI.ThreeFlat.RAM.AdmissionPost

namespace OAI
/-! # The native charge and parent scans of one true chronological node layer -/

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.NavigationNodeRows
open RAM.PhysicalPinsExpr RAM.DescriptorExpr RAM.DescriptorScan
open scoped Fin.CommRing Classical
variable {W : ℕ}

abbrev natural (m : Memory W) (x : ℕ) := (m x).val

def LayerRecord (_b : Banks) (s : Layer) (p : Parent) (owners : Fin s.count → ℕ)
    (cost : Fin s.count → Fin 2 → ℕ) (j : Fin s.count) : HistoryNodeDirectory.Node ℕ where
  kind := s.kind
  parent := if p.finalLayer then s.first+j.val else p.first+owners j
  ordinal := j.val
  childPtr := s.children+j.val*s.childCount
  childCount := s.childCount
  kernelPtr := s.kernels+j.val*5
  incidentPtr := s.incident+j.val*2
  externalCount := 2*cost j 1

/-- An absolute address in a rectangular row-major word bank. -/
def wordAt {rows stride : ℕ} (base : ℕ) (value : Fin rows→Fin stride→ℕ) (x : ℕ) : Word W :=
  if j : (x-base)/stride<rows then if c : (x-base)%stride<stride then
    (value ⟨_,j⟩ ⟨_,c⟩:Word W) else 0 else 0

theorem wordAt_read {rows stride : ℕ} (base : ℕ) (value : Fin rows→Fin stride→ℕ)
    (j : Fin rows) (c : Fin stride) : wordAt (W:=W) base value (base+stride*j.val+c.val)=(value j c:Word W) := by
  have z : base+stride*j.val+c.val-base=c.val+stride*j.val := by omega
  have d : (c.val+stride*j.val)/stride=j.val := by
    rw [Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt c.isLt),Nat.div_eq_of_lt c.isLt,Nat.zero_add]
  have r : (c.val+stride*j.val)%stride=c.val := by simp [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt c.isLt]
  simp only [wordAt,z,d,r,dite_eq_left j.isLt,dite_eq_left c.isLt]

def charged (b : Banks) {s : Layer} (m : Memory W) (val : Fin s.count→Fin 2→ℕ) :=
  fillSegment (b.charges+2*s.first) (2*s.count) (wordAt (b.charges+2*s.first) val) m

def recorded (b : Banks) {s : Layer} (m : Memory W) (val : Fin s.count→Fin 8→ℕ) :=
  fillSegment (b.nodes+8*s.first) (8*s.count) (wordAt (b.nodes+8*s.first) val) m

/-- The exact memory returned by the two scans and six-instruction next-header transfer. -/
def emitted (b : Banks) (s : Layer) (p : Parent) (next : ℕ) (m : Memory W)
    (val : Fin s.count→Fin 2→ℕ) (owners : Fin s.count→ℕ) : Memory W :=
  writeMemory (recorded b (s:=s) (charged b (s:=s) m val)
    (fun j => (LayerRecord b s p owners val j).words)) (b.current:Word W) (next:Word W)

theorem charged_read (b : Banks) (s : Layer) (m : Memory W) (val : Fin s.count→Fin 2→ℕ)
    (j : Fin s.count) (c : Fin 2) :
    charged b (s:=s) m val (b.charges+2*(s.first+j.val)+c.val)=(val j c:Word W) := by
  let a:=b.charges+2*s.first
  have ix : b.charges+2*(s.first+j.val)+c.val=a+2*j.val+c.val := by dsimp [a];omega
  rw [ix]
  change (if a≤a+2*j.val+c.val ∧ a+2*j.val+c.val<a+2*s.count then _ else _) = _
  rw [ite_eq_left (by have:=j.isLt;have:=c.isLt;omega)]
  exact wordAt_read a val j c

theorem recorded_read (b : Banks) (s : Layer) (m : Memory W) (val : Fin s.count→Fin 8→ℕ)
    (j : Fin s.count) (c : Fin 8) :
    recorded b (s:=s) m val (b.nodes+8*(s.first+j.val)+c.val)=(val j c:Word W) := by
  let a:=b.nodes+8*s.first
  have ix : b.nodes+8*(s.first+j.val)+c.val=a+8*j.val+c.val := by dsimp [a];omega
  rw [ix]
  change (if a≤a+8*j.val+c.val ∧ a+8*j.val+c.val<a+8*s.count then _ else _) = _
  rw [ite_eq_left (by have:=j.isLt;have:=c.isLt;omega)]
  exact wordAt_read a val j c

structure Mounted (b : Banks) (s : Layer) (p : Parent) (hdr next : ℕ) (m : Memory W) : Prop where
  current : (m b.current).val=hdr
  words : ∀ j<14,(m (hdr+j)).val=header b s p next j

theorem Mounted.column {b : Banks} {s : Layer} {p : Parent} {hdr next : ℕ} {m : Memory W}
    (h : Mounted b s p hdr next m) : ∀ j<14,b.column (natural m) j=header b s p next j := by
  intro j hj
  simpa only [Banks.column,natural,h.current] using h.words j hj

theorem Mounted.agree {b : Banks} {s : Layer} {p : Parent} {hdr next t : ℕ} {m m' : Memory W}
    (h : Mounted b s p hdr next m) (ctl : b.current<t) (words : hdr+14≤t)
    (same : ∀ x,x<t→m' x=m x) : Mounted b s p hdr next m' where
  current := by rw [same _ ctl];exact h.current
  words j hj := by rw [same _ (by omega)];exact h.words j hj

private theorem closedScan (m : Memory W) (b : Banks) (e : Formula 1) (hdr off len base n : ℕ)
    (word : ℕ→Word W) (hctl : b.current<2^W) (ho : hdr+off<2^W) (hl : hdr+len<2^W)
    (room : base+n<2^W) (curr : (m b.current).val=hdr)
    (start : (m (hdr+off)).val=base) (count : (m (hdr+len)).val=n)
    (each : ∀ (addr : Word W) (m' : Memory W),base≤addr.val→addr.val<base+n→
      agreesOutside base (base+n) m' m →
      e.Fits W (fun _=>0) (natural m') (fun _=>addr.val) ∧
      (e.natural W (fun _=>0) (natural m') (fun _=>addr.val):Word W)=word addr.val) :
    (HeaderScan.procedure (b.current:Word W) off len (HeaderScan.closed e)).Spec
      (fun x=>x=m) (fun _ out=>out=fillSegment base n word m)
      (13+n*(2*(HeaderScan.closed (w:=W) e).binds+4)) := by
  have cv : m b.current=(hdr:Word W) := by
    rw [←curr,Fin.cast_val_eq_self]
  have atHeader (j : ℕ) (h : hdr+j<2^W) :
      (m ((b.current:Word W).val)+(j:Word W)).val=hdr+j := by
    rw [Fin.val_cast_of_lt hctl,cv,←Nat.cast_add,Fin.val_cast_of_lt h]
  intro _ _ _ machine
  refine Procedure.Spec.atMemory
    (A:=HeaderScan.procedure (b.current:Word W) off len (HeaderScan.closed e))
    (HeaderScan.spec (b.current:Word W) off len (HeaderScan.closed e) (fun x=>x=m)
      (fun _=>base) (fun _=>n) (fun _=>word) _ ?_ ?_ ?_) m rfl machine
  · exact fun _ _=>⟨room,le_rfl⟩
  · rintro _ rfl
    rw [atHeader off ho,atHeader len hl,←start,←count,Fin.cast_val_eq_self,Fin.cast_val_eq_self]
    exact ⟨rfl,rfl⟩
  · rintro _ rfl addr m' lo hi keep
    obtain ⟨ok,read⟩:=each addr m' lo hi keep
    have core:=e.value_eq_natural (fun _=>0) (natural m') (fun _=>addr.val) ok
    simpa only [HeaderScan.eval_closed,natural,Nat.cast_zero,Fin.cast_val_eq_self] using core.trans read

end ThreeFlat.Diagonal.NavigationPass.NodePublication

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.NavigationNodeRows
open RAM.PhysicalPinsExpr RAM.DescriptorExpr RAM.DescriptorScan
open scoped Fin.CommRing Classical
variable {W : ℕ} {b : Banks} {s : Layer} {p : Parent} {hdr next : ℕ}

/-- The controls and published stage records precede the disjoint charge and node arrays.
The raw lane endpoints are the only potentially large operands of the leaf subtraction. -/
structure Bounds (W : ℕ) (b : Banks) (s : Layer) (p : Parent) (hdr cc hc mc : ℕ) : Prop where
  wide : 16<2^W
  current : b.current<b.charges
  header : hdr+16≤b.charges
  chargeEnd : b.charges+2*(s.first+s.count)≤b.nodes
  nodeEnd : b.nodes+8*(s.first+s.count)<2^W
  ownerEnd : p.finalLayer=false → p.owners+s.count≤b.charges
  arity : s.childCount≤cc
  caps : max cc (max hc mc)<2^W
  lanes : b.lanes<2^W
  pairs : b.totalPairs<2^W
  perLane : b.perLanePairs<2^W
  leafSpan : ∀ j : Fin s.count,s.kind=0 → j.val<b.lanes → j.val*b.perLanePairs<2^W

/-- The input to one chronological pass consists of real words. The child and owner
arrays and the local motif/width rows are read directly from the emitted stage records. -/
structure StageInput (b : Banks) {s : Layer} (d : LayerData s) (p : Parent)
    (hdr next hc mc : ℕ) (owners : Fin s.count→ℕ) (prior : ℕ→Fin 2→ℕ) (m : Memory W) : Prop where
  mounted : Mounted b s p hdr next m
  records : d.Reads (natural m)
  low : d.Below (2^W) (natural m)
  separate : d.Footprint (fun x => x<b.charges ∨ b.nodes+8*(s.first+s.count)≤x) (natural m)
  parents : ParentReads p owners (natural m)
  old : ∀ j i,d.child j i<s.first
  charges : ∀ j i (c : Fin 2),(m (b.charges+2*d.child j i+c.val)).val=prior (d.child j i) c
  halves : ∀ j,(d.halfWidth j).length≤hc
  motifs : s.kind≠0 → ∀ j,(d.motifCopies j).length ≤ mc
  result : ∀ j,d.cost b prior j 1<2^W

private theorem below_charged {m : Memory W} (val : Fin s.count→Fin 2→ℕ) (x : ℕ)
    (hx : x<b.charges+2*s.first) : charged b (s:=s) m val x=m x := by
  simp only [charged,fillSegment,not_le_of_gt hx,false_and,ite_false]

private theorem below_recorded {m : Memory W} (val : Fin s.count→Fin 8→ℕ) (x : ℕ)
    (hx : x<b.nodes+8*s.first) : recorded b (s:=s) m val x=m x := by
  simp only [recorded,fillSegment,not_le_of_gt hx,false_and,ite_false]

private theorem nodeRecord_read {m : Memory W} {owners : Fin s.count→ℕ}
    {val : Fin s.count→Fin 2→ℕ} (ready : Mounted b s p hdr next m)
    (par : ParentReads p owners (natural m)) (j : Fin s.count)
    (chargedPair : (m (b.charges+2*(s.first+j.val)+1)).val=val j 1) :
    b.nodeRecord (natural m) j.val=LayerRecord b s p owners val j := by
  have r (i : ℕ) (hi : i<14) := ready.column i hi
  cases hp : p.finalLayer <;>
    simp only [Banks.nodeRecord,LayerRecord,r 5 (by decide),r 6 (by decide),r 11 (by decide),
      r 12 (by decide),r 13 (by decide),r 8 (by decide),r 7 (by decide),r 9 (by decide),
      r 10 (by decide),header,hp,Bool.false_eq_true,ite_false,ite_true,Nat.zero_ne_one,
      Nat.mul_comm (s.first+j.val) 2,natural,chargedPair]
  all_goals first | rw [show (m (p.owners+j.val)).val=owners j from par hp j]

private theorem scanNodes {d : LayerData s} {owners : Fin s.count→ℕ} {prior : ℕ→Fin 2→ℕ}
    {cc hc mc : ℕ} {m : Memory W} (room : Bounds W b s p hdr cc hc mc)
    (input : StageInput b d p hdr next hc mc owners prior m) :
    let val := d.cost b prior
    let first := charged b (s:=s) m val
    (HeaderScan.procedure (b.current:Word W) 2 3 (HeaderScan.closed (node b))).Spec
      (fun x=>x=first) (fun _ out=>out=recorded b (s:=s) first (fun j=>(LayerRecord b s p owners val j).words))
      (13+8*s.count*(2*(HeaderScan.closed (w:=W) (node b)).binds+4)) := by
  intro val first
  let lo:=b.nodes+8*s.first
  let words : Fin s.count→Fin 8→ℕ := fun j=>(LayerRecord b s p owners val j).words
  have ctl:=room.current
  have headerRoom:=room.header
  have a:=room.chargeEnd
  have bEnd:=room.nodeEnd
  have before (x : ℕ) (hx : x<b.charges) : first x=m x :=
    below_charged val x (by omega)
  have installed := input.mounted.agree ctl (by omega) before
  apply closedScan first b (node b) hdr 2 3 lo (8*s.count) (wordAt lo words) (by omega)
    (by omega) (by omega) (by dsimp [lo];omega) installed.current
    (installed.words 2 (by decide)) (installed.words 3 (by decide))
  intro addr m' lower upper keep
  let r : Fin s.count := ⟨(addr.val-lo)/8,by omega⟩
  let c : Fin 8 := ⟨(addr.val-lo)%8,Nat.mod_lt _ (by decide)⟩
  have addrEq : addr.val=lo+8*r.val+c.val := by dsimp [r,c];omega
  have low (x : ℕ) (hx : x<lo) := keep x (Or.inl hx)
  have hold (x : ℕ) (hx : x<b.charges) : m' x=m x :=
    (low x (by dsimp [lo];omega)).trans (before x hx)
  have current := input.mounted.agree ctl (by omega) hold
  have rd := current.column
  have rroom : NodeRoom W b (natural m') s.count := by
    refine ⟨by have:=room.wide;omega,by omega,?_,?_,?_,?_,?_⟩
    · change (m' b.current).val+13<2^W
      rw [current.current];omega
    · rw [rd 2 (by decide)];change b.nodes+8*s.first+8*s.count≤_;omega
    · rw [rd 11 (by decide),rd 13 (by decide)]
      intro nf
      have flag : p.finalLayer=false := by cases h : p.finalLayer <;> simp_all [header]
      change p.owners+s.count≤_
      exact (room.ownerEnd flag).trans (by omega)
    · rw [rd 5 (by decide)];exact a.trans (by omega)
    · rw [rd 11 (by decide)]
      change (if p.finalLayer then 1 else 0)<2^W
      refine Nat.lt_of_le_of_lt ?_ room.wide
      split <;> decide
  have relative : addr.val=b.column (natural m') 2+8*r.val+c.val := by
    rw [rd 2 (by decide)];exact addrEq
  refine ⟨node_fits b (natural m') (fun _=>0) (fun _=>addr.val) _ _ c rroom r.isLt relative,?_⟩
  have parent : ParentReads p owners (natural m') := by
    intro h j
    rw [show natural m' (p.owners+j.val)=natural m (p.owners+j.val) from
      congrArg Fin.val (hold _ (by have := room.ownerEnd h;have := j.isLt;omega))]
    exact input.parents h j
  have pair : (m' (b.charges+2*(s.first+r.val)+1)).val=val r 1 := by
    rw [low _ (by dsimp [lo];have :=r.isLt;omega)]
    have fits : val r 1<2^W:=input.result r
    calc
      _ = (val r 1 : Word W).val := by
        simpa only [first,Fin.val_one] using congrArg Fin.val (charged_read b s m val r 1)
      _ = val r 1 := Fin.val_cast_of_lt fits
  have nEq:=nodeRecord_read current parent r pair
  rw [node_read b (natural m') (fun _=>0) (fun _=>addr.val) _ c relative,nEq,addrEq,wordAt_read]

end ThreeFlat.Diagonal.NavigationPass.NodePublication

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.NavigationNodeRows
open RAM.PhysicalPinsExpr RAM.DescriptorExpr RAM.DescriptorScan
open scoped Fin.CommRing Classical
variable {W : ℕ} {b : Banks} {s : Layer} {p : Parent} {hdr next : ℕ}

private theorem rect_le (start rows stride cap : ℕ) (emptyStart : start≤cap)
    (bits : ∀ (j : Fin rows) (i : Fin stride), start+j.val*stride+i.val<cap) :
    start+rows*stride≤cap := by
  cases rows with
  | zero => simpa using emptyStart
  | succ n =>
    cases stride with
    | zero => simpa using emptyStart
    | succ k =>
      have last:=bits ⟨n,by omega⟩ ⟨k,by omega⟩
      change start+n*(k+1)+k<cap at last
      rw [Nat.succ_mul]
      omega

/-- The sizes of every actually read metadata word and every child charge ensure the
unrolled formula agrees with its natural-number semantics, even on zero-length rows. -/
private theorem chargeRoom {d : LayerData s} {owners : Fin s.count→ℕ} {prior : ℕ→Fin 2→ℕ}
    {cc hc mc : ℕ} {m m' : Memory W} (room : Bounds W b s p hdr cc hc mc)
    (input : StageInput b d p hdr next hc mc owners prior m)
    (keep : ∀ x,x<b.charges+2*s.first ∨ b.nodes≤x→m' x=m x) :
    ChargeRoom W b (natural m') s.count cc hc mc := by
  have early (x : ℕ) (hx : x<b.charges) := keep x (.inl (by omega))
  have safe (x : ℕ) (hx : x<b.charges ∨ b.nodes+8*(s.first+s.count)≤x) :=
    congrArg Fin.val (keep x (by rcases hx with l|r <;> omega))
  have r := input.mounted.agree room.current (by have:=room.header;omega) early
  have vals := r.column
  have reads := input.records.of_footprint input.separate safe
  have low := input.low.of_footprint input.separate safe
  have lim:=room.nodeEnd
  have sep:=room.chargeEnd
  have h6 : b.column (natural m') 6=s.kind := vals 6 (by decide)
  have h7 : b.column (natural m') 7=s.childCount := vals 7 (by decide)
  have h8 : b.column (natural m') 8=s.children := vals 8 (by decide)
  have h9 : b.column (natural m') 9=s.kernels := vals 9 (by decide)
  have h10 : b.column (natural m') 10=s.incident := vals 10 (by decide)
  have cap' := room.caps
  have real (i : ℕ) : b.column (natural m') i<2^W := (m' _).isLt
  refine { wide:=by have:=room.wide;omega
           control:=by have:=room.current;omega
           header:=by change (m' b.current).val+13<_;rw [r.current];have:=room.header;omega
           output:=by rw [vals 0 (by decide)];change b.charges+2*s.first+2*s.count≤_;omega
           childCap:=by omega
           halfCap:=by omega
           motifCap:=by omega
           kind:=real _
           childCount:=real _
           children:=?_
           prior:=?_
           incident:=?_
           halves:=fun j=>(m' _).isLt
           width:=?_
           kernels:=?_
           motifs:=fun _ j=>(m' _).isLt
           copies:=?_
           lanes:=fun _=>room.lanes
           pairs:=room.pairs
           perLane:=room.perLane
           laneOffset:=?_ }
  · rw [h7,h8]
    apply rect_le _ _ _ _ (h8 ▸ (real 8).le)
    intro j i;have:=low.child j i;omega
  · intro j i hi
    rw [h7] at hi
    rw [h8,h7]
    have childRead := reads.child j ⟨i.val,hi⟩
    change natural m' (s.children+j.val*s.childCount+i.val)=_ at childRead
    rw [childRead]
    have old:=input.old j ⟨i.val,hi⟩
    omega
  · rw [h10,Nat.mul_comm 2]
    apply rect_le _ _ _ _ (h10 ▸ (real 10).le)
    intro j i;have:=low.halves j;have:=i.isLt;omega
  · intro j i hi
    rw [h10] at hi
    change i.val < (m' (s.incident+j.val*2)).val at hi
    rw [reads.halves j] at hi
    rw [h10]
    exact low.width j ⟨i.val,hi⟩
  · rw [h6,h9,Nat.mul_comm 5]
    intro h
    apply rect_le _ _ _ _ (h9 ▸ (real 9).le)
    intro j i;have:=low.motifs h j;have:=i.isLt;omega
  · intro nz j i hi
    rw [h6] at nz
    rw [h9] at hi
    change i.val < (m' (s.kernels+j.val*5+3)).val at hi
    rw [reads.motifs nz j] at hi
    rw [h9]
    exact low.copies nz j ⟨i.val,hi⟩
  · rw [h6]
    intro zero j live
    exact room.leafSpan j zero live

private theorem scanCharges {d : LayerData s} {owners : Fin s.count→ℕ} {prior : ℕ→Fin 2→ℕ}
    {cc hc mc : ℕ} {m : Memory W} (room : Bounds W b s p hdr cc hc mc)
    (input : StageInput b d p hdr next hc mc owners prior m) :
    (HeaderScan.procedure (b.current:Word W) 0 1 (HeaderScan.closed (charge b cc hc mc))).Spec
      (fun x=>x=m) (fun _ out=>out=charged b (s:=s) m (d.cost b prior))
      (13+2*s.count*(2*(HeaderScan.closed (w:=W) (charge b cc hc mc)).binds+4)) := by
  let lo:=b.charges+2*s.first
  have reg:=room.header
  have ctl:=room.current
  have sep:=room.chargeEnd
  have enclosing:=room.nodeEnd
  apply closedScan m b (charge b cc hc mc) hdr 0 1 lo (2*s.count) (wordAt lo (d.cost b prior))
    (by omega) (by omega) (by omega) (by dsimp [lo];omega)
    input.mounted.current (input.mounted.words 0 (by decide)) (input.mounted.words 1 (by decide))
  intro addr m' lower upper keep
  let j : Fin s.count:=⟨(addr.val-lo)/2,by omega⟩
  let c : Fin 2:=⟨(addr.val-lo)%2,Nat.mod_lt _ (by decide)⟩
  have eq : addr.val=lo+2*j.val+c.val := by dsimp [j,c];omega
  have early (x : ℕ) (hx : x<b.charges) : m' x=m x := keep x (.inl (by dsimp [lo];omega))
  have mounted := input.mounted.agree ctl (by omega) early
  have old (i : Fin s.childCount) (col : Fin 2) :
      natural m' (b.charges+2*d.child j i+col.val)=prior (d.child j i) col := by
    have hb:=input.old j i
    have oldAddress : b.charges+2*d.child j i+col.val < lo := by dsimp [lo];have:=col.isLt;omega
    change (m' _).val=_
    rw [keep _ (.inl oldAddress)]
    exact input.charges j i col
  have reach : addr.val=b.column (natural m') 0+2*j.val+c.val := by rw [mounted.column 0 (by decide)];exact eq
  refine ⟨charge_fits b (natural m') (fun _=>0) (fun _=>addr.val) _ cc hc mc _ c
    (chargeRoom room input (fun x hx=>keep x (hx.imp_right (fun z=>by dsimp [lo];omega)))) j.isLt reach,?_⟩
  have read := d.charge_natural (W:=W) b p next (natural m') (fun _=>0) (fun _=>addr.val)
    prior cc hc mc j c (input.records.of_footprint input.separate (fun x hx=>congrArg Fin.val (keep x (by
      dsimp [lo];rcases hx with l|r <;> omega))))
    mounted.column room.arity (input.halves j) (fun h=>input.motifs h j) old reach
  rw [read,eq,wordAt_read]

def ticks (W : ℕ) (b : Banks) (cc hc mc n : ℕ) :=
  (13+2*n*(2*(HeaderScan.closed (w:=W) (charge b cc hc mc)).binds+4))+
    ((13+8*n*(2*(HeaderScan.closed (w:=W) (node b)).binds+4))+6)

/-- Execute real mutable scans for the full layer, then load the next header pointer.
All source/child facts come from the public words of this same execution. -/
theorem publish_layer_spec {d : LayerData s} {owners : Fin s.count→ℕ} {prior : ℕ→Fin 2→ℕ}
    {cc hc mc : ℕ} {m : Memory W} (room : Bounds W b s p hdr cc hc mc)
    (input : StageInput b d p hdr next hc mc owners prior m) :
    (NavigationNodeRows.procedure b cc hc mc).Spec (fun x=>x=m)
      (fun _ out=>out=emitted b s p next m (d.cost b prior) owners)
      (ticks W b cc hc mc s.count) := by
  let val:=d.cost b prior
  let first:=charged b (s:=s) m val
  let middle:=recorded b (s:=s) first (fun j=>(LayerRecord b s p owners val j).words)
  intro labels regs slots
  apply Procedure.Spec.mono
    (Procedure.Spec.seq (scanCharges room input)
      (Procedure.Spec.seq (scanNodes room input) (NextStage.spec (b.current:Word W) middle)
        (fun _ _ h=>h))
      (fun _ _ h=>h)) (fun _ h=>h) ?_ le_rfl
  rintro x out ⟨_,rfl,_,rfl,rfl⟩
  have ctl:=room.current; have hdrFit:=room.header;have t:=room.chargeEnd;have end':=room.nodeEnd
  have low (i : ℕ) (hi : i<b.charges) : middle i=m i :=
    (below_recorded _ i (by omega)).trans (below_charged _ i (by omega))
  have pctl : middle ((b.current:Word W).val)=(hdr:Word W) := by
    rw [Fin.val_cast_of_lt (by omega : b.current<2^W),low _ ctl,←input.mounted.current,Fin.cast_val_eq_self]
  have nextValue : middle ((middle ((b.current:Word W).val))+4).val=(next:Word W) := by
    rw [pctl,show (4:Word W)=((4:ℕ):Word W) from rfl,←Nat.cast_add,
      Fin.val_cast_of_lt (by omega : hdr+4<2^W),low _ (by omega)]
    have nextWord : (m (hdr+4)).val=next := input.mounted.words 4 (by decide)
    exact (Fin.cast_val_eq_self (m (hdr+4))).symm.trans
      (congrArg (fun z : ℕ => (z : Word W)) nextWord)
  exact congrArg (writeMemory middle (b.current:Word W)) nextValue

end ThreeFlat.Diagonal.NavigationPass.NodePublication

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.NavigationNodeRows
open scoped Fin.CommRing
variable {W cc hc mc hdr : ℕ} {s : Layer} {p : Parent} {b : Banks}
    {m : Memory W} {next : ℕ} {val : Fin s.count→Fin 2→ℕ} {owners : Fin s.count→ℕ}

theorem emitted_current (room : Bounds W b s p hdr cc hc mc) :
    emitted b s p next m val owners b.current=(next:Word W) := by
  have ctl := room.current;have a:=room.chargeEnd;have end':=room.nodeEnd
  simp [emitted,writeMemory,Fin.val_cast_of_lt (by omega : b.current<2^W)]

theorem emitted_charge (room : Bounds W b s p hdr cc hc mc) (j : Fin s.count) (c : Fin 2) :
    emitted b s p next m val owners (b.charges+2*(s.first+j.val)+c.val)=(val j c:Word W) := by
  have ctl:=room.current;have a:=room.chargeEnd;have t:=room.nodeEnd
  have j' := j.isLt;have c' := c.isLt
  simp only [emitted,writeMemory,Fin.val_cast_of_lt (by omega : b.current<2^W),
    ite_eq_right (show b.charges+2*(s.first+j.val)+c.val≠b.current by omega)]
  rw [below_recorded _ _ (by omega)]
  exact charged_read b s m val j c

theorem emitted_node (room : Bounds W b s p hdr cc hc mc) (j : Fin s.count) (c : Fin 8) :
    emitted b s p next m val owners (b.nodes+8*(s.first+j.val)+c.val)=
      ((LayerRecord b s p owners val j).words c:Word W) := by
  have ctl := room.current;have a:=room.chargeEnd;have t:=room.nodeEnd
  simp only [emitted,writeMemory,Fin.val_cast_of_lt (by omega : b.current<2^W),
    ite_eq_right (show b.nodes+8*(s.first+j.val)+c.val≠b.current by omega)]
  exact recorded_read b s _ _ j c

theorem emitted_frame (room : Bounds W b s p hdr cc hc mc) (x : ℕ) (ctl : x≠b.current)
    (work : x<b.charges+2*s.first ∨ b.charges+2*(s.first+s.count)≤x)
    (nodes : x<b.nodes+8*s.first ∨ b.nodes+8*(s.first+s.count)≤x) :
    emitted b s p next m val owners x=m x := by
  have c:=room.current;have first:=room.chargeEnd;have t:=room.nodeEnd
  have wsep : ¬(b.charges+2*s.first≤x ∧ x<b.charges+2*s.first+2*s.count) := by omega
  have nsep : ¬(b.nodes+8*s.first≤x ∧ x<b.nodes+8*s.first+8*s.count) := by omega
  simp only [emitted,writeMemory,Fin.val_cast_of_lt (by omega : b.current<2^W),ite_eq_right ctl,
    recorded,charged,fillSegment,ite_eq_right wsep,ite_eq_right nsep]

end ThreeFlat.Diagonal.NavigationPass.NodePublication

end OAI
