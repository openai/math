import OAI.Hierarchy.DescentPackedOperandFields
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Installation and address space of the common ordinary operand tables -/
namespace Hierarchy.DescentPackedOperand.ROM
open DescentSIMDLookup DescentPacking.PackedMatch.Local Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

def page (k M : ℕ) := 2^(unit k*M)
def rowBits (H r M : ℕ) := Nat.clog 2 (H*chunks r M+1)
def rows (H r M : ℕ) := 2^(rowBits H r M)
def maskBase (base k M : ℕ) := base+12*page k M

def chart (base k H r M : ℕ) (fields : Fin 10→Bank) : Layout where
  field := fields
  joins i := ⟨⟨base,inputWidth k*M⟩,⟨base+(i.val+1)*page k M,(inputWidth k+(k+2))*M⟩⟩
  remap := ⟨⟨maskBase base k M+rows H r M,rowBits H r M⟩,
    ⟨base+11*page k M,inputWidth k*M⟩,⟨maskBase base k M,rowBits H r M⟩⟩

def output (base k H r M : ℕ) := maskBase base k M+2*rows H r M

theorem row_bounds (H r M : ℕ) :
    H*chunks r M≤rows H r M ∧ rows H r M≤2*(H*chunks r M+1) := by
  let n:=H*chunks r M
  change n≤2^(Nat.clog 2 (n+1)) ∧ 2^(Nat.clog 2 (n+1))≤2*(n+1)
  refine ⟨(Nat.le_succ n).trans (Nat.le_pow_clog (by decide) _),?_⟩
  cases e : Nat.clog 2 (n+1) with
  | zero=>simp;omega
  | succ t=>
    have positive : 1 < n+1 := by
      by_contra! h
      have zero : n=0 := by omega
      rw [zero] at e
      change 0=t+1 at e
      omega
    have lt:=Nat.pow_pred_clog_lt_self (b:=2) (by decide) positive
    rw [e] at lt
    change 2^t<n+1 at lt
    rw [pow_succ]
    omega

private theorem joined (k : ℕ) : inputWidth k+(k+2)=unit k := by unfold inputWidth unit;omega

private theorem short (k M : ℕ) : 2^(inputWidth k*M)≤page k M := by
  apply Nat.pow_le_pow_right (by decide)
  exact Nat.mul_le_mul_right M (by unfold inputWidth unit;omega)

theorem room (base k H r M w : ℕ) (fields : Fin 10→Bank)
    (up : ∀i,(fields i).Fits w base) (cap : ∀i,H*chunks r M≤(fields i).size)
    (word : M*unit k≤w/2) (space : maskBase base k M+3*rows H r M<2^w) :
    Room (chart base k H r M fields) k H r M w (output base k H r M) := by
  let P:=page k M
  let R:=rows H r M
  change base+12*P+3*R<2^w at space
  have rcap : H*chunks r M≤R:=(row_bounds H r M).1
  have small : 2^(inputWidth k*M)≤P:=short k M
  have ppos : 0<P:=Nat.two_pow_pos _
  have rpos : 0<R:=Nat.two_pow_pos _
  have packed : M*max (inputWidth k) (outputWidth k)≤w/2 :=
    (Nat.mul_le_mul_left M (max_le (by unfold inputWidth unit;omega) (by unfold outputWidth unit;omega))).trans word
  have bank {lo bits stop : ℕ} (size : 2^bits<2^w) (before : lo+2^bits≤ stop) :
      (⟨lo,bits⟩:Bank).Fits w stop:=⟨Nat.two_pow_pos _,size,before⟩
  refine ⟨?_,cap,?_,?_⟩
  · intro i
    have slot:=Nat.mul_le_mul_right P (show i.val+1≤10 by omega)
    obtain ⟨pos,fit,below⟩:=up i
    refine ⟨⟨⟨pos,fit,?_⟩,trivial⟩,bank (by omega) ?_,bank ?_ ?_,rfl,rfl⟩
    · change (fields i).base+(fields i).size≤base+12*P+R
      omega
    · change base+2^(inputWidth k*M)≤base+12*P+R
      omega
    · rw [joined];change P<2^w;omega
    · change base+(i.val+1)*P+2^((inputWidth k+(k+2))*M)≤base+12*P+R
      rw [joined];change base+(i.val+1)*P+P≤base+12*P+R;omega
  · refine ⟨bank (by change R<2^w;omega) (by change base+12*P+R+R≤base+12*P+2*R;omega),
      bank (by omega) (by change base+11*P+2^(inputWidth k*M)≤base+12*P+2*R;omega),
      bank (by change R<2^w;omega) (by change base+12*P+R≤base+12*P+2*R;omega),
      rcap,rfl,rcap,?_,packed⟩
    change base+12*P+2*R+H*chunks r M<2^w
    omega
  · rintro (i|i)
    · change base+11*P+i.val<base+12*P+R
      have := i.isLt
      omega
    · change base+12*P+i.val<base+12*P+R
      exact Nat.add_lt_add_left (i.isLt.trans_le rcap) _

/-- Data for each of the twelve public dictionary pages. Each page has the same
address pitch; an unused high input to a shorter table receives zero. -/
def literal (k M q j : ℕ) : ℕ :=
  if q=0 then 2^((k+2)*M)*j
  else if i : q-1<10 then
    if h:j<2^((inputWidth k+(k+2))*M) then
      (DescentPackedZip.table (M:=M) (Gather.setField (d:=k+2) (⟨q-1,i⟩:Fin 10)) ⟨j,h⟩).val else 0
  else if h:j<2^(inputWidth k*M) then (DescentSIMDLookup.table (M:=M) (transition k) ⟨j,h⟩).val else 0

def contents (k H r M x : ℕ) :=
  let P:=page k M
  if x<12*P then literal k M (x/P) (x%P)
  else if h:x-12*P<H*chunks r M then
    maskWord (outputWidth k) M r ((row H r M).symm ⟨x-12*P,h⟩).2.val else 0

private theorem page_read (k H r M q j : ℕ) (pageNo : q<12) (cell : j<page k M) :
    contents k H r M (q*page k M+j)=literal k M q j := by
  have below:=Nat.mul_le_mul_right (page k M) (Nat.succ_le_of_lt pageNo)
  rw [Nat.succ_mul] at below
  have div : (q*page k M+j)/page k M=q := by
    rw [Nat.mul_comm q (page k M),Nat.mul_add_div (Nat.zero_lt_of_lt cell),Nat.div_eq_of_lt cell,Nat.add_zero]
  simp [contents,show q*page k M+j<12*page k M by omega,div,Nat.mul_add_mod_of_lt cell]

def mount (base k H r M w : ℕ) :=
  DescentStaticWordColumn.program w base (contents k H r M) (12*page k M+H*chunks r M)

def mounted (base k H r M : ℕ) {w : ℕ} (m : Memory w) :=
  DescentStaticWordColumn.image base (contents k H r M) m (12*page k M+H*chunks r M)

theorem installed (base k H r M w : ℕ) (fields : Fin 10→Bank) (x : Fin H→Fin r→Fragment k)
    (up : ∀i,(fields i).Fits w base) (cap : ∀i,H*chunks r M≤(fields i).size)
    (m : Memory w) (src : ∀i (p : Row H r M),m ((fields i).base+(row H r M p).val)=
      ((data (fun v t=>sourceFields (x v t) i) p).val:ℕ))
    (space : maskBase base k M+3*rows H r M<2^w) :
    (mount base k H r M w).Exec m (mounted base k H r M m) (4+10*(12*page k M+H*chunks r M)) ∧
      Installed (chart base k H r M fields) x M (mounted base k H r M m) := by
  have bounds:=(row_bounds H r M).1
  have read (q j : ℕ) (hq : q<12) (hj : j<page k M) :
      mounted base k H r M m (base+q*page k M+j)=(literal k M q j:Word w) := by
    rw [Nat.add_assoc]
    have ord:=Nat.mul_le_mul_right (page k M) (Nat.succ_le_of_lt hq)
    rw [Nat.succ_mul] at ord
    exact (DescentStaticWordColumn.read base _ _ m (by omega)).trans
      (congrArg (fun z : ℕ=>(z:Word w)) (page_read k H r M q j hq hj))
  refine ⟨DescentStaticWordColumn.mount _ _ _ _ (by unfold maskBase at space;omega),?_,?_,?_⟩
  · intro i p
    apply Eq.trans (DescentStaticWordColumn.frame ..) (src i p)
    apply Or.inl
    exact (Nat.add_lt_add_left ((row H r M p).isLt.trans_le (cap i)) _).trans_le (up i).2.2
  · intro i
    constructor
    · intro j
      simpa [chart,literal] using read 0 j.val (by decide) (j.isLt.trans_le (short k M))
    · intro j
      have encoded : j.val<2^((inputWidth k+(k+2))*M) := by
        simpa only [inputWidth] using j.isLt
      have jlt : j.val<page k M := by simpa only [page, ←joined] using encoded
      simpa [chart, literal, encoded] using read (i.val+1) j.val (by omega) jlt
  · rintro (j|j)
    · simpa [fixedAddr,fixedWord,chart,literal,j.isLt] using
        read 11 j.val (by decide) (j.isLt.trans_le (short k M))
    · change mounted base k H r M m (base+12*page k M+j.val)=(maskWord _ _ _ _:Word w)
      rw [Nat.add_assoc, mounted,DescentStaticWordColumn.read _ _ _ _ (Nat.add_lt_add_left j.isLt _)]
      simp [contents,j.isLt]

private theorem public_cheap (w base : ℕ) (data : ℕ→ℕ) (n : ℕ) :
    CheapCode (DescentStaticWordColumn.program w base data n) := by
  induction n with
  | zero=>exact @scan_cheap _ _ _ _
  | succ n ih=>exact cheap_seq ih (@scan_cheap _ _ _ _)

def run (base k H r M w : ℕ) (fields : Fin 10→Bank) :=
  (mount base k H r M w).seq (routed (chart base k H r M fields) (output base k H r M) H r M w)

private abbrev Verified {w : ℕ} (P : Procedure w) (m : Memory w)
    (post : Memory w → Prop) (ticks : ℕ) : Prop :=
  P.Spec (·=m) (fun _ done => post done) ticks ∧ CheapCode P

private theorem prepend {w : ℕ} (A B : Procedure w) (m mid : Memory w)
    (post : Memory w → Prop) (a b budget : ℕ) (runA : A.Exec m mid a)
    (cheapA : CheapCode A) (next : Verified B mid post b) (bound : a+b≤budget) :
    Verified (A.seq B) m post budget := by
  obtain ⟨runB, cheapB⟩ := next
  refine ⟨?_, cheap_seq (A:=A) (B:=B) cheapA cheapB⟩
  exact Procedure.Spec.mono (A:=A.seq B)
    (Procedure.Spec.seq (A:=A) (B:=B) runA runB (fun _ _ h => h))
    (fun _ h => h) (fun _ _ ⟨_, _, h⟩ => h) bound

set_option maxHeartbeats 600000 in
/-- All fixed shift and transition tables execute their literal stores before the
two packed scans. Only the ten genuine preceding columns are read from the input. -/
theorem execute (base k H r M w : ℕ) (fields : Fin 10→Bank) (x : Fin H→Fin r→Fragment k)
    (up : ∀i,(fields i).Fits w base) (cap : ∀i,H*chunks r M≤(fields i).size)
    (word : M*unit k≤w/2) (positive : 0<M)
    (space : maskBase base k M+3*rows H r M<2^w)
    (m : Memory w) (src : ∀i (p : Row H r M),m ((fields i).base+(row H r M p).val)=
      ((data (fun v t=>sourceFields (x v t) i) p).val:ℕ)) :
    Verified (run base k H r M w fields) m (fun done=>∀v j (f : Fin 5),
      digit (k+4) f.val (digit (outputWidth k) (lane j positive).val
        (done (output base k H r M+(row H r M (position v j positive)).val)).val)=(resolve (x v j)).fields f)
      (12+120*page k M+420*(H*chunks r M)) := by
  let L := chart base k H r M fields
  let out := output base k H r M
  let post := fun (done : Memory w) => ∀ (v : Fin H) (j : Fin r) (f : Fin 5),
    digit (k+4) f.val (digit (outputWidth k) (lane j positive).val
      (done (out+(row H r M (position v j positive)).val)).val)=(resolve (x v j)).fields f
  obtain ⟨mountedRun, load⟩ := installed base k H r M w fields x up cap m src space
  have tail : Verified (routed L out H r M w) (mounted base k H r M m) post (8+410*(H*chunks r M)) :=
    routed_spec L out (room base k H r M w fields up cap word space) x positive (mounted base k H r M m) load
  exact prepend (mount base k H r M w) (routed L out H r M w) m (mounted base k H r M m)
    post (4+10*(12*page k M+H*chunks r M)) (8+410*(H*chunks r M))
    (12+120*page k M+420*(H*chunks r M)) @mountedRun
    (@public_cheap w base (contents k H r M) (12*page k M+H*chunks r M)) tail (by omega)

theorem price (k w H r : ℕ) (wide : 2*unit k≤w) :
    let M:=lanes w (unit k)
    (12+120*page k M+420*(H*chunks r M))*w≤
      (12+120*2^(w/2))*w+420*(H*w+4*H*r*unit k) ∧
    12*page k M+3*rows H r M≤12*2^(w/2)+6*(H*chunks r M+1) := by
  let M:=lanes w (unit k)
  have pos : 0 < unit k:=by unfold unit;omega
  have v:=volume H r w (unit k) pos wide
  have room:=lanes_fit w (unit k)
  have high : page k M≤2^(w/2):=Nat.pow_le_pow_right (by decide) (by simpa [M,Nat.mul_comm] using room)
  have rcap:=(row_bounds H r M).2
  dsimp only
  constructor
  · nlinarith only [Nat.mul_le_mul_right w high,Nat.mul_le_mul_left 420 v]
  · change 12*page k M+3*rows H r M≤12*2^(w/2)+6*(H*chunks r M+1)
    omega

/-- The installed block, including the literal-store instructions, also fits
the shared ROM allowance in number of labels, registers and public slots. -/
theorem control (base k H r M w : ℕ) (fields : Fin 10→Bank) :
    let P:=run base k H r M w fields
    P.labels+P.registers+P.slots=841+15*(12*page k M+H*chunks r M) := by
  change DescentStaticWordColumn.names _=_
  simp only [run,DescentStaticWordColumn.names_seq,mount,DescentStaticWordColumn.names_mount,routed,prepare,DescentSIMDLookup.program,
    DescentStaticWordColumn.names_scan,panel_work,lookup_work]
  omega

end
end Hierarchy.DescentPackedOperand.ROM

end OAI
