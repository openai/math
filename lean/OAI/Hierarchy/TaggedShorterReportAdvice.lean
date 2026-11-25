import OAI.Hierarchy.TaggedShorterReportedPublish
import OAI.Hierarchy.TaggedShorterSlotWidthNative

namespace OAI
/-! # Selector-independent advice for the final sparse RAM publisher -/

noncomputable section
namespace Hierarchy.TaggedShorterReportAdvice
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat Routing CallPool RAM RAM.DescriptorExpr
open ProtocolRAM TaggedShorterEmitMachine TaggedShorterReportedPublish TaggedShorterGroups
open scoped Classical Fin.CommRing

variable {W : ℕ}

/-- Thirteen banks occupy consecutive equal-sized regions. Columns 0, 1 and 2
unpack the ten words for each potential slot; the other banks hold arithmetic
lookups or the five public base pointers of each reserved candidate. -/
def bank (base bits : ℕ) (j : Fin 13) : Bank := ⟨base+j.val*2^bits,bits⟩

def store (base bits : ℕ) (word : Fin 13 → ℕ → Word W) (m : Memory W) : Memory W :=
  fillSegment base (13*2^bits) (fun a =>
    if h : (a-base)/2^bits<13 then word ⟨_,h⟩ ((a-base)%2^bits) else 0) m

theorem read_store (base bits : ℕ) (word : Fin 13 → ℕ → Word W) (m : Memory W)
    (j : Fin 13) (i : ℕ) (cap : i<2^bits) (wide : i<2^W) :
    (bank base bits j).read (store base bits word m) (i:Word W)=word j i := by
  let p := 2^bits
  have pos : 0<p := Nat.two_pow_pos _
  have less : j.val*p+i<13*p := by
    have h := Nat.mul_le_mul_right p j.isLt
    rw [Nat.succ_mul] at h
    omega
  have div : (j.val*p+i)/p=j.val := by
    rw [Nat.mul_comm j.val p,Nat.mul_add_div pos,Nat.div_eq_of_lt cap,Nat.add_zero]
  have rem : (j.val*p+i)%p=i := Nat.mul_add_mod_of_lt cap
  change store base bits word m (base+j.val*p+(i:Word W).val%p)=word j i
  rw [Fin.val_cast_of_lt wide,Nat.mod_eq_of_lt cap]
  have inside : base≤base+j.val*p+i ∧ base+j.val*p+i<base+13*p := by omega
  have idx : base+j.val*p+i-base=j.val*p+i := by omega
  change (if base≤base+j.val*p+i ∧ base+j.val*p+i<base+13*p then
    (if h : (base+j.val*p+i-base)/p<13 then word ⟨_,h⟩ ((base+j.val*p+i-base)%p) else 0)
    else m (base+j.val*p+i))=_
  simp only [ite_eq_left inside,idx,div,rem,dite_eq_left j.isLt]

def pointer (groups D B M base : ℕ) (j : Fin 5) (a : ℕ) : Word W :=
  let len := poolBatchCount D B
  if h : a/len<groups ∧ a%len<len then
    bases (capacity (Fin groups) D B M) D base
      (board (Fin groups) D B M ⟨⟨a/len,h.1⟩,⟨a%len,h.2⟩⟩) j
  else 0

theorem pointer_read (groups D B M base : ℕ) (g : Fin groups)
    (k : Fin (poolBatchCount D B)) (j : Fin 5) :
    pointer (W:=W) groups D B M base j (g.val*poolBatchCount D B+k.val)=
      (bases (capacity (Fin groups) D B M) D base (board (Fin groups) D B M ⟨g,k⟩)) j := by
  let len := poolBatchCount D B
  have pos : 0<len := (Nat.zero_le _).trans_lt k.isLt
  have q : (g.val*len+k.val)/len=g.val := by
    rw [Nat.mul_comm g.val len,Nat.mul_add_div pos,Nat.div_eq_of_lt k.isLt,Nat.add_zero]
  have r : (g.val*len+k.val)%len=k.val := Nat.mul_add_mod_of_lt k.isLt
  have hk : k.val<len := k.isLt
  simp [pointer,←show len=poolBatchCount D B from rfl,q,r,g.isLt,hk]

def words (groups D B M base w m cap : ℕ) : Fin 13 → ℕ → Word W
  | 0,a => ((a/10/cap:ℕ):Word W)
  | 1,a => ((a/10%cap:ℕ):Word W)
  | 2,a => ((a%10:ℕ):Word W)
  | 3,a => (TaggedShorterBudget.widthIndex m (a/(w:ℝ)):Word W)
  | 4,a => (TaggedShorterBudget.copies (a/(w:ℝ)):Word W)
  | 5,a => ((a*poolBatchCount D B:ℕ):Word W)
  | 6,a => ((a/B:ℕ):Word W)
  | 7,a => ((a%B:ℕ):Word W)
  | 8,a => pointer groups D B M base 0 a
  | 9,a => pointer groups D B M base 1 a
  | 10,a => pointer groups D B M base 2 a
  | 11,a => pointer groups D B M base 3 a
  | 12,a => pointer groups D B M base 4 a

/-- The five remaining banks are the actual report/scan arrays, installed at the
addresses supplied by the preceding native phases. -/
def tables (rom bits : ℕ) (width group common left right : Bank) : Tables :=
  let b := bank rom bits
  ⟨b 0,b 1,b 2,width,group,b 3,b 4,common,left,right,b 5,b 6,b 7,
    fun j=>b (j.natAdd 8)⟩

/-- A contiguous thirteen-column public directory fits below the first write. -/
theorem banks_fit (rom bits floor : ℕ) (word : 2^bits<2^W)
    (before : rom+13*2^bits≤floor) (j : Fin 13) : (bank rom bits j).Fits W floor := by
  refine ⟨Nat.two_pow_pos _,word,?_⟩
  change rom+j.val*2^bits+2^bits≤floor
  have width := Nat.mul_le_mul_right (2^bits) j.isLt
  rw [Nat.succ_mul] at width
  omega

set_option maxHeartbeats 1600000 in
theorem term_fits (rom bits floor γ sink : ℕ) (width group common left right : Bank)
    (romSafe : ∀j,(bank rom bits j).Fits W floor)
    (hw : width.Fits W floor) (hg : group.Fits W floor) (hc : common.Fits W floor)
    (hl : left.Fits W floor) (hr : right.Fits W floor) :
    (TaggedShorterEmitMachine.term (tables rom bits width group common left right) γ sink).Fits W floor := by
  simp [TaggedShorterEmitMachine.term,TaggedShorterEmitMachine.select,chooseField,Expr.Fits,tables,
    romSafe,hw,hg,hc,hl,hr]

set_option maxHeartbeats 800000 in
theorem width_term_fits (rom bits floor D γ sink : ℕ) (width group common left right origins : Bank)
    (romSafe : ∀j,(bank rom bits j).Fits W floor)
    (hw : width.Fits W floor) (hg : group.Fits W floor) (_hc : common.Fits W floor)
    (hl : left.Fits W floor) (hr : right.Fits W floor) (ho : origins.Fits W floor) :
    (TaggedShorterSlotWidth.term (tables rom bits width group common left right) origins D γ sink).Fits W floor := by
  simp [TaggedShorterSlotWidth.term,TaggedShorterEmitMachine.select,Expr.Fits,tables,
    romSafe,hw,hg,hl,hr,ho]

theorem directory_of_reads (groups D B M base w m cap rom bits : ℕ) (mem : Memory W)
    (width group common left right : Bank)
    (gFit : groups≤2^bits) (dFit : D≤2^bits) (mapFit : groups*poolBatchCount D B≤2^bits)
    (read : ∀ (j : Fin 13) (i : ℕ),i<2^bits → (bank rom bits j).read mem (i:Word W) =
      words groups D B M base w m cap j i) :
    let A := tables rom bits width group common left right
    Directory A mem base groups D B M := by
  intro A
  refine ⟨fun g=>read 5 g.val (g.isLt.trans_le gFit),fun r=>read 6 r.val (r.isLt.trans_le dFit),
    fun r=>read 7 r.val (r.isLt.trans_le dFit),?_⟩
  intro g k j
  let q := poolBatchCount D B
  have h : g.val*q+k.val<2^bits := by
    have ht := Nat.mul_le_mul_right q g.isLt
    rw [Nat.succ_mul] at ht
    have hk : k.val<q:=k.isLt
    change groups*q≤2^bits at mapFit
    omega
  have r := read (j.natAdd 8) (g.val*q+k.val) h
  change (bank rom bits (j.natAdd 8)).read mem _=_
  refine r.trans ?_
  fin_cases j <;> exact pointer_read groups D B M base g k _

theorem directory (groups D B M base w m cap rom bits : ℕ) (source : Memory W)
    (width group common left right : Bank)
    (gFit : groups≤2^bits) (dFit : D≤2^bits) (mapFit : groups*poolBatchCount D B≤2^bits)
    (wide : 2^bits≤2^W) :
    let A := tables rom bits width group common left right
    let pub := store rom bits (words groups D B M base w m cap) source
    Directory A pub base groups D B M := by
  apply directory_of_reads _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gFit dFit mapFit
  intro j x h
  exact read_store _ _ _ _ j x h (h.trans_le wide)

private theorem div_part (a b c : ℕ) (h : c<b) : (a*b+c)/b=a := by
  rw [Nat.mul_comm a b,Nat.mul_add_div (Nat.zero_lt_of_lt h),Nat.div_eq_of_lt h,Nat.add_zero]

/-- The flattened static word directory maps the two words in each effect, and all five
effects in a slot, back to their original report row without arithmetic opcodes. -/
theorem ordinal {N cap W : ℕ} (s : Fin (N*cap)) (j : Fin 5) (k : Fin 2)
    (fits : 10*(N*cap)≤2^W) :
    (atWord (W:=W) s j k).val/10/cap=(finProdFinEquiv.symm s).1.val ∧
    (atWord (W:=W) s j k).val/10%cap=(finProdFinEquiv.symm s).2.val ∧
    (atWord (W:=W) s j k).val%10=(finProdFinEquiv (j,k)).val ∧
    (BinaryOp.bitAnd.eval (atWord (W:=W) s j k) 1).val=k.val := by
  obtain ⟨⟨i,z⟩,rfl⟩ := finProdFinEquiv.surjective s
  let s := finProdFinEquiv (i,z)
  let t := finProdFinEquiv (j,k)
  have a : s.val=i.val*cap+z.val := by simp [s,finProdFinEquiv_apply_val];ring
  have tAt : t.val=2*j.val+k.val := by
    change k.val+2*j.val=2*j.val+k.val
    omega
  have low : 2*(finProdFinEquiv (s,j)).val+k.val=s.val*10+t.val := by
    change 2*(j.val+5*s.val)+k.val=s.val*10+t.val
    rw [tAt]
    omega
  have lt : s.val*10+t.val<2^W := by
    have := s.isLt
    have := t.isLt
    omega
  have addr : (atWord (W:=W) s j k).val=s.val*10+t.val := by
    change ((2*(finProdFinEquiv (s,j)).val+k.val:ℕ):Word W).val=_
    rw [low,Fin.val_cast_of_lt lt]
  have parity : (s.val*10+t.val)%2=k.val := by rw [tAt];omega
  have wide : 1<2^W := by
    have := s.isLt
    omega
  have andOne (x : ℕ) : x &&& 1=x%2 := Nat.and_two_pow_sub_one_eq_mod x 1
  simp only [Equiv.symm_apply_apply]
  refine ⟨?_,?_,?_,?_⟩
  · rw [addr,div_part _ _ _ t.isLt,a,div_part _ _ _ z.isLt]
  · rw [addr,div_part _ _ _ t.isLt,a,Nat.mul_add_mod_of_lt z.isLt]
  · rw [addr,Nat.mul_add_mod_of_lt t.isLt]
  · change ((↑((atWord (W:=W) s j k).val &&& (1:Word W).val) : Word W)).val=_
    rw [Fin.val_one',Nat.mod_eq_of_lt wide,andOne,addr,parity,Fin.val_cast_of_lt (k.isLt.trans_le wide)]

/-- The only five dynamic banks used by the final emission program. -/
structure Dynamic {N : ℕ} (rows : Fin N → ProtocolRAMEmit.Row) (m : Memory W)
    (width group common left right : Bank) (cr : Fin N → ℕ) (lr : Bool → Fin N → ℕ) : Prop where
  widthAt : ∀i : Fin N, width.read m ((3*i.val:ℕ):Word W)=((rows i).width:Word W)
  groupAt : ∀i : Fin N, group.read m ((3*i.val:ℕ):Word W)=((rows i).group:Word W)
  commonAt : ∀i : Fin N,common.read m ((4*i.val:ℕ):Word W)=(cr i:Word W)
  leftAt : ∀i : Fin N,left.read m (i.val:Word W)=(lr false i:Word W)
  rightAt : ∀i : Fin N,right.read m (i.val:Word W)=(lr true i:Word W)

/-- Read the true dynamic arrays and the fixed public board data from the same memory.
The public reads are preserved by the preceding native passes' memory frames. -/
theorem source {N groups D B M base w menu cap rom bits : ℕ}
    (m : Memory W) (rows : Fin N→ProtocolRAMEmit.Row) (width group common left right : Bank)
    (cr : Fin N → ℕ) (lr : Bool → Fin N→ℕ) (dynamic : Dynamic rows m width group common left right cr lr)
    (pub : ∀ j : Fin 13,∀ x : ℕ,x<2^bits →
      (bank rom bits j).read m (x:Word W)=words groups D B M base w menu cap j x)
    (tapeFits : 10*(N*cap)≤2^bits) (widthFit : ∀i,(rows i).width<2^bits) (room : 2^bits≤2^W)
    (mFit : menu<2^W) (piecesFit : ∀ i,ProtocolRAMReportedPorts.pieces rows w i<2^W)
    (s : Fin (N*cap)) (j : Fin 5) (k : Fin 2) :
    let t := finProdFinEquiv (j,k)
    let i := (finProdFinEquiv.symm s).1
    let z := (finProdFinEquiv.symm s).2
    Source (tables rom bits width group common left right) m (atWord s j k)
      i.val z.val t.val (rows i).width (rows i).group
      (TaggedShorterBudget.widthIndex menu ((rows i).width/(w:ℝ)))
      (ProtocolRAMReportedPorts.pieces rows w i) (cr i) (lr false i) (lr true i) := by
  intro t i z
  let a := atWord (W:=W) s j k
  obtain ⟨owner,part,col,_⟩:=ordinal s j k (tapeFits.trans room)
  have maxA : a.val<2^bits := by
    have h := (finProdFinEquiv (s,j)).isLt
    have hk := k.isLt
    have fits : 2*(finProdFinEquiv (s,j)).val+k.val<2^bits := by omega
    change ((2*(finProdFinEquiv (s,j)).val+k.val : ℕ):Word W).val<_
    rw [Fin.val_cast_of_lt (fits.trans_le room)]
    exact fits
  have get (b : Fin 13) : (bank rom bits b).read m a=words groups D B M base w menu cap b a.val := by
    simpa using pub b a.val maxA
  have classFit : TaggedShorterBudget.widthIndex menu ((rows i).width/(w:ℝ))<2^W :=
    (TaggedShorterBudget.widthIndex_spec menu).1.trans_lt mFit
  have smallCol : t.val<2^W := by
    have := s.isLt
    have := t.isLt
    omega
  exact ⟨(get 0).trans (congrArg (fun x : ℕ=>(x:Word W)) owner),
    (get 1).trans (congrArg (fun x : ℕ=>(x:Word W)) part),
    by rw [show (tables rom bits width group common left right).column=bank rom bits 2 from rfl,get 2]
       change ((a.val%10:ℕ):Word W).val=t.val
       rw [col,Fin.val_cast_of_lt smallCol],
    dynamic.widthAt i,dynamic.groupAt i,
    by rw [show (tables rom bits width group common left right).widthClass=bank rom bits 3 from rfl,
        pub 3 _ (widthFit i),show words (W:=W) groups D B M base w menu cap 3 (rows i).width =
          (TaggedShorterBudget.widthIndex menu ((rows i).width/(w:ℝ)):Word W) from rfl,
        Fin.val_cast_of_lt classFit],
    by rw [show (tables rom bits width group common left right).widthPieces=bank rom bits 4 from rfl,
        pub 4 _ (widthFit i),show words (W:=W) groups D B M base w menu cap 4 (rows i).width =
          (ProtocolRAMReportedPorts.pieces rows w i:Word W) from rfl,Fin.val_cast_of_lt (piecesFit i)],
    dynamic.commonAt i,dynamic.leftAt i,dynamic.rightAt i⟩

theorem pieces_capacity {N cap w : ℕ} (rows : Fin N→ProtocolRAMEmit.Row) (hw : 0<w)
    (bound : ∀i,(rows i).width≤cap*w) (i : Fin N) : ProtocolRAMReportedPorts.pieces rows w i≤cap := by
  change ⌈((rows i).width:ℝ)/(w:ℝ)⌉₊≤cap
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ (by exact_mod_cast hw : (0:ℝ)<w)).mpr
  exact_mod_cast bound i

/-- The metric-width and group reads have the offsets of the original emitted triples.
The rank buffers remain the numerical outputs of the three weighted scans. -/
theorem dynamic_of_report {N dst bits : ℕ} (rows : Fin N→ProtocolRAMEmit.Row)
    (prior mem : Memory W) (common left right : Bank) (cr : Fin N→ℕ) (lr : Bool→Fin N→ℕ)
    (cap : 3*N≤2^bits) (wide : 2^bits≤2^W)
    (metric : ∀i : Fin N,mem (dst+3*N+3*i.val+1)=
        ProtocolRAMEmit.emitted dst rows prior (dst+3*N+3*i.val+1))
    (gate : ∀i : Fin N,mem (dst+6*N+3*i.val)=
        ProtocolRAMEmit.emitted dst rows prior (dst+6*N+3*i.val))
    (commonAt : ∀i : Fin N,common.read mem ((4*i.val:ℕ):Word W)=(cr i:Word W))
    (leftAt : ∀i : Fin N,left.read mem (i.val:Word W)=(lr false i:Word W))
    (rightAt : ∀i : Fin N,right.read mem (i.val:Word W)=(lr true i:Word W)) :
    Dynamic rows mem ⟨dst+3*N+1,bits⟩ ⟨dst+6*N,bits⟩ common left right cr lr := by
  have atIndex (i : Fin N) (base : ℕ) : (Bank.mk base bits).read mem ((3*i.val:ℕ):Word W)=mem (base+3*i.val) := by
    have sm : 3*i.val<2^bits := by have := i.isLt;omega
    change mem (base+((3*i.val:ℕ):Word W).val%(2^bits))=_
    rw [Fin.val_cast_of_lt (sm.trans_le wide),Nat.mod_eq_of_lt sm]
  refine ⟨?_,?_,commonAt,leftAt,rightAt⟩
  · intro i
    rw [atIndex,show dst+3*N+1+3*i.val=dst+3*N+3*i.val+1 by omega,metric i]
    exact (ProtocolRAMEmit.emitted_read dst rows prior i 1).2.1
  · intro i
    rw [atIndex,gate i]
    have rowWord := (ProtocolRAMEmit.emitted_read dst rows prior i 0).2.2
    change _=(((rows i).group:ℕ):Word W) at rowWord
    simpa only [Fin.val_zero,Nat.add_zero] using rowWord

/-- End-to-end publication on the actual reported rows. External data consist only
of the physical report and numeric prefix outputs, plus the fixed thirteen advice
tables. No selector-dependent mask or identifier word is supplied. -/
theorem publish_report_at_framed_stored_live {N groups D B M n w menu cap rom bits base src sink γ : ℕ}
    (mem : Memory W) (rows : Fin N→ProtocolRAMEmit.Row)
    (width group common left right : Bank) (cr : Fin N→ℕ) (lr : Bool→Fin N→ℕ)
    (dynamic : Dynamic rows mem width group common left right cr lr)
    (read : ∀ j : Fin 13,∀ x : ℕ,x<2^bits → (bank rom bits j).read mem (x:Word W)=
      words groups D B M base w menu cap j x)
    (gFit : ∀i,0<ProtocolRAMReportedPorts.pieces rows w i → (rows i).group<groups) (distinct : Function.Injective fun i=>(rows i).link)
    (bound : ∀g : Fin groups,size rows w menu γ g≤D)
    (copied : ∀i,ProtocolRAMReportedPorts.pieces rows w i≤cap)
    (cn : ∀ (g : Fin groups) (i : ProtocolRAMReportedPorts.InGroup rows w menu γ g.val),cr i.val =
      ProtocolRAMPortRanks.«prefix» (ProtocolRAMReportedPorts.slotCount rows w menu γ g.val)
        (fun j=>(rows j.val).link) i)
    (pl : ∀g : Fin groups,Bool → Fin (size rows w menu γ g) ↪ Fin D)
    (located : ∀ b (g : Fin groups) (u : ProtocolRAMReportedPorts.Unit rows w menu γ g.val),
      (pl g b (ProtocolRAMReportedPorts.common rows w menu γ g.val distinct u)).val=
        lr b u.1.val+u.2.val)
    (groupCap : groups≤2^bits) (boundCap : D≤2^bits) (mapCap : groups*poolBatchCount D B≤2^bits)
    (tableCap : 10*(N*cap)≤2^bits) (widthFit : ∀i,(rows i).width<2^bits) (wide : 2^bits≤2^W)
    (menuFits : menu<2^W) (typeFits : γ ≤ menu) (small : 10≤2^W) (slotFits : cap<2^W)
    (hb : 0<B) (hw : B≤2^n) (batchFits : B≤2^W)
    (layoutFit : let C := capacity (Fin groups) D B M; base+(C+2*(C*2*D))≤2^W)
    (ordered : let C := capacity (Fin groups) D B M; base+(C+2*(C*2*D))≤ src)
    (room : src+10*(N*cap)<2^W) (sinkLow : sink<src)
    (apart : ∀ f, (sink:Word W)≠TaggedShorterScatter.layout (capacity (Fin groups) D B M) D base layoutFit f)
    (input : (term (tables rom bits width group common left right) γ sink).Fits W src)
    (low : (term (tables rom bits width group common left right) γ sink).Fits W base) :
    let A := tables rom bits width group common left right
    let C := capacity (Fin groups) D B M
    let total := C+2*(C*2*D)
    let c := size (groups:=groups) rows w menu γ
    let addr := TaggedShorterScatter.layout C D base layoutFit
    ∃ out, (clearedProcedure W base total src (N*cap) γ sink A).Exec mem out
      ((4+6*total)+(8+16230*(N*cap))) ∧
      (∀ a, a<base → a≠sink → out a=mem a) ∧
      ∀ f, out (addr f).val=(TaggedShorterScatter.contents c bound hb hw pl f : Word W) := by
  intro A C total c addr
  let choose := selectedLive rows w menu γ cap gFit distinct
  have covers := selectedLive_covers rows w menu γ cap gFit distinct copied
  have dir := directory_of_reads groups D B M base w menu cap rom bits mem width group common left right
    groupCap boundCap mapCap read
  apply publish_cleared_framed_stored c bound hb hw pl A γ src sink base choose mem layoutFit covers input low room
    ordered sinkLow apart (by omega) batchFits
  intro s j k
  have fields := source mem rows width group common left right cr lr dynamic read tableCap widthFit wide
    menuFits (fun i=>(copied i).trans_lt slotFits) s j k
  have parity := (ordinal (W:=W) s j k (tableCap.trans wide)).2.2.2
  exact selected_words_at_live A mem rows w menu γ cap sink base gFit distinct bound hb layoutFit dir small
    (typeFits.trans_lt menuFits) slotFits.le cr lr cn pl located s j k fields parity

theorem publish_report_at_framed_live {N groups D B M n w menu cap rom bits base src sink γ : ℕ}
    (mem : Memory W) (rows : Fin N→ProtocolRAMEmit.Row)
    (width group common left right : Bank) (cr : Fin N→ℕ) (lr : Bool→Fin N→ℕ)
    (dynamic : Dynamic rows mem width group common left right cr lr)
    (read : ∀ j : Fin 13,∀ x : ℕ,x<2^bits → (bank rom bits j).read mem (x:Word W)=
      words groups D B M base w menu cap j x)
    (gFit : ∀i,0<ProtocolRAMReportedPorts.pieces rows w i → (rows i).group<groups) (distinct : Function.Injective fun i=>(rows i).link)
    (bound : ∀g : Fin groups,size rows w menu γ g≤D)
    (copied : ∀i,ProtocolRAMReportedPorts.pieces rows w i≤cap)
    (cn : ∀ (g : Fin groups) (i : ProtocolRAMReportedPorts.InGroup rows w menu γ g.val),cr i.val =
      ProtocolRAMPortRanks.«prefix» (ProtocolRAMReportedPorts.slotCount rows w menu γ g.val)
        (fun j=>(rows j.val).link) i)
    (pl : ∀g : Fin groups,Bool → Fin (size rows w menu γ g) ↪ Fin D)
    (located : ∀ b (g : Fin groups) (u : ProtocolRAMReportedPorts.Unit rows w menu γ g.val),
      (pl g b (ProtocolRAMReportedPorts.common rows w menu γ g.val distinct u)).val=
        lr b u.1.val+u.2.val)
    (groupCap : groups≤2^bits) (boundCap : D≤2^bits) (mapCap : groups*poolBatchCount D B≤2^bits)
    (tableCap : 10*(N*cap)≤2^bits) (widthFit : ∀i,(rows i).width<2^bits) (wide : 2^bits≤2^W)
    (menuFits : menu<2^W) (typeFits : γ ≤ menu) (small : 10≤2^W) (slotFits : cap<2^W)
    (hb : 0<B) (hw : B≤2^n) (batchFits : B≤2^W)
    (layoutFit : let C := capacity (Fin groups) D B M; base+(C+2*(C*2*D))≤2^W)
    (ordered : let C := capacity (Fin groups) D B M; base+(C+2*(C*2*D))≤ src)
    (room : src+10*(N*cap)<2^W) (sinkLow : sink<src)
    (apart : ∀ f, (sink:Word W)≠TaggedShorterScatter.layout (capacity (Fin groups) D B M) D base layoutFit f)
    (input : (term (tables rom bits width group common left right) γ sink).Fits W src)
    (low : (term (tables rom bits width group common left right) γ sink).Fits W base) :
    let A := tables rom bits width group common left right
    let C := capacity (Fin groups) D B M
    let total := C+2*(C*2*D)
    let c := size (groups:=groups) rows w menu γ
    let addr := TaggedShorterScatter.layout C D base layoutFit
    ∃ out, (clearedProcedure W base total src (N*cap) γ sink A).Exec mem out
      ((4+6*total)+(8+16230*(N*cap))) ∧
      (∀ a, a<base → a≠sink → out a=mem a) ∧
      (∀ i,decide ((out (addr (.inl i)).val).val≠0)=groupOccupied c bound B M i) ∧
      (∀ sb x,decide ((out (addr (.inr (false,sb,x))).val).val≠0)=groupMask c bound B M pl sb x) ∧
      (∀ sb x,Computability.VPVNP.RAMSerialization.wordBits n (((out (addr (.inr (true,sb,x))).val).val:ℕ):Word n)=
        groupID c bound M hb hw pl sb x) := by
  intro A C total c addr
  obtain ⟨out,run,frame,stored⟩ := publish_report_at_framed_stored_live mem rows width group common left right
    cr lr dynamic read gFit distinct bound copied cn pl located groupCap boundCap mapCap tableCap widthFit wide
    menuFits typeFits small slotFits hb hw batchFits layoutFit ordered room sinkLow apart input low
  exact ⟨out,run,frame,TaggedShorterScatter.decode_words c bound hb hw pl addr out (by omega) batchFits stored⟩

theorem publish_report_at_framed {N groups D B M n w menu cap rom bits base src sink γ : ℕ}
    (mem : Memory W) (rows : Fin N→ProtocolRAMEmit.Row)
    (width group common left right : Bank) (cr : Fin N→ℕ) (lr : Bool→Fin N→ℕ)
    (dynamic : Dynamic rows mem width group common left right cr lr)
    (read : ∀ j : Fin 13,∀ x : ℕ,x<2^bits → (bank rom bits j).read mem (x:Word W)=
      words groups D B M base w menu cap j x)
    (gFit : ∀i,(rows i).group<groups) (distinct : Function.Injective fun i=>(rows i).link)
    (bound : ∀g : Fin groups,size rows w menu γ g≤D)
    (copied : ∀i,ProtocolRAMReportedPorts.pieces rows w i≤cap)
    (cn : ∀ (g : Fin groups) (i : ProtocolRAMReportedPorts.InGroup rows w menu γ g.val),cr i.val =
      ProtocolRAMPortRanks.«prefix» (ProtocolRAMReportedPorts.slotCount rows w menu γ g.val)
        (fun j=>(rows j.val).link) i)
    (pl : ∀g : Fin groups,Bool → Fin (size rows w menu γ g) ↪ Fin D)
    (located : ∀ b (g : Fin groups) (u : ProtocolRAMReportedPorts.Unit rows w menu γ g.val),
      (pl g b (ProtocolRAMReportedPorts.common rows w menu γ g.val distinct u)).val=
        lr b u.1.val+u.2.val)
    (groupCap : groups≤2^bits) (boundCap : D≤2^bits) (mapCap : groups*poolBatchCount D B≤2^bits)
    (tableCap : 10*(N*cap)≤2^bits) (widthFit : ∀i,(rows i).width<2^bits) (wide : 2^bits≤2^W)
    (menuFits : menu<2^W) (typeFits : γ ≤ menu) (small : 10≤2^W) (slotFits : cap<2^W)
    (hb : 0<B) (hw : B≤2^n) (batchFits : B≤2^W)
    (layoutFit : let C := capacity (Fin groups) D B M; base+(C+2*(C*2*D))≤2^W)
    (ordered : let C := capacity (Fin groups) D B M; base+(C+2*(C*2*D))≤ src)
    (room : src+10*(N*cap)<2^W) (sinkLow : sink<src)
    (apart : ∀ f, (sink:Word W)≠TaggedShorterScatter.layout (capacity (Fin groups) D B M) D base layoutFit f)
    (input : (term (tables rom bits width group common left right) γ sink).Fits W src)
    (low : (term (tables rom bits width group common left right) γ sink).Fits W base) :
    let A := tables rom bits width group common left right
    let C := capacity (Fin groups) D B M
    let total := C+2*(C*2*D)
    let c := size (groups:=groups) rows w menu γ
    let addr := TaggedShorterScatter.layout C D base layoutFit
    ∃ out, (clearedProcedure W base total src (N*cap) γ sink A).Exec mem out
      ((4+6*total)+(8+16230*(N*cap))) ∧
      (∀ a, a<base → a≠sink → out a=mem a) ∧
      (∀ i,decide ((out (addr (.inl i)).val).val≠0)=groupOccupied c bound B M i) ∧
      (∀ sb x,decide ((out (addr (.inr (false,sb,x))).val).val≠0)=groupMask c bound B M pl sb x) ∧
      (∀ sb x,Computability.VPVNP.RAMSerialization.wordBits n (((out (addr (.inr (true,sb,x))).val).val:ℕ):Word n)=
        groupID c bound M hb hw pl sb x) :=
  publish_report_at_framed_live mem rows width group common left right cr lr dynamic read
    (fun i _=>gFit i) distinct bound copied cn pl located groupCap boundCap mapCap tableCap widthFit wide
    menuFits typeFits small slotFits hb hw batchFits layoutFit ordered room sinkLow apart input low

theorem publish_report_at {N groups D B M n w menu cap rom bits base src sink γ : ℕ}
    (mem : Memory W) (rows : Fin N→ProtocolRAMEmit.Row)
    (width group common left right : Bank) (cr : Fin N→ℕ) (lr : Bool→Fin N→ℕ)
    (dynamic : Dynamic rows mem width group common left right cr lr)
    (read : ∀ j : Fin 13,∀ x : ℕ,x<2^bits → (bank rom bits j).read mem (x:Word W)=
      words groups D B M base w menu cap j x)
    (gFit : ∀i,(rows i).group<groups) (distinct : Function.Injective fun i=>(rows i).link)
    (bound : ∀g : Fin groups,size rows w menu γ g≤D)
    (copied : ∀i,ProtocolRAMReportedPorts.pieces rows w i≤cap)
    (cn : ∀ (g : Fin groups) (i : ProtocolRAMReportedPorts.InGroup rows w menu γ g.val),cr i.val =
      ProtocolRAMPortRanks.«prefix» (ProtocolRAMReportedPorts.slotCount rows w menu γ g.val)
        (fun j=>(rows j.val).link) i)
    (pl : ∀g : Fin groups,Bool → Fin (size rows w menu γ g) ↪ Fin D)
    (located : ∀ b (g : Fin groups) (u : ProtocolRAMReportedPorts.Unit rows w menu γ g.val),
      (pl g b (ProtocolRAMReportedPorts.common rows w menu γ g.val distinct u)).val=
        lr b u.1.val+u.2.val)
    (groupCap : groups≤2^bits) (boundCap : D≤2^bits) (mapCap : groups*poolBatchCount D B≤2^bits)
    (tableCap : 10*(N*cap)≤2^bits) (widthFit : ∀i,(rows i).width<2^bits) (wide : 2^bits≤2^W)
    (menuFits : menu<2^W) (typeFits : γ ≤ menu) (small : 10≤2^W) (slotFits : cap<2^W)
    (hb : 0<B) (hw : B≤2^n) (batchFits : B≤2^W)
    (layoutFit : let C := capacity (Fin groups) D B M; base+(C+2*(C*2*D))≤2^W)
    (ordered : let C := capacity (Fin groups) D B M; base+(C+2*(C*2*D))≤ src)
    (room : src+10*(N*cap)<2^W) (sinkLow : sink<src)
    (apart : ∀ f, (sink:Word W)≠TaggedShorterScatter.layout (capacity (Fin groups) D B M) D base layoutFit f)
    (input : (term (tables rom bits width group common left right) γ sink).Fits W src)
    (low : (term (tables rom bits width group common left right) γ sink).Fits W base) :
    let A := tables rom bits width group common left right
    let C := capacity (Fin groups) D B M
    let total := C+2*(C*2*D)
    let c := size (groups:=groups) rows w menu γ
    let addr := TaggedShorterScatter.layout C D base layoutFit
    ∃ out, (clearedProcedure W base total src (N*cap) γ sink A).Exec mem out
      ((4+6*total)+(8+16230*(N*cap))) ∧
      (∀ i,decide ((out (addr (.inl i)).val).val≠0)=groupOccupied c bound B M i) ∧
      (∀ sb x,decide ((out (addr (.inr (false,sb,x))).val).val≠0)=groupMask c bound B M pl sb x) ∧
      (∀ sb x,Computability.VPVNP.RAMSerialization.wordBits n (((out (addr (.inr (true,sb,x))).val).val:ℕ):Word n)=
        groupID c bound M hb hw pl sb x) := by
  obtain ⟨out,run,_,physical⟩ := publish_report_at_framed mem rows width group common left right cr lr dynamic read
    gFit distinct bound copied cn pl located groupCap boundCap mapCap tableCap widthFit wide menuFits
    typeFits small slotFits hb hw batchFits layoutFit ordered room sinkLow apart input low
  exact ⟨out,run,physical⟩

theorem publish_report {N groups D B M n w menu cap rom bits base src sink γ : ℕ}
    (mem : Memory W) (rows : Fin N→ProtocolRAMEmit.Row)
    (width group common left right : Bank) (cr : Fin N→ℕ) (lr : Bool→Fin N→ℕ)
    (dynamic : Dynamic rows mem width group common left right cr lr)
    (read : ∀ j : Fin 13,∀ x : ℕ,x<2^bits → (bank rom bits j).read mem (x:Word W)=
      words groups D B M base w menu cap j x)
    (gFit : ∀i,(rows i).group<groups) (distinct : Function.Injective fun i=>(rows i).link)
    (bound : ∀g : Fin groups,size rows w menu γ g≤D)
    (copied : ∀i,ProtocolRAMReportedPorts.pieces rows w i≤cap)
    (cn : ∀ (g : Fin groups) (i : ProtocolRAMReportedPorts.InGroup rows w menu γ g.val),cr i.val =
      ProtocolRAMPortRanks.«prefix» (ProtocolRAMReportedPorts.slotCount rows w menu γ g.val)
        (fun j=>(rows j.val).link) i)
    (lo : ∀ b (g : Fin groups) (i : ProtocolRAMReportedPorts.InGroup rows w menu γ g.val),lr b i.val =
      ProtocolRAMPortRanks.«prefix» (ProtocolRAMReportedPorts.slotCount rows w menu γ g.val)
        (fun j=>ProtocolRAMPortRanks.bySite (ProtocolRAMReportedPorts.sideSite rows b) j.val) i)
    (groupCap : groups≤2^bits) (boundCap : D≤2^bits) (mapCap : groups*poolBatchCount D B≤2^bits)
    (tableCap : 10*(N*cap)≤2^bits) (widthFit : ∀i,(rows i).width<2^bits) (wide : 2^bits≤2^W)
    (menuFits : menu<2^W) (typeFits : γ ≤ menu) (small : 10≤2^W) (slotFits : cap<2^W)
    (hb : 0<B) (hw : B≤2^n) (batchFits : B≤2^W)
    (layoutFit : let C := capacity (Fin groups) D B M; base+(C+2*(C*2*D))≤2^W)
    (ordered : let C := capacity (Fin groups) D B M; base+(C+2*(C*2*D))≤ src)
    (room : src+10*(N*cap)<2^W) (sinkLow : sink<src)
    (apart : ∀ f, (sink:Word W)≠TaggedShorterScatter.layout (capacity (Fin groups) D B M) D base layoutFit f)
    (input : (term (tables rom bits width group common left right) γ sink).Fits W src)
    (low : (term (tables rom bits width group common left right) γ sink).Fits W base) :
    let A := tables rom bits width group common left right
    let C := capacity (Fin groups) D B M
    let total := C+2*(C*2*D)
    let c := size (groups:=groups) rows w menu γ
    let pl := fun g => ProtocolRAMReportedPorts.place rows w menu γ g.val distinct (bound g)
    let addr := TaggedShorterScatter.layout C D base layoutFit
    ∃ out, (clearedProcedure W base total src (N*cap) γ sink A).Exec mem out
      ((4+6*total)+(8+16230*(N*cap))) ∧
      (∀ i,decide ((out (addr (.inl i)).val).val≠0)=groupOccupied c bound B M i) ∧
      (∀ sb x,decide ((out (addr (.inr (false,sb,x))).val).val≠0)=groupMask c bound B M pl sb x) ∧
      (∀ sb x,Computability.VPVNP.RAMSerialization.wordBits n (((out (addr (.inr (true,sb,x))).val).val:ℕ):Word n)=
        groupID c bound M hb hw pl sb x) := by
  apply publish_report_at mem rows width group common left right cr lr dynamic read gFit distinct
    bound copied cn (fun g => ProtocolRAMReportedPorts.place rows w menu γ g.val distinct (bound g))
    _ groupCap boundCap mapCap tableCap widthFit wide menuFits typeFits small slotFits hb hw batchFits
    layoutFit ordered room sinkLow apart input low
  intro b g v
  exact (ProtocolRAMReportedPorts.read_place rows w menu γ g.val distinct (bound g) b v).trans
    (congrArg (·+v.2.val) (lo b g v.1).symm)

end Hierarchy.TaggedShorterReportAdvice

end
end OAI
