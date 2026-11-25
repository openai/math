import OAI.ThreeFlat.Diagonal.PhysicalProgramRecords
import OAI.ThreeFlat.Diagonal.PhysicalIndividualCharge
import OAI.ThreeFlat.Diagonal.RefreshCursorTime
import OAI.ThreeFlat.Diagonal.HistorySelectedChronology
import OAI.ThreeFlat.Diagonal.PhysicalRefreshAssembly
import OAI.ThreeFlat.Diagonal.PhysicalRefreshOutput
import OAI.ThreeFlat.RAM.AdmissionSandwich

namespace OAI
/-! # End-to-end native admission of one chronological physical refresh -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.PhysicalProcedure NavigationDirectory
open CompressorPacking Native RefreshDemandRows RefreshTies RefreshStageNav
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F : Type} [Field F] {W s rem h pad K : ℕ} {c : Fin (2^s)→Fin (2^s)→ℕ} {C γ : ℝ}
    (T : RefreshMotif.Table F c (1+h+pad) C) (A : State (2^s) (s+rem))
    (hm : 2≤2^s) (hh : 0<h) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)
    (zero : ∀ i,c i i=0) (conn : Expander.Bound (Expander.transition c h) ℝ γ)
set_option quotPrecheck false
local notation "M" => refreshBinary T A hm hh sym rows zero conn
local notation "Q" => refreshBinaryFamily T A hm hh sym rows zero conn
local notation "m" => 2^s
local notation "v" => Fintype.card A.Base
local notation "d" => 1+h+pad

/-- The time depends only on the immutable chronological header and the fixed
grid program. All externally guessed W-bit counts are allowed at entry. -/
def refreshCallTime (K : ℕ) (cur : Word W) (csr : Cursor) :=
  let en := allocate K csr (.refresh v m (2^rem) h pad)
  (refreshPre T cur).time en.words+(6+(v*2^rem)*(2*AdmissionBank.cost 0 K+4)+
    refreshTailTime T sym rows zero cur K en.words)

/-- The common word-fit threshold for the sole fixed refresh grid of the repeated block. -/
def refreshFixedWords :=
  7+2*(1+h+pad)+m*h+2*m+(T.last+1)+2*m*m+refreshBaseBound T+refreshWidthFactor T

theorem refresh_scalar_room {u : ℕ} (hu : 40≤u) (fixed : refreshFixedWords T≤u) (alphabet : K≤u)
    (arena : (Stage.refresh v m (2^rem) h pad).heapWords≤2^(u^10))
    (wire : A.maxWidth+1≤(2^(u^10))^4) :
    let W := 16*u^10
    v*m≤2^W ∧ 2^rem<2^W ∧ 2*d<2^W ∧ 6<2^W ∧ m*h≤2^W ∧ 2*m<2^W ∧
      m*2^rem<2^W ∧ T.last+1≤2^W ∧ K<2^W ∧
      1+2*m*m*A.maxWidth+refreshBaseBound T<2^W ∧ refreshWidthFactor T*(1+A.maxWidth)<2^W := by
  dsimp only
  let V:=2^(u^10)
  have huV : u≤V := (Nat.le_self_pow (by decide : 10≠0) u).trans (Nat.lt_two_pow_self.le)
  have four : 4≤V := by omega
  have huge : 2^(16*u^10)=V^16 := by dsimp [V];rw [Nat.mul_comm,pow_mul]
  rw [huge]
  have one_lt : 1<V := by omega
  have big : V<V^16 := by simpa using Nat.pow_lt_pow_right one_lt (by decide : 1<16)
  have nodes : (v*m)*2^rem≤V := by
    let n:=RefreshStageLayout.counts v m (2^rem) h pad
    have hn : (v*m)*2^rem=n.nodes := rfl
    have amount : n.nodes≤(15+8*d)*n.nodes := Nat.le_mul_of_pos_left _ (by positivity)
    rw [hn]
    exact (amount.trans (Nat.le_add_left _ _)).trans arena
  have vpos : 0<v := Fintype.card_pos
  have oldRows : v*m≤V := (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans nodes
  have lanes : m*2^rem≤V := by
    rw [Nat.mul_assoc] at nodes
    exact (Nat.le_mul_of_pos_left _ vpos).trans nodes
  have l : 2^rem≤V := (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)).trans lanes
  unfold refreshFixedWords at fixed
  have coef : 2*m*m≤V := by omega
  have gain : refreshWidthFactor T≤V := by omega
  change A.maxWidth+1≤V^4 at wire
  have width : A.maxWidth≤V^4 := (Nat.le_add_right _ 1).trans wire
  have prod : 2*m*m*A.maxWidth≤V^5 := (Nat.mul_le_mul coef width).trans_eq (by ring)
  have prod' : refreshWidthFactor T*(1+A.maxWidth)≤V^5 :=
    (Nat.mul_le_mul gain (by simpa [Nat.add_comm] using wire)).trans_eq (by ring)
  have five : V^5<V^16 := Nat.pow_lt_pow_right one_lt (by decide)
  have six : V^6<V^16 := Nat.pow_lt_pow_right one_lt (by decide)
  have b : V≤V^5 := Nat.le_self_pow (by decide) V
  have one : 1≤V^5 := Nat.pow_pos (by omega)
  have res : 1+2*m*m*A.maxWidth+refreshBaseBound T≤V^6 :=
    (show 1+2*m*m*A.maxWidth+refreshBaseBound T≤3*V^5 by omega).trans
      ((Nat.mul_le_mul_right _ (show 3≤V by omega)).trans_eq (by ring))
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega,by omega,by omega,
    res.trans_lt six,prod'.trans_lt five⟩

private theorem bank_word {motifs K W : ℕ} (R : HistogramRegister.Rows motifs K W)
    (x : HistogramRegister.Words motifs K W) (mem : Memory W) (ctrl dense : ℕ)
    (layout : HistogramRegister.BankLayout ctrl R x mem) (address : AdmissionBank.denseBase ctrl mem=dense)
    (i : Fin motifs) (j : Fin K) : (mem (dense+i.val*K+j.val)).val=(x i j).val := by
  have word := layout.words i j
  rw [address,Nat.mul_comm K] at word
  exact congrArg Fin.val word

set_option maxHeartbeats 800000 in
/-- The actual installed procedure rejects every invalid record, including
nonzero padded symbols. Each accepted branch returns its exact physical
tensor width image, sparse supplies, four kernel directories, owner maps
and the next header pointer, preserving all prior stages. -/
theorem refresh_admission (field : FieldCode F W) (width : 0<W) (cur : Word W) (input : Memory W) (csr : Cursor)
    (u : CursorSpace cur input csr K v s rem h pad)
    (old : SlotImage.Stored A.graph A.order (tagOrdinal (s+rem)) (oldColumns csr v m) (fun i=>(input i).val) A.width)
    (fit : (Q).Fits K W) (x : HistogramRegister.Words (Q).motifs K W)
    (raw : ∀ (i : Fin (Q).motifs) (j : Fin K),input (csr.dense+i.val*K+j.val)=x i j)
    (bases : v*m≤2^W) (lanes : 2^rem<2^W) (deg : 2*d<2^W) (small : 6<2^W)
    (rom : m*h≤2^W) (rot : 2*m<2^W) (full : m*2^rem<2^W) (tiles : T.last+1≤2^W)
    (alphabet : refreshSymbolBound T≤K) (Kfit : K<2^W)
    (room : 1+2*m*m*A.maxWidth+refreshBaseBound T<2^W) (widthFit : refreshWidthFactor T*(1+A.maxWidth)<2^W) :
    let body := NavigationPass.refresh cur K s h pad T sym rows zero
    let bits := List.ofFn (HistogramRegister.bitTable x)
    let pre := ((refreshPre T cur).pipeline cur).run input
    TickStageSpec.Admission field body.block body.publicData (fun mem=>mem=input) (fun _=>(((Q).record fit).read bits).isSome)
      (fun _ out=>∃ b : Fin (M).rules.count,((Q).record fit).read bits=some b ∧
        RefreshOutput T A hm hh sym rows zero conn K cur csr b pre out ∧
        (∀ (i : Fin (Q).motifs) (f : Fin 3),out (csr.heap+(i.val*3+f.val))=
          ((if f.val=0 then (Q).copies i else if f.val=1 then
            (T.winner (refreshBinaryGraph A) (tagOrdinal s).symm (refreshBinaryInput A)
              ((refreshBlockOrder A).symm i)).val else Fintype.card ((Q).alphabet i):ℕ):Word W)) ∧
        ∀ i,i≠cur.val → (i<csr.heap ∨ (allocate K csr (.refresh v m (2^rem) h pad)).next.heap≤ i) → out i=input i)
      (refreshCallTime T A sym rows zero K cur csr) := by
  let en := allocate K csr (.refresh v m (2^rem) h pad)
  let p := refreshPre T cur
  let mid := (p.pipeline cur).run input
  let bits := List.ofFn (HistogramRegister.bitTable x)
  let good : Prop := (((Q).record fit).read bits).isSome
  let w := en.words
  let keep := fun i : ℕ=>i<csr.heap ∨ en.next.heap≤ i
  have pSafe := u.pre_safe T.base (fun j=>Fintype.card (T.block j).Alphabet)
  have pf := p.run_spec cur input csr.header 63 w keep u.header (.inr u.controls) u.start_live pSafe
  have um : CursorSpace cur mid csr K v s rem h pad := u.frame _ pf.2.2
  have prepared := refresh_prepare_physical T A hm hh sym rows zero conn cur input (oldColumns csr v m)
    (en.words 12) csr.heap old u.prepare (by omega) lanes tiles room
  have bank := refresh_bank T A hm hh sym rows zero conn cur input csr u old fit x raw (by omega) lanes tiles Kfit room
  have mid_eq : (preparation cur T.base (fun j=>Fintype.card (T.block j).Alphabet)).run input=mid :=
    congrArg (fun (a : Pipeline W)=>a.run input) (pre_pipeline cur T.base (fun j=>Fintype.card (T.block j).Alphabet)).symm
  dsimp only at prepared bank
  rw [mid_eq] at prepared bank
  have chk : TickStageSpec.Admission field (NavigationPass.admit cur K).block (NavigationPass.admit cur K).publicData
      (fun z=>z=mid) (fun _=>good) (fun mem out=>out=mem) (6+(Q).motifs*(2*AdmissionBank.cost 0 K+4)) :=
    TickStageSpec.Admission.mono
      (pre:=fun z=>AdmissionBank.Fits cur.val K z ∧ HistogramRegister.BankLayout cur.val ((Q).rows fit) x z)
      (good:=fun _=>good) (post:=fun mem out=>out=mem)
      (NavigationPass.admit_record field width cur ((Q).rows fit) ((Q).sequence fit) x)
      (by rintro z rfl; exact bank) (fun _ _=>Iff.rfl) (fun _ _ _ _ same=>same) le_rfl
  let kp := p.time w
  let kg := 6+(Q).motifs*(2*AdmissionBank.cost 0 K+4)
  let ks := refreshTailTime T sym rows zero cur K w
  let endM := refreshAfter T sym rows zero cur K mid
  let suffix := refreshSuffix T sym rows zero cur K
  have front : (p.pipeline cur).program.Spec (fun z=>z=input) (fun _ out=>out=mid) kp :=
    Procedure.Spec.mono (A:=(p.pipeline cur).program) (pre:=fun z=>z=input)
      (post:=fun _ out=>out=mid ∧ CursorSpace cur out csr K v s rem h pad ∧ ∀ i,keep i → out i=input i)
      (budget:=kp) (u.call p pSafe) (fun _=>id) (fun _ _ done=>done.1) le_rfl
  have back : suffix.Spec (fun z=>z=mid ∧ good) (fun _ out=>out=endM) ks :=
    Procedure.Spec.mono (A:=suffix) (pre:=fun z=>z=mid) (post:=fun _ out=>out=endM) (budget:=ks)
      (refresh_tail_returns T sym rows zero cur K mid csr um) (fun _ h=>h.1) (fun _ _=>id) le_rfl
  let joined := (p.pipeline cur).program.seq ((NavigationPass.admit cur K).seq suffix)
  have linked : TickStageSpec.Admission field joined.block joined.publicData (fun z=>z=input)
      (fun _=>good) (fun _ out=>out=endM) (kp+(kg+ks)) :=
    TickStageSpec.guarded field (p.pipeline cur).program (NavigationPass.admit cur K) suffix
      (fun z=>z=input) (fun z=>z=mid) good (fun _=>mid) (fun _=>endM) kp kg ks
      front (fun _ _=>rfl) chk back
  dsimp only
  rw [refresh_native_code]
  intro np nr nk machine
  refine TickStageSpec.Admission.mono (b:=joined.block) (data:=joined.publicData)
    (pre:=fun z=>z=input) (good:=fun _=>good) (post:=fun _ out=>out=endM)
    (t:=kp+(kg+ks)) linked (fun _=>id) (fun _ _=>Iff.rfl) ?_ le_rfl machine
  intro _ out _ accepted final
  obtain ⟨b,rb⟩ := Option.isSome_iff_exists.mp accepted
  have words := refresh_read_table T A hm hh sym rows zero conn fit x b rb
  have parsed (i : Fin (Q).motifs) (j : Fin K) : (mid (csr.dense+i.val*K+j.val)).val=
      (HistogramRegister.words ((Q).rows fit) ((Q).sequence fit b) i j).val := by
    rw [words]
    have ad : AdmissionBank.denseBase cur.val mid=csr.dense := um.read 1 (by decide)
    exact bank_word ((Q).rows fit) x mid cur.val csr.dense bank.2 ad i j
  have actual := refresh_after_physical T A hm hh sym rows zero conn cur mid csr um prepared.1 b fit parsed
    bases lanes deg small rom rot full tiles alphabet room widthFit
  subst out
  refine ⟨b,rb,actual,?_,?_⟩
  · intro i f
    have fi : i.val*3+f.val<(Q).motifs*3 := (Nat.add_lt_add_left f.isLt _).trans_le (by
      simpa only [Nat.succ_mul] using Nat.mul_le_mul_right 3 i.isLt)
    have upper : csr.heap+(i.val*3+f.val)<csr.heap+3*(v*2^rem) := by
      rw [Nat.mul_comm 3]
      exact Nat.add_lt_add_left fi _
    exact (actual.descriptors _ (Nat.le_add_right _ _) upper).trans (prepared.2 i f)
  · intro i different range
    exact (actual.frame i different range).trans (pf.2.2 i range)



def refreshAbsoluteTicks (K : ℕ) (cur : Word W) (csr : Cursor) (sites t : ℕ) :=
  let en := allocate K csr (.refresh sites m (2^t) h pad)
  (refreshPre T cur).time en.words+(6+(sites*2^t)*(2*AdmissionBank.cost 0 K+4)+
    refreshTailTime T sym rows zero cur K en.words)

theorem refreshCallTime_absolute (K : ℕ) (cur : Word W) (csr : Cursor) :
    refreshCallTime T A sym rows zero K cur csr = refreshAbsoluteTicks T sym rows zero K cur csr v rem := rfl

private theorem two_scan_times {l r cw ow n child owner : ℕ}
    (left : l = n) (right : r = n) (childWork : cw = child) (ownerWork : ow = owner) :
    (11+l*(2*cw+4))+(11+r*(2*ow+4)) = (11+n*(2*child+4))+(11+n*(2*owner+4)) := by
  subst l
  subst r
  subst cw
  subst ow
  rfl

attribute [local irreducible] RAM.HeaderScan.closed RefreshNodeOwners.expr in
/-- The two refresh ownership streams read only their two row-count slots when priced. -/
private theorem owner_times {W : ℕ} (cur : Word W) (ports : ℕ) (word : ℕ → ℕ)
    (n child owner : ℕ) (childRows : word 43 = n) (ownerRows : word 45 = n)
    (childWork : (RAM.HeaderScan.closed (w:=W) (RefreshNodeOwners.expr cur.val ports true)).binds = child)
    (ownerWork : (RAM.HeaderScan.closed (w:=W) (RefreshNodeOwners.expr cur.val ports false)).binds = owner) :
    (RefreshNodeOwners.both cur ports).time word =
      (11+n*(2*child+4))+(11+n*(2*owner+4)) := by
  simp only [RefreshNodeOwners.both, RefreshNodeOwners.scan, eq_self, Bool.false_eq_true,
    ite_true, ite_false, RAM.HeaderScan.Scans.time]
  exact two_scan_times childRows ownerRows childWork ownerWork

theorem refresh_absolute_time (K : ℕ) :
    ∃ B : ℕ,∀ (W : ℕ) (cur : Word W) (csr : Cursor) (t V : ℕ),
      refreshAbsoluteTicks T sym rows zero K cur csr V t ≤ 133+B*(V*m*2^t) := by
  let G := DoublePorts.ofMatrix (Equiv.refl _) c sym rows zero
  obtain ⟨B,lim⟩ := cursor_scan_time G pad K T.base (fun j=>Fintype.card (T.block j).Alphabet)
    (fun j=>(T.block j).bits) (poolOf T rows)
  let child := (RefreshNodeOwners.expr 0 m true).work
  let owner := (RefreshNodeOwners.expr 0 m false).work
  let guess := 2*AdmissionBank.cost 0 K+4
  refine ⟨B+(2*child+4)+(2*owner+4)+guess,?_⟩
  intro W cur csr t V
  let P := V*m*2^t
  let e := allocate K csr (.refresh V m (2^t) h pad)
  have rowsN : V*2^t≤P := by
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos s))
  have structs := lim W cur csr V t
  have costChild : (RAM.HeaderScan.closed (w:=W) (RefreshNodeOwners.expr cur.val m true)).binds=child := by
    rw [RAM.HeaderScan.binds_closed];rfl
  have costOwner : (RAM.HeaderScan.closed (w:=W) (RefreshNodeOwners.expr cur.val m false)).binds=owner := by
    rw [RAM.HeaderScan.binds_closed];rfl
  have childRows : e.words 43 = P := rfl
  have ownerRows : e.words 45 = P := rfl
  have own := owner_times cur m e.words P child owner childRows ownerRows costChild costOwner
  change (refreshPre T cur).time e.words+(6+(V*2^t)*guess+
    ((refreshPost T sym rows zero cur K).time e.words+((recordScans cur m (1+h+pad) K).time e.words+
      ((RefreshNodeOwners.both cur m).time e.words+6))))≤_
  rw [own]
  change (refreshPre T cur).time e.words+(refreshPost T sym rows zero cur K).time e.words+
    (recordScans cur m (1+h+pad) K).time e.words≤99+B*P at structs
  have g := Nat.mul_le_mul_right guess rowsN
  dsimp only [P] at *
  nlinarith only [g,structs]



/-- The complete native refresh, including both owner arrays and advancing the header. -/
theorem refresh_return_time (K : ℕ) :
    ∃ B : ℕ,∀ (W : ℕ) (cur : Word W) (csr : Cursor) (t : ℕ) (state : State m (s+t)),
      refreshCallTime T state sym rows zero K cur csr ≤ 133+B*(Fintype.card state.Base*m*2^t) := by
  obtain ⟨B,fit⟩ := refresh_absolute_time T sym rows zero K
  exact ⟨B,fun W cur c t a=>fit W cur c t (Fintype.card a.Base)⟩

/-- The mixed-radix order chosen by the native refresh allocation. -/
def refreshArchiveSites (K : ℕ) (csr : Cursor) (branch : Fin (M).rules.count) : ((M).next branch).ArchiveSites :=
  ⟨refreshOutputLayer K csr v m (2^rem) h pad,refreshFinalOrder T A hm hh sym rows zero conn branch⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2300000 in
/-- The actual four-word incidence records of the admitted graph at every site. -/
theorem RefreshOutput.halfRows {cur : Word W} {csr : Cursor} {branch : Fin (M).rules.count}
    {prepared out : Memory W} (receipt : RefreshOutput T A hm hh sym rows zero conn K cur csr branch prepared out)
    (heapRoom : (allocate K csr (.refresh v m (2^rem) h pad)).next.heap≤2^W)
    (small : ∀ y,((M).next branch).incidentWidth y<2^W) :
    State.HalfRows (refreshArchiveSites T A hm hh sym rows zero conn K csr branch)
      (fun x=>csr.heap≤x ∧ x<(allocate K csr (.refresh v m (2^rem) h pad)).next.heap) (fun x=>(out x).val) := by
  let en:=allocate K csr (.refresh v m (2^rem) h pad)
  change en.next.heap≤2^W at heapRoom
  let P:=CursorSpace.recordPointers en
  let graph:=CompressorRefresh.graph (numberedRefreshGraph A) (DoublePorts.ofMatrix (Equiv.refl _) c sym rows zero) hm pad
  let width:=refreshNumericWidths T A hm hh sym rows zero conn branch
  let n:=v*m*2^rem
  let ord:=refreshFinalOrder T A hm hh sym rows zero conn branch
  let site:=(Records.siteOrder («v»:=v) («m»:=m) (t:=rem)).symm
  let X:=(M).next branch
  have siteId' (j:Fin n) : Records.siteId ((site j).1.1,(site j).2) (site j).1.2=j.val :=
    (Records.siteOrder_val (site j)).symm.trans (congrArg Fin.val (site.symm_apply_apply j))
  have ordinal (q : Records.Table) (j:Fin n) (f:Fin (q.cols d)) :
      (Records.rowOrder d q (site j,f)).val=j.val*q.cols d+f.val := by
    rw [Records.rowOrder,RefreshStageLayout.pair_index]
    simp only [site,Equiv.apply_symm_apply,Equiv.refl_apply]
  have cell (q : Records.Table) (j:Fin n) (f:Fin (q.cols d)) :
      out (P.dst q+j.val*q.cols d+f.val)=(q.value P csr.header K graph width (fun x=>(prepared x).val) (site j,f):Word W) := by
    simpa only [ordinal,Nat.add_assoc] using receipt.records q (site j,f)
  obtain ⟨_,start,_,edges,ends⟩:=CursorSpace.retained_addresses
    (c:=csr) (K:=K) («v»:=v) (a:=s) (t:=rem) (h:=h) (pad:=pad)
  obtain ⟨lastChild,lastOwner,_,_⟩:=RefreshNodeOwners.owner_spans
    (c:=csr) (K:=K) («v»:=v) (a:=s) (t:=rem) (h:=h) (pad:=pad)
  obtain ⟨_,km,mh,hhp,_⟩:=CursorSpace.record_layout
    (c:=csr) (K:=K) («v»:=v) (a:=s) (t:=rem) (h:=h) (pad:=pad)
  change csr.heap+3*(v*2^rem)≤P.kernel at start
  change P.kernel+n*5=P.motif at km
  change P.motif+n*6=P.headers at mh
  change P.headers+n*2=P.halves at hhp
  change en.words 42+n=en.words 44 at lastChild
  change en.words 44+n=en.next.heap at lastOwner
  have endKernel : P.kernel+n*5≤en.words 42:=ends .kernel
  have endWidth : v*m*d*2^rem≤P.kernel := (Nat.le_add_left _ _).trans edges
  have ownerEnd : en.words 42 ≤ en.next.heap := by omega
  have below (q:Records.Table) (j:Fin n) (f:Fin (q.cols d)) :
      P.dst q+j.val*q.cols d+f.val<en.next.heap := by
    have rowBound : j.val*q.cols d+f.val<n*q.cols d := by
      rw [←ordinal q j f]
      exact (Records.rowOrder d q (site j,f)).isLt
    have box:P.dst q+n*q.cols d≤en.words 42:=ends q
    rw [Nat.add_assoc]
    exact (Nat.add_lt_add_left rowBound (P.dst q)).trans_le (box.trans ownerEnd)
  have access (j:Fin n) (i:Fin (2*d)) (k:Fin 4) :
      csr.heap≤P.halves+j.val*(8*d)+4*i.val+k.val ∧ P.halves+j.val*(8*d)+4*i.val+k.val<en.next.heap := by
    have hi:=below .halves j (Records.halfCol (i,k))
    change P.halves+j.val*(8*d)+(Records.halfCol (i,k)).val<en.next.heap at hi
    rw [Records.halfCol_val,Nat.mul_comm i.val 4] at hi
    exact ⟨by omega,by simpa only [Nat.add_assoc] using hi⟩
  have pointer (j:Fin n) : (out (P.headers+j.val*2+1)).val=P.halves+j.val*(8*d) := by
    have stored:=cell .halfHeader j (1 : Fin 2)
    change out (P.headers+j.val*2+1)=((P.halves+Records.siteId ((site j).1.1,(site j).2) (site j).1.2*(8*d):ℕ):Word W) at stored
    rw [siteId'] at stored
    have lo:=below .halves j ⟨0,by change 0<8*(1+h+pad);positivity⟩
    change P.halves+j.val*(8*d)+0<en.next.heap at lo
    exact (congrArg Fin.val stored).trans (Fin.val_cast_of_lt (by simpa only [Nat.add_zero] using lo.trans_le heapRoom))
  have word (y:X.Site) (i:Fin (2*d)) (k:Fin 4) :
      let j:=ord y
      let e:=ShrinkStage.Halves.sourceHalf graph (site j) i
      out (P.halves+j.val*(8*d)+4*i.val+k.val)=
        ((![ShrinkStage.Halves.edgeNumber finProdFinEquiv e,if i.val<d then 0 else 1,width e,
          ShrinkStage.Halves.prefixValue graph width (site j) i]:Fin 4→ℕ) k:Word W) := by
    have stored:=cell .halves (ord y) (Records.halfCol (i,k))
    simpa only [Records.Table.cols,Records.Pointers.dst,Records.Table.value,Equiv.symm_apply_apply,
      Records.halfCol_val,Nat.mul_comm i.val 4,Nat.add_assoc] using stored
  have source (y:X.Site) (i:Fin (2*d)) : ShrinkStage.Halves.edgeNumber finProdFinEquiv
      (ShrinkStage.Halves.sourceHalf graph (site (ord y)) i)<2^W := by
    have h:=SlotImage.edgeOrdinal_lt finProdFinEquiv (tagOrdinal rem)
      (ShrinkStage.Halves.sourceHalf graph (site (ord y)) i)
    change ShrinkStage.Halves.edgeNumber finProdFinEquiv (ShrinkStage.Halves.sourceHalf graph (site (ord y)) i)<v*m*d*2^rem at h
    exact h.trans_le (endWidth.trans ((Nat.le_add_right _ _).trans (endKernel.trans (ownerEnd.trans heapRoom))))
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro y
    let j:=ord y
    have countWord : out (P.headers+j.val*2)=((2*d:ℕ):Word W) :=
      cell .halfHeader j (0 : Fin 2)
    have bound:=below .halves j ⟨2*d,by change 2*(1+h+pad)<8*(1+h+pad);omega⟩
    change P.halves+j.val*(8*d)+2*d<en.next.heap at bound
    have countRoom : 2*d<2^W := (Nat.le_add_left ..).trans_lt (bound.trans_le heapRoom)
    exact (congrArg Fin.val countWord).trans (Fin.val_cast_of_lt countRoom)
  · intro y i
    change (out ((out (P.headers+(ord y).val*2+1)).val+4*i.val)).val=_
    rw [pointer (ord y)]
    have raw : out (P.halves+(ord y).val*(8*d)+4*i.val)=
        (ShrinkStage.Halves.edgeNumber finProdFinEquiv
          (ShrinkStage.Halves.sourceHalf graph (site (ord y)) i):Word W) := word y i 0
    exact ((congrArg Fin.val raw).trans (Fin.val_cast_of_lt (source y i))).trans
      (refresh_half_src T A hm hh sym rows zero conn branch y i)
  · intro y i
    change (out ((out (P.headers+(ord y).val*2+1)).val+4*i.val+2)).val=_
    rw [pointer (ord y)]
    have eq:=refresh_half_width T A hm hh sym rows zero conn branch y i
    have hi : X.width (ShrinkStage.Halves.sourceHalf X.graph (X.chart.symm y) i)<2^W := by
      rw [←receipt.graph.widthWord (ShrinkStage.Halves.sourceHalf X.graph (X.chart.symm y) i)]
      exact Fin.isLt _
    have raw:=word y i 2
    exact ((congrArg Fin.val raw).trans (Fin.val_cast_of_lt (eq.trans_lt hi))).trans eq
  · intro y i
    change (out ((out (P.headers+(ord y).val*2+1)).val+4*i.val+3)).val=_
    rw [pointer (ord y)]
    have eq:=refresh_half_prefix T A hm hh sym rows zero conn branch y i
    have prefixBound : ShrinkStage.Halves.prefixValue X.graph X.width (X.chart.symm y) i≤X.incidentWidth y := by
      calc
        _≤∑ j : Fin (2*d),X.width (ShrinkStage.Halves.sourceHalf X.graph (X.chart.symm y) j) := by
          unfold ShrinkStage.Halves.prefixValue
          apply Finset.sum_le_sum
          intro j _
          split
          · exact le_rfl
          · exact Nat.zero_le _
        _=X.incidentWidth y:=half_total X.graph X.width (X.chart.symm y)
    exact ((congrArg Fin.val (word y i 3)).trans (Fin.val_cast_of_lt
      (eq.trans_lt (prefixBound.trans_lt (small y))))).trans eq
  · intro y k
    have z:=below .halfHeader (ord y) k
    change P.headers+(ord y).val*2+k.val<en.next.heap at z
    change csr.heap≤P.headers+(ord y).val*2+k.val ∧ _
    exact ⟨by omega,z⟩
  · intro y i k
    change csr.heap≤(out (P.headers+(ord y).val*2+1)).val+4*i.val+k.val ∧
      (out (P.headers+(ord y).val*2+1)).val+4*i.val+k.val<en.next.heap
    rw [pointer (ord y)]
    exact access (ord y) i k

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem refreshArchiveSites_numbered (K : ℕ) (csr : Cursor) (branch : Fin (M).rules.count) :
    (refreshArchiveSites T A hm hh sym rows zero conn K csr branch).Numbered := by
  intro y
  let z := ((M).next branch).chart.symm y
  change (RefreshStageNav.Records.siteOrder (((A.order z.1.1),z.1.2),z.2)).val=
    (((M).next branch).order z.1).val*2^rem+(tagOrdinal rem z.2).val
  rw [RefreshStageNav.Records.siteOrder_val]
  change ((A.order z.1.1).val*m+z.1.2.val)*2^rem+(tagOrdinal rem z.2).val=
    (z.1.2.val+m*(A.order z.1.1).val)*2^rem+(tagOrdinal rem z.2).val
  ring

/-- The physical parent is the owner used to construct the retained one-child record. -/
private theorem refreshArchiveParent (branch : Fin (M).rules.count) (x : A.Site) :
    (M).parent branch x = (M).rules.owner branch x :=
  (refreshParent T A (splitWord s rem) (tagOrdinal s).symm hm hh sym rows zero conn branch x).trans
    (refreshParentSites_apply T A hm hh sym rows zero conn branch x)

private def archiveChildren (branch : Fin (M).rules.count) (y : ((M).next branch).Site) :
    Fin 1 ≃ {x : A.Site // (M).parent branch x = y} :=
  (refreshChildFiber T A hm hh sym rows zero conn branch y).trans
    (Equiv.subtypeEquivRight (fun x =>
      let eqn := refreshArchiveParent T A hm hh sym rows zero conn branch x
      ⟨fun hx => eqn.trans hx, fun hx => eqn.symm.trans hx⟩))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
def refreshArchiveRow {K : ℕ} (csr : Cursor) (branch : Fin (M).rules.count) (prepared : Memory W)
    (old : A.ArchiveSites) (numbered : old.Numbered) (first : old.layer.first=csr.node)
    (copies : ∀ i : Fin (Q).motifs,(prepared (csr.heap+i.val*3)).val=(Q).copies i) :
    (M).ArchiveRow branch old (refreshArchiveSites T A hm hh sym rows zero conn K csr branch)
      (refreshOutputData T A hm hh sym rows zero conn K csr branch prepared)
      (refreshBinaryCharge T A hm hh sym rows zero conn branch) where
  contiguous := by
    have c : old.layer.count=v*m*2^rem := by
      simpa only [Fintype.card_fin] using Fintype.card_congr (old.ord.symm.trans (refreshOldOrder A))
    change csr.node+v*m*2^rem=old.layer.first+old.layer.count
    rw [c,first]
  nonleaf := by
    change (2 : ℕ) ≠ 0
    decide
  children := archiveChildren T A hm hh sym rows zero conn branch
  childId := by
    intro y j
    let x := ((refreshChildFiber T A hm hh sym rows zero conn branch y) j).val
    have ort : (refreshOldOrder A x).val=(old.ord x).val := by
      rw [numbered]
      change (RefreshStageLayout.pair A.order (tagOrdinal (s+rem)) (A.chart.symm x)).val=_
      exact RefreshStageLayout.pair_index ..
    change _=old.layer.first+(old.ord x).val
    rw [first,←ort]
    exact refresh_child_id T A hm hh sym rows zero conn K csr branch prepared y j
  fresh := refresh_archive_charge T A hm hh sym rows zero conn K csr branch prepared copies

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
/-- The direct result of a native refresh call carries the selected counts
in its retained descriptor bank. -/
def refreshArchiveStep {K : ℕ} {cur : Word W} {csr : Cursor} {branch : Fin (M).rules.count} {prepared out : Memory W}
    (result : RefreshOutput T A hm hh sym rows zero conn K cur csr branch prepared out) (fit : (Q).Fits K W)
    (outCopies : ∀ i : Fin (Q).motifs,out (csr.heap+i.val*3)=((Q).copies i:Word W))
    (old : A.ArchiveSites) (numbered : old.Numbered) (first : old.layer.first=csr.node) :
    (M).ArchiveStep branch old (refreshBinaryCharge T A hm hh sym rows zero conn branch) where
  sites := refreshArchiveSites T A hm hh sym rows zero conn K csr branch
  data := refreshOutputData T A hm hh sym rows zero conn K csr branch prepared
  row := refreshArchiveRow T A hm hh sym rows zero conn csr branch prepared old numbered first (by
    intro i
    have size : i.val<v*2^rem := i.isLt
    have eq := (result.descriptors (csr.heap+i.val*3) (by omega) (by omega)).symm.trans (outCopies i)
    exact (congrArg Fin.val eq).trans (Fin.val_cast_of_lt (fit.2 i)))
  ownerPtr := (allocate K csr (.refresh v m (2^rem) h pad)).words 44


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem refreshArchive_parentReads {K : ℕ} {cur : Word W} {csr : Cursor} {branch : Fin (M).rules.count}
    {prepared out : Memory W} (result : RefreshOutput T A hm hh sym rows zero conn K cur csr branch prepared out)
    (old : A.ArchiveSites) (numbered : old.Numbered) (room : v*m*2^rem≤2^W) :
    let en := allocate K csr (.refresh v m (2^rem) h pad)
    let sites := refreshArchiveSites T A hm hh sym rows zero conn K csr branch
    NavigationNodeRows.ParentReads ⟨false,sites.layer.first,en.words 44⟩
      (fun j=>(sites.ord ((M).parent branch (old.ord.symm j))).val) (fun x=>(out x).val) := by
  intro en sites _ j
  let x := old.ord.symm j
  have ix : (refreshOldOrder A x).val=j.val := by
    calc
      _ = (old.ord x).val := by
        rw [numbered]
        exact RefreshStageLayout.pair_index A.order (tagOrdinal (s+rem)) (A.chart.symm x)
      _ = j.val := congrArg Fin.val (old.ord.apply_symm_apply j)
  have record := RefreshOutput.owner_index T A hm hh sym rows zero conn result room x
  dsimp only at record
  rw [ix] at record
  exact record.trans (congrArg (fun z => (refreshFinalOrder T A hm hh sym rows zero conn branch z).val)
    (refreshArchiveParent T A hm hh sym rows zero conn branch x).symm)

theorem refreshArchive_ownerFootprint {K : ℕ} (csr : Cursor) (old : A.ArchiveSites) (j : Fin old.layer.count) :
    let en := allocate K csr (.refresh v m (2^rem) h pad)
    csr.heap≤en.words 44+j.val ∧ en.words 44+j.val<en.next.heap := by
  let en := allocate K csr (.refresh v m (2^rem) h pad)
  have count : old.layer.count=v*m*2^rem := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (old.ord.symm.trans (refreshOldOrder A))
  have bound : j.val<v*m*2^rem := by simpa only [←count] using j.isLt
  obtain ⟨childEnd,ownerEnd,low,_⟩ := RefreshNodeOwners.owner_spans
    (c:=csr) (K:=K) («v»:=v) (a:=s) (t:=rem) (h:=h) (pad:=pad)
  change csr.heap≤en.words 42 at low
  change en.words 42+v*m*2^rem=en.words 44 at childEnd
  change en.words 44+v*m*2^rem=en.next.heap at ownerEnd
  change csr.heap≤en.words 44+j.val ∧ en.words 44+j.val<en.next.heap
  omega

namespace Program

/-- Carry the chosen physical row and its native pointer through the output-degree
equality used in the recursive program. -/
def recastArchiveStep {i l D D' L tariff : ℕ} {B : State i l} (e : D=D') (R : Move F B D L)
    (funding : siteCharge R tariff) (branch : Fin R.rules.count) (old : B.ArchiveSites)
    (step : R.ArchiveStep branch old (funding.1 branch)) :
    (recastMove e R).ArchiveStep (degreeTerm e R branch) old
      ((siteRecast e R funding).1 (degreeTerm e R branch)) := by
  cases e
  exact step

end Program

set_option maxRecDepth 4200 in
set_option maxHeartbeats 450000 in
/-- The transported physical refresh has exactly one immediate predecessor. Its
stage assembly and native archive must therefore publish the same child ordinal. -/
theorem refresh_childOrder_at_scale {Pins : Type} {D : ℕ} (deg : 1+h+pad=D)
    (L : A.Words Pins) {b : Fin (Program.recastMove deg M).rules.count}
    (step : (Program.recastMove deg M).WordStep Pins L b) {old : A.ArchiveSites}
    {charge : ((Program.recastMove deg M).next b).Site→ℕ}
    (row : (Program.recastMove deg M).ArchiveStep b old charge) :
    Move.WordStep.ChildOrder (R := Program.recastMove deg M) (i := b) (L := L) step row := by
  cases deg
  apply step.childOrder_of_subsingleton row
  intro y
  let e : Fin 1 ≃ {x : A.Site // (M).parent b x=y} := archiveChildren T A hm hh sym rows zero conn b y
  exact ⟨fun x z=>e.symm.injective (Subsingleton.elim (e.symm x) (e.symm z))⟩

theorem refresh_childOrder {Pins : Type} (L : A.Words Pins) {K : ℕ} {cur : Word W} {csr : Cursor}
    {branch : Fin (M).rules.count} {prepared out : Memory W}
    (result : RefreshOutput T A hm hh sym rows zero conn K cur csr branch prepared out) (fit : (Q).Fits K W)
    (copies : ∀ i : Fin (Q).motifs,out (csr.heap+i.val*3)=((Q).copies i:Word W))
    (old : A.ArchiveSites) (numbered : old.Numbered) (first : old.layer.first=csr.node) :
    (refreshBinary_assembler T A hm hh sym rows zero conn L branch).ChildOrder
      (refreshArchiveStep T A hm hh sym rows zero conn result fit copies old numbered first) :=
  refresh_childOrder_at_scale T A hm hh sym rows zero conn rfl L _ _


end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
