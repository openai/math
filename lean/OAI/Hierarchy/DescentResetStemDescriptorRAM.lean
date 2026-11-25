import OAI.Hierarchy.DescentResetStemRaw
import OAI.Hierarchy.DescentPeerRankFits
import OAI.Hierarchy.DescentPeerRankWork
import OAI.Hierarchy.DescentResetFieldAssembler
import OAI.Hierarchy.DescentPackedSumWords
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.ProbeStageProgramSize

namespace OAI
/-! # Construct each actor's seven scalar stem digits before broadcast -/
namespace Hierarchy.DescentResetStemDescriptorRAM
open DescentSIMDLookup DescentSortedRoster DescentFallbackRankRAM DescentFallbackLeafScan DescentPackedColony
open DescentColonies.SplitRAM DescentResetFieldAssembler Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing BigOperators
noncomputable section

structure Inputs (K : ℕ) where
  roster : Fin 4→Expr
  here : Expr
  src : Fin K→Expr
  dst : Fin K→Expr
  live : Fin K→Expr
  selfAbsent : Fin K→Expr
  core : Fin K→Expr

structure Inputs.All {K : ℕ} (L : Inputs K) (P : Expr→Prop) : Prop where
  roster : ∀j,P (L.roster j)
  here : P L.here
  src : ∀j,P (L.src j)
  dst : ∀j,P (L.dst j)
  live : ∀j,P (L.live j)
  absent : ∀j,P (L.selfAbsent j)
  core : ∀j,P (L.core j)

variable {K H pitch b w : ℕ} (L : Inputs K)

def digitsAt (j : Fin K) : Fin 7→Expr :=
  ![.lit 1,calculate L.roster (L.src j),calculate L.roster (L.dst j),calculate L.roster L.here,
    L.selfAbsent j,L.core j,.lit 1]

/-- Only ranks 0 through 4 and Boolean flags are needed. All seven scalar
lookup pages therefore use just 56 words, independently of the actor count
and of the physical identifier width. -/
def bank (base : ℕ) (j : Fin 7) : Bank := ⟨base+j.val*8,3⟩
def weight (b j d : ℕ) := (d%2^b)*(2^b)^j
def literal (b n : ℕ) := weight b (n/8) (n%8)
def mounted (b base : ℕ) (m : Memory w) := DescentStaticWordColumn.image base (literal b) m 56

def body (base : ℕ) (j : Fin K) : Expr :=
  .branch .eq (L.live j) (.lit 0) (.lit 0)
    (total (fun i=>.lookup (bank base i) (digitsAt L j i)) (List.finRange 7))

def fields (base : ℕ) := List.ofFn (body L base)
def code (b w H base out : ℕ) :=
  (DescentStaticWordColumn.program w base (literal b) 56).seq
    (ProtocolRAM.program w (ProbeStage.Native.columns H out (fields L base)))
def ticks (H base out : ℕ) := (4+10*56)+clock (ProbeStage.Native.columns H out (fields L base))
def output (b H base out : ℕ) (m : Memory w) :=
  result (ProbeStage.Native.columns H out (fields L base)) (mounted b base m)

theorem bank_fits (j : Fin 7) (base out : ℕ) (early : base+56≤out) (word : out<2^w) :
    (bank base j).Fits w out := by
  change 0<8 ∧ 8<2^w ∧ base+j.val*8+8≤out
  have h:=j.isLt
  omega

theorem bank_data (j : Fin 7) (base out : ℕ) (d : ℕ) (tiny : d<8) (m : Memory w)
    (early : base+56≤out) (word : out<2^w) :
    (bank base j).read (mounted b base m) (d:Word w)=(weight b j.val d:Word w) := by
  rw [DescentPackedZip.bank_read _ _ tiny (bank_fits j base out early word)]
  have hi:=j.isLt
  have installed:=DescentStaticWordColumn.read base 56 (literal b) m (j:=j.val*8+d) (by omega)
  have idx : (j.val*8+d)/8=j.val := by omega
  have lane : (j.val*8+d)%8=d := by omega
  simpa only [bank,mounted,literal,idx,lane,Nat.add_assoc] using installed

theorem body_fits (base out : ℕ) (early : base+56≤out) (word : out<2^w)
    (ready : L.All (Expr.Fits w base)) (j : Fin K) : (body L base j).Fits w out := by
  have low : base≤out := by omega
  have ext (e : Expr) (fit : e.Fits w base) := ProtocolRAMGeneratedWrite.fits_mono e low fit
  have ranks (e : Expr) (fit : e.Fits w base) := DescentResetSourceClassRAM.rank_fits L.roster e
    (fun n=>ext _ (ready.roster n)) (ext _ fit)
  refine ⟨ext _ (ready.live j),trivial,trivial,fits_total _ (fun i=>?_) _⟩
  refine ⟨bank_fits i base out early word,?_⟩
  fin_cases i
  · trivial
  · exact ranks _ (ready.src j)
  · exact ranks _ (ready.dst j)
  · exact ranks _ ready.here
  · exact ext _ (ready.absent j)
  · exact ext _ (ready.core j)
  · trivial

structure Values (K H pitch : ℕ) where
  peer : Fin pitch→Fin 4→Option (Fin pitch)
  here : Fin H→Fin pitch
  src : Fin K→Fin H→Fin pitch
  dst : Fin K→Fin H→Fin pitch
  live : Fin K→Fin H→Bool
  selfAbsent : Fin K→Fin H→Bool
  core : Fin K→Fin H→Bool

def Values.descriptor (x : Values K H pitch) (j : Fin K) (r : Fin H) : Meta :=
  if x.live j r then ⟨true,before x.peer (x.here r) (x.src j r),before x.peer (x.here r) (x.dst j r),
    before x.peer (x.here r) (x.here r),x.selfAbsent j r,x.core j r,1⟩ else .blank

structure Observed (x : Values K H pitch) (m : Memory w) : Prop where
  roster : ∀r:Fin H,∀i,(L.roster i).eval m (r.val:Word w)=(target (x.peer (x.here r) i):Word w)
  here : ∀r:Fin H,(L.here.eval m (r.val:Word w)).val=(x.here r).val
  live : ∀j,∀r:Fin H,(L.live j).eval m (r.val:Word w)=((x.live j r).toNat:Word w)
  src : ∀j,∀r:Fin H,x.live j r=true→((L.src j).eval m (r.val:Word w)).val=(x.src j r).val
  dst : ∀j,∀r:Fin H,x.live j r=true→((L.dst j).eval m (r.val:Word w)).val=(x.dst j r).val
  absent : ∀j,∀r:Fin H,x.live j r=true→(L.selfAbsent j).eval m (r.val:Word w)=((x.selfAbsent j r).toNat:Word w)
  core : ∀j,∀r:Fin H,x.live j r=true→(L.core j).eval m (r.val:Word w)=((x.core j r).toNat:Word w)

private theorem score_small (x : Values K H pitch) (v z : Fin pitch) : before x.peer v z<8 := by
  rw [←order_count]
  have dom:=(Finset.card_le_univ ((Finset.univ : Finset (Fin 4)).filter (fun j=>keep x.peer v z j=true)))
  simp only [Fintype.card_fin] at dom
  omega

private theorem raw_value (b : ℕ) (x : Meta) :
    (raw b x).val=∑ i:Fin 7,weight b i.val (digits x i) := by
  change (finFunctionFinEquiv (fun i:Fin 7=>(digits x i:Cell b))).val=_
  exact finFunctionFinEquiv_apply _

private theorem blank_value (b : ℕ) : (raw b .blank).val=0 := by
  rw [raw_value]
  apply Finset.sum_eq_zero
  intro i _
  fin_cases i <;> simp [Meta.blank,digits,weight]

theorem body_read {base out : ℕ} (x : Values K H pitch) (m : Memory w) (seen : Observed L x m)
    (ready : L.All (Expr.Fits w base)) (small : pitch<2^w) (baseEnd : base+56≤out)
    (word : out<2^w) (j : Fin K) (r : Fin H) :
    (body L base j).eval (mounted b base m) (r.val:Word w)=((raw b (x.descriptor j r)).val:Word w) := by
  let mid:=mounted b base m
  let rwrd : Word w:=(r.val:ℕ)
  have unchanged (e : Expr) (fit : e.Fits w base) : e.eval mid rwrd=e.eval m rwrd :=
    eval_below _ _ _ _ fit (fun a ha=>DescentStaticWordColumn.frame _ _ _ m a (.inl ha))
  have flag := (unchanged _ (ready.live j)).trans (seen.live j r)
  cases hv : x.live j r with
  | false =>
    simp only [hv,Bool.toNat_false,Nat.cast_zero] at flag
    change (if (L.live j).eval mid rwrd == 0 then (0:Word w) else _) = _
    simp [flag,Values.descriptor,hv,blank_value]
  | true =>
    let record : Meta:=⟨true,before x.peer (x.here r) (x.src j r),before x.peer (x.here r) (x.dst j r),
      before x.peer (x.here r) (x.here r),x.selfAbsent j r,x.core j r,1⟩
    have rank (e:Expr) (atZ:Fin pitch) (fit:e.Fits w base) (which:(e.eval m rwrd).val=atZ.val) :
        (calculate L.roster e).eval mid rwrd=(before x.peer (x.here r) atZ:Word w) := by
      apply rank_read x.peer mid rwrd L.roster (x.here r) small
        (fun i=>(unchanged _ (ready.roster i)).trans (seen.roster r i)) e atZ
      rw [unchanged e fit]
      exact which
    have entry (i : Fin 7) : ((digitsAt L j i).eval mid rwrd)=(digits record i:Word w) := by
      fin_cases i
      · rfl
      · exact rank _ _ (ready.src j) (seen.src j r hv)
      · exact rank _ _ (ready.dst j) (seen.dst j r hv)
      · exact rank _ _ ready.here (seen.here r)
      · exact (unchanged _ (ready.absent j)).trans (seen.absent j r hv)
      · exact (unchanged _ (ready.core j)).trans (seen.core j r hv)
      · rfl
    have bounded (i : Fin 7) : digits record i<8 := by
      fin_cases i
      · exact (by decide : (1:ℕ) < 8)
      · exact score_small x _ _
      · exact score_small x _ _
      · exact score_small x _ _
      · cases eqn:x.selfAbsent j r <;> simp [record,digits,eqn]
      · cases eqn:x.core j r <;> simp [record,digits,eqn]
      · exact (by decide : (1:ℕ) < 8)
    have piece (i : Fin 7) : (Expr.lookup (bank base i) (digitsAt L j i)).eval mid rwrd=
        (weight b i.val (digits record i):Word w) := by
      change (bank base i).read mid ((digitsAt L j i).eval mid rwrd)=_
      rw [entry]
      exact bank_data i base out _ (bounded i) m baseEnd word
    have emitted:=DescentPackedSumWords.eval_sum _ _ mid rwrd piece (List.finRange 7)
    rw [←List.ofFn_eq_map,List.sum_ofFn,←raw_value] at emitted
    have one : (1:Word w)≠0 := by
      have wide : 1<2^w:=by omega
      intro bad
      have v:=congrArg Fin.val bad
      change 1 % (2^w) = 0 at v
      rw [Nat.mod_eq_of_lt wide] at v
      exact Nat.one_ne_zero v
    have liveOne : (L.live j).eval mid rwrd=1 := by simpa only [hv,Bool.toNat_true,Nat.cast_one] using flag
    change (if (L.live j).eval mid rwrd == 0 then (0:Word w) else _) =_
    rw [liveOne,ite_eq_right (by simpa using one)]
    simpa only [Values.descriptor,hv,ite_true] using emitted

theorem run (b base out : ℕ) (x : Values K H pitch) (m : Memory w) (seen : Observed L x m)
    (ready : L.All (Expr.Fits w base)) (small : pitch<2^w) (early : base+56≤out)
    (room : out+K*H<2^w) :
    let last:=output L b H base out m
    (code L b w H base out).Exec m last (ticks L H base out) ∧
      DescentResetStemHeaders.Raw out (fun j r=>raw b (x.descriptor j r)) last ∧
      (∀u,u<base ∨ base+56≤u→u<out ∨ out+K*H≤u→last u=m u) ∧ CheapCode (code L b w H base out) := by
  let es:=fields L base
  let mid:=mounted b base m
  have n : es.length=K := List.length_ofFn
  have word : out<2^w := (Nat.le_add_right ..).trans_lt room
  have indexed : ∀e∈es,e.Fits w out := by
    intro e h
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp h
    exact body_fits L base out early word ready j
  have book : (DescentStaticWordColumn.program w base (literal b) 56).Exec m mid (4+10*56) :=
    DescentStaticWordColumn.mount base 56 (literal b) m (early.trans_lt word)
  have scans : (ProtocolRAM.program w (ProbeStage.Native.columns H out es)).Exec mid
      (result (ProbeStage.Native.columns H out es) mid) (clock (ProbeStage.Native.columns H out es)) :=
    ProbeStage.Native.columns_exec es mid (ProbeStage.Native.columns_safe (n:=H) es le_rfl indexed
    (by simpa only [n] using room))
  refine ⟨by
    intro np nr nk machine pc reg pub exit rom advice cfg raw enter same
    exact Procedure.Exec.then book scans machine pc reg pub exit rom advice cfg raw enter same,?_,?_,@cheap_seq w _ _ (@DescentStaticWordColumn.cheap w base (literal b) 56)
    (@program_cheap w (ProbeStage.Native.columns H out es))⟩
  · intro j r
    have index : j.val<es.length := by rw [n];exact j.isLt
    have stored:=ProbeStage.Native.columns_read es mid le_rfl indexed j.val index r
    have field : es[j.val]'index=body L base j := by simp only [es,fields,List.getElem_ofFn]
    rw [field] at stored
    exact stored.trans (body_read L x m seen ready small early word j r)
  · intro u left right
    exact (ProbeStage.Native.columns_frame es mid (by simpa only [n] using right)).trans
      (DescentStaticWordColumn.frame base 56 (literal b) m u left)

theorem any (b H base out : ℕ) (m : Memory w)
    (ready : L.All (Expr.Fits w base)) (early : base+56≤out) (room : out+K*H<2^w) :
    let last:=output L b H base out m
    (code L b w H base out).Exec m last (ticks L H base out) ∧
      (∀u,u<base ∨ base+56≤u→u<out ∨ out+K*H≤u→last u=m u) ∧ CheapCode (code L b w H base out) := by
  let es:=fields L base
  let mid:=mounted b base m
  have n : es.length=K := List.length_ofFn
  have word : out<2^w := (Nat.le_add_right ..).trans_lt room
  have indexed : ∀e∈es,e.Fits w out := by
    intro e h
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp h
    exact body_fits L base out early word ready j
  have book : (DescentStaticWordColumn.program w base (literal b) 56).Exec m mid (4+10*56) :=
    DescentStaticWordColumn.mount base 56 (literal b) m (early.trans_lt word)
  have scans : (ProtocolRAM.program w (ProbeStage.Native.columns H out es)).Exec mid
      (result (ProbeStage.Native.columns H out es) mid) (clock (ProbeStage.Native.columns H out es)) :=
    ProbeStage.Native.columns_exec es mid (ProbeStage.Native.columns_safe (n:=H) es le_rfl indexed
    (by simpa only [n] using room))
  refine ⟨by
    intro np nr nk machine pc reg pub exit rom advice cfg raw enter same
    exact Procedure.Exec.then book scans machine pc reg pub exit rom advice cfg raw enter same,?_,@cheap_seq w _ _ (@DescentStaticWordColumn.cheap w base (literal b) 56)
    (@program_cheap w (ProbeStage.Native.columns H out es))⟩
  · intro u left right
    exact (ProbeStage.Native.columns_frame es mid (by simpa only [n] using right)).trans
      (DescentStaticWordColumn.frame base 56 (literal b) m u left)

def opWork (U : ℕ) := 1+4*((2*U+3+4*(2*U+2))+1)
def workLimit (U : ℕ) := U+3+(1+7*(max (U+1) (opWork U)+6))

theorem body_work (U base : ℕ) (bounded : L.All (fun e=>e.work≤U)) (j : Fin K) :
    (body L base j).work≤workLimit U := by
  have ranked (e : Expr) (cost : e.work≤U) : (calculate L.roster e).work≤opWork U :=
    DescentResetStemCompactOrder.rank_work L.roster e U bounded.roster cost
  let lim:=max (U+1) (opWork U)
  have hi (i : Fin 7) : (digitsAt L j i).work≤lim := by
    have one:=le_max_left (U+1) (opWork U)
    have two:=le_max_right (U+1) (opWork U)
    fin_cases i
    · exact (Nat.le_add_left ..).trans one
    · exact (ranked _ (bounded.src j)).trans two
    · exact (ranked _ (bounded.dst j)).trans two
    · exact (ranked _ bounded.here).trans two
    · exact (bounded.absent j).trans ((Nat.le_succ _).trans one)
    · exact (bounded.core j).trans ((Nat.le_succ _).trans one)
    · exact (Nat.le_add_left ..).trans one
  have row:=work_total (fun i=>Expr.lookup (bank base i) (digitsAt L j i)) (lim+5)
    (fun i=>Nat.add_le_add_right (hi i) 5) (List.finRange 7)
  simp only [List.length_finRange] at row
  have live:=bounded.live j
  change (L.live j).work+1+1+_+1≤_
  dsimp only [workLimit,lim] at *
  omega

theorem ticks_le (U H base out : ℕ) (bounded : L.All (fun e=>e.work≤U)) :
    ticks L H base out≤(4+10*56)+(4+K*(4+H*(2*workLimit U+4))) := by
  apply Nat.add_le_add_left
  apply le_trans (ProbeStage.Native.columns_clock _ _ (workLimit U) _ ?_)
  · simp only [fields,List.length_ofFn,le_refl]
  · intro e h
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp h
    exact body_work L U base bounded j

theorem names_le (b w U H base out : ℕ) (bounded : L.All (fun e=>e.work≤U)) :
    DescentStaticWordColumn.names (code L b w H base out)≤
      15*(56+1)+(15+K*(11+4*workLimit U)) := by
  rw [code,DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_mount]
  apply Nat.add_le_add_left
  apply le_trans (ProbeStage.Native.columns_text _ _ _ (workLimit U) _ ?_)
  · simp only [fields,List.length_ofFn,le_refl]
  · intro e h
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp h
    exact body_work L U base bounded j


end
end Hierarchy.DescentResetStemDescriptorRAM

end OAI
