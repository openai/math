import OAI.ThreeFlat.RAM.HistoryMotifJoin
import OAI.ThreeFlat.RAM.HistoryPhysicalFamilies
import OAI.ThreeFlat.RAM.HistoryPartyPairExec
import OAI.ThreeFlat.RAM.HistoryGatherExecution
import OAI.ThreeFlat.Diagonal.RefreshSiteTree
import OAI.ThreeFlat.Diagonal.RefreshRecordImage
import OAI.ThreeFlat.Diagonal.TickWorkspace

namespace OAI
/-! # Refresh party batch reads and cost bounds -/
set_option quotPrecheck false

namespace ThreeFlat.RAM.HistoryRefreshEmitter

set_option maxRecDepth 6000

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure
open Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree HistoryPartyBatchExec
open HistoryBoundedJoin HistoryMotifJoin HistoryPartyBatch HistoryBoundedBody BitNetwork.Ordered
open scoped BigOperators Classical Fin.CommRing

noncomputable section
variable {W p a b : ℕ} {F : Type*}

def rawParty (A : HistoryGatherBody.Layout) (motif party : ℕ) :=
  withParty (withMotif A motif) party

def rawArm (A : HistoryGatherBody.Layout) (i : ℕ) :=
  withParty (withMotif A 0) i

/-- The raw incident mask and motif count determine the party batch's actual branch. -/
theorem batch_occupied (A : HistoryGatherBody.Layout) (mem : Memory W)
    (winner : Fin A.party.parties) (j : ℕ)
    (one : 0<numeric mem (kernel (rawArm A j).party (numeric mem)+3))
    (mask : numeric mem (incident (rawArm A j).party (numeric mem)+5)=2^winner.val) :
    occupied (rawArm A j).party (numeric mem) ↔ j=winner.val := by
  change (0<_ ∧ _/2^j%2=1) ↔ _
  rw [and_iff_right one,mask]
  have same : decide (2^winner.val/2^j%2=1)=decide (winner.val=j) := by
    rw [←Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_two_pow]
  have e := congrArg (fun b : Bool=>b=true) same
  exact (show (2^winner.val/2^j%2=1) ↔ winner.val=j by simpa only [decide_eq_true_eq] using Iff.of_eq e).trans eq_comm

theorem gather_occupied (A : HistoryGatherBody.Layout) (mem : Memory W)
    (winner j : Fin A.party.parties)
    (one : 0<(HistoryGatherBody.wordAt mem (HistoryGatherBody.selected (rawArm A j.val) mem).kernel 3).val)
    (mask : (HistoryGatherBody.wordAt mem (HistoryGatherBody.selected (rawArm A j.val) mem).incident 5).val=2^winner.val)
    (wide : 2^A.party.parties<2^W) (two : 2<2^W) :
    HistoryGatherBody.partyActive (rawArm A j.val) mem ↔ j=winner := by
  rw [HistoryGatherBody.partyActive_iff _ _ (by exact Nat.two_pow_pos W)
    ((Nat.pow_le_pow_right (by decide : 0<2) j.isLt.le).trans_lt wide) two]
  change (0<_ ∧ _ ) ↔ _
  rw [and_iff_right one,mask,Nat.testBit_two_pow,decide_eq_true_eq]
  exact ⟨fun h=>Fin.ext h.symm,fun h=>by subst j;rfl⟩

/-- The group join obtains child zero from the elected raw party's pair bank. -/
theorem single_role (A : HistoryGatherBody.Layout) (mem : Memory W) (winner : Fin A.party.parties)
    (live : (A.party.motif : Word W)<HistoryGatherBody.wordAt mem (HistoryGatherBody.selected A mem).kernel 3)
    (mask : (HistoryGatherBody.wordAt mem (HistoryGatherBody.selected A mem).incident 5).val=2^winner.val) :
    Fintype.card {j : Fin A.party.parties // selectedBit A mem j.val}=1 ∧ role A mem 0=winner.val := by
  have pick (i : Fin A.party.parties) : selectedBit A mem i.val ↔ i=winner := by
    simp only [selectedBit,live,true_and,mask,Nat.testBit_two_pow,decide_eq_true_eq]
    exact ⟨fun h=>Fin.ext h.symm,fun h=>by subst i;rfl⟩
  let eqv : {j : Fin A.party.parties // selectedBit A mem j.val} ≃ Unit :=
    ⟨fun _=>(),fun _=>⟨winner,(pick winner).2 rfl⟩,
      fun j=>Subtype.ext ((pick j.val).1 j.property).symm,fun i=>by cases i;rfl⟩
  have count : Fintype.card {j : Fin A.party.parties // selectedBit A mem j.val}=1 := by
    simpa using Fintype.card_congr eqv
  refine ⟨count,?_⟩
  rw [role,dite_eq_left (by omega : 0<Fintype.card {j : Fin A.party.parties // selectedBit A mem j.val})]
  apply congrArg Fin.val
  have positive : 0 < Fintype.card {j : Fin A.party.parties // selectedBit A mem j.val} := by omega
  exact (pick _).1 ((Diagonal.HistoryMaskOrder.order (fun j : Fin A.party.parties => selectedBit A mem j.val)) ⟨0, positive⟩).property

def emptyKind : HistoryPartyHeader.Kind := ⟨0,0,0,0,0,0,0⟩

/-- Both dummy pointers address zero words actually written in the seed stage. -/
theorem inactive_header (A : HistoryPartyBatch.Layout) (ck : Bool) (m : Memory W)
    (room : A.seed+37<2^W) (absent : ¬occupied A (numeric m)) :
    let X : HistoryPartyBatchExec.Build W := ⟨A,ck,emptyKind,m⟩
    info X.table=⟨dest A ck (numeric m A.cursor-1) 0,0,0,0⟩ := by
  let X : HistoryPartyBatchExec.Build W := ⟨A,ck,emptyKind,m⟩
  have k : X.bootImage (A.seed+18)=0 := by
    rw [HistoryPartyBatchExec.Build.bootImage,HistoryPartyBootExec.output_at _ _ _ room,ite_eq_right (by omega),ite_eq_right (by omega)]
    exact HistoryPartyBootExec.seedMemory_at A ck m (18:Fin 37)
  have z : numeric X.bootImage (A.seed+15+3)=0 := by
    change (X.bootImage _).val=0
    rw [show A.seed+15+3=A.seed+18 by omega,k]
    rfl
  change info X.table=_
  cases ck <;> simp [X,HistoryPartyBatchExec.Build.table,HistoryPartyBatchExec.Build.regs,registers,absent,emptyKind,HistoryPartyHeader.batch,
    info] at z ⊢ <;> simp_all [HistoryPartyBatchExec.Build.bootImage]

/-- An absent raw arm still runs the two native batch preparations and the pair procedure. -/
def nullTree (F : Type*) : Tree F 0 := .join 0 0 (fun i=>i.elim0) (fun i=>i.elim0) (fun i=>i.elim0)

@[simp] theorem null_rows : (nullTree F).rows=0 := by simp [nullTree,Tree.rows]
@[simp] theorem null_bits : (nullTree F).bits=0 := by simp [nullTree,Tree.bits]

variable [CommRing F]

def vacantChecks (A : HistoryPartyBatch.Layout) (input : Memory W) : HistoryPartyBatchExec.Build W :=
  ⟨A,true,emptyKind,input⟩

def vacantPayload (A : HistoryPartyBatch.Layout) (input : Memory W) : HistoryPartyBatchExec.Build W :=
  ⟨A,false,emptyKind,(vacantChecks A input).published []⟩



section VacantBatch
variable (A : HistoryPartyBatch.Layout) (ck : Bool) (input : Memory W)
local notation "X" => (⟨A,ck,emptyKind,input⟩:HistoryPartyBatchExec.Build W)

private theorem zero_seed_field (room : A.seed+37<2^W) (i : Fin 13) :
    numeric (X).bootImage (A.seed+15+i.val)=0 := by
  let j:Fin 37:=⟨15+i.val,by have:=i.isLt;omega⟩
  have addr:A.seed+15+i.val=A.seed+j.val:=by dsimp [j];omega
  change (HistoryPartyBootExec.output A ck input _).val=0
  rw [HistoryPartyBootExec.output_at _ _ _ room,ite_eq_right (by omega),ite_eq_right (by omega),addr,
    HistoryPartyBootExec.seedMemory_at]
  fin_cases i <;> rfl

/-- The absent branch reads only its seed sentinel, the first LUT page, and the zero-power
entry of the permanent compactor count table. No jobs are decoded or emitted. -/
theorem vacant_source (absent : ¬occupied A (numeric input))
    (seed : A.seed+37<2^W) (header : A.batch+26<2^W)
    (seedOrder : A.seed+37≤A.batch) (headerOrder : A.batch+26≤A.commands) (order : A.commands≤A.arguments)
    (args : A.arguments<2^W) (wordSize : 23<2^W)
    (atMotif : A.motif<2^W)
    (probes : ∀ h,HistoryPartyBootExec.SeedRead A ck (numeric input) h→(h<A.seed ∨ A.seed+37≤h) ∧ h<2^W)
    (mask : A.motif<numeric input (kernel A (numeric input)+3)→2^A.party<2^W)
    (regs : ∀ j:Fin 11,(X).regs.words j<2^W)
    (lut : A.lutBase+1<2^W) (counts : A.countBase+1<2^W)
    (lutAway : A.lutBase+2≤A.batch ∨ A.batch+26≤A.lutBase)
    (countsAway : A.countBase+2≤A.batch ∨ A.batch+26≤A.countBase)
    (destFit : (X).target+4<2^W) (destAway : (X).target+4≤A.seed ∨ A.batch+26≤(X).target) : (X).Source [] := by
  have wordWidth : 0 < W := by
    by_contra! zero
    have hw : W = 0 := Nat.eq_zero_of_le_zero zero
    simp [hw] at wordSize
  have z : (X).count=0:=by simp [HistoryPartyBatchExec.Build.count,children,HistoryPartyBatch.copies,kinds,absent]
  have ext : HistoryPartyBootExec.extent A (numeric input)=0:=by
    simp [HistoryPartyBootExec.extent,HistoryPartyBatch.copies,digit,absent]
  have ext' : HistoryPartyBootExec.extent A (HistoryPartyBootExec.raw input)=0:=ext
  have dyadic : numeric (X).bootImage (A.seed+1+1)=0 := by
    change (HistoryPartyBootExec.output A ck input _).val=_
    rw [HistoryPartyBootExec.output_at _ _ _ seed,ite_eq_right (by omega),ite_eq_left (by omega),ext']
    simp
  have width : numeric (X).bootImage (A.seed+1+2)=1 := by
    change (HistoryPartyBootExec.output A ck input _).val=_
    rw [HistoryPartyBootExec.output_at _ _ _ seed,ite_eq_left (by omega),ext']
    simp [wordWidth]
  have sentinel (i:Fin 13) := zero_seed_field A ck input seed i
  have mix : numeric (X).bootImage (A.seed+15+3)=0:=sentinel 3
  have hist : numeric (X).bootImage (A.seed+15+1)=0:=sentinel 1
  have grid (j:Fin 7) : numeric (X).bootImage ((X).regs.grid+j.val)=emptyKind.words j := by
    have addr : (X).regs.grid+j.val=A.seed+15+((6+j.val:ℕ)):=by
      change (if occupied A (numeric input) then shape A (numeric input) else A.seed+21)+j.val=_
      rw [ite_eq_right absent];omega
    rw [addr,sentinel ⟨6+j.val,by have:=j.isLt;omega⟩]
    fin_cases j <;> rfl
  have probesProtected : HeaderProtected A (X).regs emptyKind ck (X).bootImage := by
    constructor
    · intro j;left;have:=j.isLt;omega
    · intro j;left;change (if occupied A (numeric input) then _ else A.seed+21)+j.val<A.batch
      rw [ite_eq_right absent];have:=j.isLt;omega
    · intro j;left;change (if occupied A (numeric input) then _ else A.seed+15)+j.val<A.batch
      rw [ite_eq_right absent];have:=j.isLt;omega
    · intro j;left;change A.seed+1+j.val<A.batch;have:=j.isLt;omega
    · intro j;cases ck <;> change A.lutBase+A.lutStride*0+j.val<_ ∨ _≤A.lutBase+A.lutStride*0+j.val <;>
        have hz:=j.isLt <;> omega
    · intro j
      change A.countBase+2*numeric (X).bootImage (A.seed+1+1)+j.val<A.batch ∨
        A.batch+26≤A.countBase+2*numeric (X).bootImage (A.seed+1+1)+j.val
      rw [dyadic];have:=j.isLt;omega
  have access : HistoryPartyHeader.ReadRoom W (X).regs emptyKind ck (numeric (X).bootImage) := by
    constructor
    · change (if occupied A (numeric input) then _ else A.seed+21)+6<2^W;rw [ite_eq_right absent];omega
    · change (if occupied A (numeric input) then _ else A.seed+15)+3<2^W;rw [ite_eq_right absent];omega
    · change A.seed+1+2<2^W;omega
    · cases ck <;> simpa [HistoryPartyBatchExec.Build.regs,registers,emptyKind] using lut
    · change A.countBase+2*numeric (X).bootImage (A.seed+1+1)+1<2^W;rw [dyadic];omega
  have lookupSize : ∀ j : ℕ,numeric (X).bootImage j<2^W := fun j=>((X).bootImage j).isLt
  have bounds (j:Fin 26) : (X).table.words j<2^W := by
    have stream := regs 1
    have maps := regs 2
    have lutStride:=regs 7
    have comp:=regs 8
    change dest A ck (numeric input A.cursor-1) 0<2^W at stream
    change A.maps<2^W at maps
    change A.lutStride<2^W at lutStride
    change A.compBase<2^W at comp
    cases ck <;> fin_cases j <;>
      simp [HistoryPartyBatchExec.Build.table,HistoryPartyBatchExec.Build.regs,emptyKind,
        HistoryBatchTape.Header.words,HistoryPartyHeader.batch,registers,absent,dyadic,width,mix,hist] at * <;>
      first | exact lookupSize _ | omega
  refine ⟨seed,fun h k=>(probes h k).1,atMotif,fun h k=>(probes h k).2,mask,?_,regs,grid,header,probesProtected,access,
    wordSize,?_,?_,bounds,⟨seedOrder,headerOrder,?_⟩,?_,by simp [HistoryReadyTape.Away],
    by simp [HistoryReadyTape.Away],by simp [HistoryReadyTape.Away],by simp [HistoryReadyTape.Away],
    destFit,destAway⟩
  · rw [ext];simp;omega
  · rw [z];simp;omega
  · rw [z];simpa using args
  · rw [z];simpa using order
  · intro _ i _
    exact (Nat.not_lt_zero i.val (i.isLt.trans_eq z)).elim

end VacantBatch

section ElectedReads
open HistoryPartySpecialization
variable {K : Type} [CommRing K] [Fintype K] {z ar H : ℕ}
  (stage : HistoryPartyBatch.Layout) (kind : HistoryPartyHeader.Kind)
  (m : Memory W) (ck : Bool) (L : HistoryStaticArchive.Catalog K z ar)
  (r d : ℕ) (t : Fin (H+1))
local notation "Y" => (⟨stage,ck,kind,m⟩:HistoryPartyBatchExec.Build W)
local notation "raw" => numeric m

/-- Both native height-counter words are no larger than the published compactor
resource bound, including height zero. -/
theorem compactor_counts_le (K : Type*) [CommRing K] [Fintype K] {H : ℕ} (m:Fin (H+1)) (j:Fin 2) :
    HistoryCompactorCounts.words K m j≤StableCompactNativeBudget.budget m.val := by
  have hm:=HistoryCompactorCounts.shape K m 0
  change (Routing.StableCompactNative.network K m.val).cells=_ ∧ (Routing.StableCompactNative.network K m.val).internal=_ at hm
  have cap:=StableCompactNativeBudget.capacities K m.val
  have one:=Nat.two_pow_pos m.val
  fin_cases j
  · change HistoryCompactorCounts.words K m 0 ≤ StableCompactNativeBudget.budget m.val
    have h:=Nat.le_mul_of_pos_right (HistoryCompactorCounts.words K m 0) one
    omega
  · change HistoryCompactorCounts.words K m 1 ≤ StableCompactNativeBudget.budget m.val
    have h:=Nat.le_mul_of_pos_right (HistoryCompactorCounts.words K m 1) one
    omega

/-- All 26 physically emitted batch fields fit from the static kind sizes, the
actual capacity of the instance, and the final compactor-page address. -/
theorem elected_header_fits (R : HistoryPartyHeader.Registers) (B : HistoryPartyHeader.Kind)
    (mem : Memory W) (ck : Bool) (v:ℕ) (positive:2≤v) (cubic : 40*v^3<2^W)
    (rSize : numeric mem (R.incident+3)≤v) (kSize : ∀ j,B.words j≤v)
    (dyadic : numeric mem (R.dyadic+2)≤v)
    (counter : ∀ j:Fin 2,numeric mem (R.countBase+2*numeric mem (R.dyadic+1)+j.val)≤v)
    (registers : ∀ j,R.words j<2^W)
    (page : R.compBase+R.compStride*numeric mem (R.dyadic+1)<2^W) (j:Fin 26) :
    (HistoryPartyHeader.batch R B (numeric mem) ck).words j<2^W := by
  let r:=numeric mem (R.incident+3)
  let N:=numeric mem (R.dyadic+2)
  let count:=R.countBase+2*numeric mem (R.dyadic+1)
  have ports : B.ports≤v:=kSize 0
  have letters : B.letters≤v:=kSize 1
  have code : B.codeBits≤v:=kSize 2
  have tile : B.tileHead≤v:=kSize 3
  have digs : B.digit≤v:=kSize 4
  have tpage : B.tilePage≤v:=kSize 5
  have spage : B.selectorPage≤v:=kSize 6
  have rsize : r≤v:=rSize
  have dim : v≤v*v:=Nat.le_mul_of_pos_right _ (by omega)
  have dim' : v*v≤v^3:=by simpa [pow_succ,pow_two] using (Nat.le_mul_of_pos_right (v*v) (by omega : 0<v))
  have sb:=Nat.mul_le_mul ports code
  have pe:=Nat.mul_le_mul ports digs
  have rd:=Nat.mul_le_mul rSize digs
  have rb:=Nat.mul_le_mul rSize tile
  have rs:=Nat.mul_le_mul rSize letters
  have rSel : r*(B.ports*B.codeBits)≤v^3:=by simpa [pow_succ,pow_two,Nat.mul_assoc] using Nat.mul_le_mul rsize sb
  have rBank : B.ports*(r*B.digit)≤v^3:=by simpa [pow_succ,pow_two,Nat.mul_assoc] using Nat.mul_le_mul ports rd
  have count0 : numeric mem count≤v:=by simpa [count] using counter 0
  have count1 : numeric mem (count+1)≤v:=counter 1
  have nr:=Nat.mul_le_mul dyadic count0
  have nb:=Nat.mul_le_mul dyadic count1
  have arg : R.arguments<2^W:=registers 0
  have stream : R.streams<2^W:=registers 1
  have maps : R.maps<2^W:=registers 2
  have lut : R.lutBase<2^W:=registers 6
  have stride : R.lutStride<2^W:=registers 7
  have word_fit (x : ℕ) : numeric mem x < 2^W := (mem x).isLt
  cases ck <;> fin_cases j <;>
    simp only [HistoryPartyHeader.batch,HistoryBatchTape.Header.words,Bool.false_eq_true,ite_false,ite_true,
      Bool.toNat_false,Bool.toNat_true,Matrix.cons_val_zero,Fin.reduceFinMk,
      Matrix.cons_val] <;>
    first | exact word_fit _ | exact page | exact arg | exact stream | exact maps | exact lut | exact stride |
      (dsimp [r,N,count] at rsize rd rb rs rSel rBank nr nb count0 count1;omega)

/-- Read the live batch's power and copies from its real dyadic boot as well as
the first two lanes of each mounted LUT and the selected compactor shape. -/
theorem elected_reads (active : occupied stage raw)
    (count : raw (incident stage raw+3)=r) (digit : raw (shape stage raw+4)=d)
    (level : t.val=Diagonal.HistogramTileNetwork.siteHeight r d) (size : 2^t.val<2^W)
    (seed : stage.seed+37<2^W) (step : stage.lutStride=HistoryStaticArchive.stride ar)
    (strideFit : HistoryStaticArchive.stride ar≤2^W)
    (values : ∀ j:Fin 7,raw (shape stage raw+j.val)=kind.words j)
    (slots : L.Stores stage.lutBase m)
    (counts : ∀ i:Fin (HistoryCompactorCounts.size H),m (stage.countBase+i.val)=HistoryCompactorCounts.data (w:=W) K H i)
    (shapeRoom : ∀ j,HistoryCompactorCounts.words K t j<2^W)
    (incidentFree : incident stage raw+4 ≤ stage.seed ∨ stage.seed+37 ≤ incident stage raw)
    (kindFree : shape stage raw+7 ≤ stage.seed ∨ stage.seed+37 ≤ shape stage raw)
    (fixedFree : stage.lutBase+HistoryStaticArchive.size z ar ≤ stage.seed ∨ stage.seed+37 ≤ stage.lutBase)
    (countsFree : stage.countBase+HistoryCompactorCounts.size H ≤ stage.seed ∨ stage.seed+37 ≤ stage.countBase) :
    Reads (Y).regs (numeric (Y).bootImage) L r t ∧
      ∀ j:Fin 7,numeric (Y).bootImage ((Y).regs.grid+j.val)=kind.words j := by
  have kept (a : ℕ) (free : a < stage.seed ∨ stage.seed+37 ≤ a) : numeric (Y).bootImage a=raw a :=
    congrArg Fin.val (HistoryPartyBootExec.output_outside stage ck m seed a free)
  have dyad : (Y).regs.dyadic=stage.seed+1:=rfl
  have it : (Y).regs.incident=incident stage raw:=ite_eq_left active
  have sh : (Y).regs.grid=shape stage raw:=ite_eq_left active
  have height : Nat.clog 2 (HistoryPartyBootExec.extent stage (HistoryPartyBootExec.raw m))=t.val:=by
    change Nat.clog 2 (max (HistoryPartyBatch.copies stage raw)
      (HistoryPartyBatch.copies stage raw * HistoryPartyBatch.digit stage raw)) = _
    simpa only [HistoryPartyBatch.copies,HistoryPartyBatch.digit,ite_eq_left active,count,digit,
      Diagonal.HistogramTileNetwork.siteHeight]
      using level.symm
  have le : t.val<2^t.val:=Nat.lt_two_pow_self
  have get (i:Fin z) (j:Fin 2) :
      numeric (Y).bootImage ((Y).regs.lutBase+(Y).regs.lutStride*i.val+j.val)=L.page i j.val:=by
    let span:=HistoryStaticArchive.stride ar
    have pos : 2 ≤ span := Nat.le_add_right _ _
    have digitFits : j.val < span := j.isLt.trans_le pos
    let k : Fin span := ⟨j.val,digitFits⟩
    have total : i.val*span+j.val < HistoryStaticArchive.size z ar := by
      have a : (i.val+1)*span ≤ z*span := Nat.mul_le_mul_right span i.isLt
      rw [Nat.add_mul,one_mul] at a
      exact (Nat.add_lt_add_left digitFits _).trans_le a
    have f := L.rows_fit i
    have cellsFit : (L.rows i).cells < 2^W := by omega
    have fits : L.page i j.val < 2^W := by
      fin_cases j
      · change (L.rows i).internal<_
        calc
          _ = 2^(L.arity i) := Diagonal.ConstantKernelLUT.network_internal (L.coeff i)
          _ ≤ 2^(L.arity i)*(L.arity i+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
          _ = (L.rows i).cells := (Diagonal.ConstantKernelLUT.network_cells (L.coeff i)).symm
          _ < 2^W := cellsFit
      · exact cellsFit
    have word := L.read i k stage.lutBase m slots
    have value : raw (stage.lutBase+(i.val*span+j.val))=L.page i j.val :=
      (congrArg Fin.val word).trans (Fin.val_cast_of_lt fits)
    change numeric (Y).bootImage (stage.lutBase+stage.lutStride*i.val+j.val)=_
    rw [step,show stage.lutBase+HistoryStaticArchive.stride ar*i.val+j.val=stage.lutBase+(i.val*span+j.val) by
      dsimp [span];rw [Nat.mul_comm (HistoryStaticArchive.stride ar) i.val,Nat.add_assoc]]
    exact (kept (stage.lutBase+(i.val*span+j.val)) (by omega)).trans value
  refine ⟨⟨?_,?_,?_,get,?_⟩,?_⟩
  · rw [it]
    exact (kept (incident stage raw+3) (by omega)).trans count
  · rw [dyad];change (HistoryPartyBootExec.output stage ck m (stage.seed+2)).val=t.val
    rw [HistoryPartyBootExec.output_at _ _ _ seed,ite_eq_right (by omega),ite_eq_left rfl,height,Fin.val_cast_of_lt (by omega)]
  · rw [dyad];change (HistoryPartyBootExec.output stage ck m (stage.seed+3)).val=2^t.val
    rw [HistoryPartyBootExec.output_at _ _ _ seed,ite_eq_left rfl,height,Fin.val_cast_of_lt size]
  · intro j
    have total : 2*t.val+j.val<HistoryCompactorCounts.size H:=by
      have:=t.isLt;have:=j.isLt;unfold HistoryCompactorCounts.size;omega
    let q:Fin (HistoryCompactorCounts.size H):=⟨2*t.val+j.val,total⟩
    change numeric (Y).bootImage (stage.countBase+2*t.val+j.val)=_
    rw [Nat.add_assoc]
    have word := (counts q).trans (HistoryCompactorCounts.data_at K t j)
    exact (kept (stage.countBase+q.val) (by change stage.countBase+(2*t.val+j.val) < stage.seed ∨
      stage.seed+37 ≤ stage.countBase+(2*t.val+j.val); omega)).trans
      ((congrArg Fin.val word).trans (Fin.val_cast_of_lt (shapeRoom j)))
  · intro j
    rw [sh]
    exact (kept (shape stage raw+j.val) (by have h := j.isLt; omega)).trans (values j)

/-- Boot only updates the seed words, so the actual selected histogram address and
each original quota remain available in the elected checker. -/
theorem elected_histogram (active : occupied stage raw) (seed : stage.seed+37<2^W)
    (hist alphabet : ℕ) (z : Fin alphabet→ℕ) (read : raw (incident stage raw+1)=hist)
    (values : ∀ j:Fin alphabet,raw (hist+j.val)=z j)
    (incidentFree : incident stage raw+4 ≤ stage.seed ∨ stage.seed+37 ≤ incident stage raw)
    (histFree : hist+alphabet ≤ stage.seed ∨ stage.seed+37 ≤ hist) :
    ∀ j:Fin alphabet,numeric (Y).bootImage (numeric (Y).bootImage ((Y).regs.incident+1)+j.val)=z j := by
  have kept (x:ℕ) (free : x < stage.seed ∨ stage.seed+37 ≤ x) : numeric (Y).bootImage x=raw x:=
    congrArg Fin.val (HistoryPartyBootExec.output_outside stage ck m seed x free)
  have it : (Y).regs.incident=incident stage raw:=ite_eq_left active
  have pointer : numeric (Y).bootImage ((Y).regs.incident+1) = hist := by
    rw [it, kept (incident stage raw+1) (by omega), read]
  intro j
  rw [pointer, kept (hist+j.val) (by have := j.isLt; omega), values]

end ElectedReads

section MountedElected
open HistoryStageBody.Physical HistoryPartySpecialization
variable {K:Type} [Field K] [Fintype K] (B:Diagonal.PhysicalStage.Block K)
  {height start n parties:ℕ} {m:Memory W} (image:Mounted B height W start m)
local notation "ar" => arity B
local notation "lib" => HistoryStaticArchive.all K ar
local notation "lut0" => start+StableCompactROMNative.size height
local notation "cnt0" => start+StableCompactROMNative.size height+staticSize B

include image in
/-- The two ROM images used by the ready batch are the immutable scalar and
compactor pages at their literal offsets in the archived program image. -/
theorem mounted_batch_archive :
    HistoryPartyTapeRun.Archive (D:=height) (fun table : (Fin 3→Bool)→K=>(Fintype.equivFin _ table).val)
      lib lut0 start m:=by
  refine ⟨stored_scalar B image.words,?_⟩
  intro q
  have cap:q.val<libraryWords B height:=by unfold libraryWords;have:=q.isLt;omega
  simpa only [data,dite_eq_left q.isLt] using image.words ⟨q.val,cap⟩

variable {grid:Grid K} {pre tail:List (Grid K)} {cells:Fin n→Fin parties→Party K}
  (gridAt:grids B=pre++grid::tail) (rowsAt:grid.rows=HistoryStageBody.Physical.grid cells)
  (i:Fin n) (j:Fin parties) (stage:HistoryPartyBatch.Layout) (ck:Bool) (r:ℕ) (t:Fin (height+1))
local notation "party" => cells i j
local notation "kind" => (party).kind ar
local notation "ptr" => (grid.family (Mounted.base B height start pre)).kinds+7*(i.val*parties+j.val)
local notation "Y" => (⟨stage,ck,kind,m⟩:HistoryPartyBatchExec.Build W)

include image gridAt rowsAt in
/-- The live batch reads a real selected physical archive row and the two tables
stored before it in the same mounted image. -/
theorem mounted_elected_reads
    (active:occupied stage (numeric m)) (incidentCount:numeric m (incident stage (numeric m)+3)=r)
    (shapeId:shape stage (numeric m)=ptr) (level:t.val=Diagonal.HistogramTileNetwork.siteHeight r (party).maxDigit)
    (size:2^t.val<2^W) (seed:stage.seed+37<2^W) (width:HistoryStaticArchive.stride ar≤2^W)
    (words:∀ a:Fin 7,(kind).words a<2^W) (work:StableCompactNativeBudget.budget t.val<2^W)
    (fixedBase:stage.lutBase=lut0) (fixedStep:stage.lutStride=HistoryStaticArchive.stride ar) (countsBase:stage.countBase=cnt0)
    (incidentFree:incident stage (numeric m)+4 ≤ stage.seed ∨ stage.seed+37 ≤ incident stage (numeric m))
    (kindFree:ptr+7 ≤ stage.seed ∨ stage.seed+37 ≤ ptr)
    (fixedFree:lut0+staticSize B ≤ stage.seed ∨ stage.seed+37 ≤ lut0)
    (countsFree:cnt0+HistoryCompactorCounts.size height ≤ stage.seed ∨ stage.seed+37 ≤ cnt0) :
    Reads (Y).regs (numeric (Y).bootImage) lib r t ∧ ∀ a:Fin 7,numeric (Y).bootImage ((Y).regs.grid+a.val)=(kind).words a := by
  have row (a:Fin 7) : numeric m (shape stage (numeric m)+a.val)=(kind).words a:=by
    rw [shapeId,numeric,image.kindAt gridAt rowsAt i j a,Fin.val_cast_of_lt (words a)]
  have digit : numeric m (shape stage (numeric m)+4)=(party).maxDigit:=row 4
  exact elected_reads stage kind m ck lib r (party).maxDigit t active incidentCount digit level size seed fixedStep
    width row (fixedBase.symm ▸ stored_scalar B image.words) (countsBase.symm ▸ stored_counts B image.words)
    (fun a=>(compactor_counts_le K t a).trans_lt work) incidentFree (shapeId.symm ▸ kindFree)
    (fixedBase.symm ▸ fixedFree) (countsBase.symm ▸ countsFree)

end MountedElected

section Batch
open HistoryPartyTapeRun HistoryCompiledRows Diagonal.HistoryContraction.Tree.BatchRows
variable [Fintype F] {z s h l r : ℕ} (X : HistoryPartyBatchExec.Build W)
  (arity : Fin (l+r)→ℕ) (nets : ∀ i,BitNetwork F (arity i)) (wire : ∀ i,Fin (arity i)→BitSource h p)
  (id : ((Fin 3→Bool)→F)→ℕ) (lib : HistoryStaticArchive.Catalog F z s) (page : Fin z)
  {depth : ℕ} (power : Fin (depth+1)) (logical fixedBase compactBase : ℕ)
  (hl : X.table.r=l) (hr : X.table.s=r)
local notation "idx" => Fin.cast (congrArg₂ Nat.add hl hr)
local notation "N" => fun i=>nets (idx i)
local notation "wireAt" => fun i=>wire (idx i)
local notation "jobs" => HistoryPartyTapeRun.jobs (w:=W) X.table N wireAt id

/-- Physical tape ranges for one of the two elected batches. The catalogue and the
shortened compactor are the mounted ones, and the archive ranges may lie above scratch. -/
structure BatchRoom : Prop where
  seed : X.Source jobs
  count : X.table.r+X.table.s=X.count
  quota : X.table.checks=true → 0<X.table.s → X.table.hist+X.table.s≤X.layout.batch ∨
    X.layout.commands+21*X.count≤X.table.hist
  space : Space (z:=z) (B:=s) (D:=depth) X.table N wireAt id fixedBase compactBase X.ctrl X.layout.commands
  archive : Archive (D:=depth) id lib fixedBase compactBase X.input
  fixedAway : fixedBase+HistoryStaticArchive.size z s≤X.layout.seed ∨ X.layout.arguments+23*X.count≤fixedBase
  compactAway : compactBase+StableCompactROMNative.size depth≤X.layout.seed ∨ X.layout.arguments+23*X.count≤compactBase
  work : StableCompactNativeBudget.budget power<2^W
  pins : ∀ i,2+arity (idx i)<2^W
  metadata : ∀ i (row : Fin (nets (idx i)).cells) j,HistoryCompiledRows.metadata id (nets (idx i)) row j<2^W
  bankWidth : X.table.e*X.table.d<2^W
  stripe : X.table.r*X.table.d<2^W
  outputApart : X.target+4≤(info X.table).stream ∨ (info X.table).stream+4*(glue N wireAt).cells≤X.target

omit [CommRing F] [Fintype F] in
private theorem cast_glue {n₁ n₂ : ℕ} (e : n₁=n₂) {a₀ : Fin n₂→ℕ}
    (nets : ∀i,BitNetwork F (a₀ i)) (pins : ∀i,Fin (a₀ i)→BitSource h p) :
    glue (fun i=>nets (Fin.cast e i)) (fun i=>pins (Fin.cast e i))=glue nets pins := by
  cases e
  rfl

theorem batch_exec
    (model : Models X.table N wireAt id lib page power logical fixedBase compactBase (numeric X.bootImage))
    (sizes : Diagonal.HistoryContraction.Tree.BatchRows.Sizes nets X.table.left X.table.right)
    (pinsEq : X.table.parentPins=p) (bitsEq : X.table.shared=h)
    (room : BatchRoom X arity nets wire id lib power fixedBase compactBase hl hr) :
    (HistoryPartyBatch.procedure W X.layout X.checks).Exec X.input (X.published jobs) (X.cost jobs) ∧
    (∀ j : Fin 4,X.published jobs (X.target+j.val)=((info X.table).words j:Word W)) ∧
    Records id (Tree.batch nets wire).compile (info X.table).stream (X.published jobs) := by
  have shape:=shape_of_sizes X.table hl hr nets wire sizes pinsEq bitsEq
  have place:=placed_of_sizes X.table hl hr nets wire sizes
  have archive:=X.archive_at_tape id lib fixedBase compactBase room.seed.order room.seed.seedRoom
    room.archive room.fixedAway room.compactAway
  obtain ⟨exec,head,rows⟩ := X.complete N wireAt id lib page power logical fixedBase compactBase room.seed
    room.count model room.quota shape room.space archive room.work room.pins room.metadata room.bankWidth
    room.stripe place room.outputApart
  rw [cast_glue _ nets wire] at rows
  exact ⟨exec,head,rows⟩

private theorem sum_blocks (t : Fin (l+r)→ℕ) (x y : ℕ)
    (values : ∀ i,t i=if i.val<l then x else y) : ∑ i,t i=l*x+r*y := by
  rw [Fin.sum_univ_add]
  have left (i : Fin l) : t (i.castAdd r)=x := (values _).trans (ite_eq_left i.isLt)
  have right (i : Fin r) : t (Fin.natAdd l i)=y :=
    (values _).trans (ite_eq_right (by change ¬l+i.val<l;omega))
  simp [left,right]

include hl hr in
omit [CommRing F] [Fintype F] in
theorem batch_info (sizes : Diagonal.HistoryContraction.Tree.BatchRows.Sizes nets X.table.left X.table.right)
    (pinsEq : X.table.parentPins=p) (bitsEq : X.table.shared=h) :
    let T:=Tree.batch nets wire
    info X.table=⟨X.table.stream+4*T.rows,p,T.rows,T.bits⟩ := by
  have row := sum_blocks (fun i=>(nets i).cells) _ _ sizes.cells
  have bit := sum_blocks (fun i=>(nets i).internal) _ _ sizes.internal
  simp [info,Tree.batch,Tree.rows,Tree.bits,hl,hr,pinsEq,bitsEq,row,bit]

end Batch

private def tariffLayout : HistoryPartyBatch.Layout :=
  ⟨0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0⟩

private def rateBuild (ck : Bool) : HistoryPartyBatchExec.Build 0 := ⟨tariffLayout,ck,emptyKind,fun _=>0⟩

def batchRate (ck : Bool) := (rateBuild ck).staticCost

def gatherRate := HistoryPartyPairExec.overhead tariffLayout 0

/-- Fixed work per copy for the two leaf banks of one batch. -/
def batchUnits (lut groups factor digit pins : ℕ) :=
  2+groups+12*(2^lut*(lut+1)+groups*(64000*(digit+1)))+lut+groups*(3*factor)+pins

def partyTariff (s e k b d : ℕ) :=
  (batchRate true+gatherRate)*batchUnits (e*k+s) s 1 d (e*k) +
  (batchRate false+gatherRate)*batchUnits (b+(e*d+e*d)) e d d (b+e*d) + gatherRate

section VacantTariff

attribute [local irreducible] HistoryPartyBatchExec.Build.staticCost HistoryPartyPairExec.overhead

private theorem build_batch_rate (X : HistoryPartyBatchExec.Build W) (ck : Bool) (hc : X.checks=ck) :
    X.staticCost=batchRate ck := by
  unfold batchRate
  exact X.staticCost_eq (rateBuild ck) hc

private theorem pair_overhead_rate (A : HistoryPartyBatch.Layout) (w : ℕ) :
    HistoryPartyPairExec.overhead A w=gatherRate := by
  unfold gatherRate
  exact HistoryPartyPairExec.overhead_eq A tariffLayout w 0

private theorem vacant_tariff_bound (x y z checks payload overhead left right total scale : ℕ)
    (hx : x=checks) (hy : y=payload) (hz : z=overhead)
    (ht : total=(checks+overhead)*left+(payload+overhead)*right+overhead)
    (hl : 0<left) (hr : 0<right) (hw : 0<scale) :
    x+y+z ≤ total*scale*(1+0) := by
  have part (cost units : ℕ) (hu : 0<units) : cost≤(cost+overhead)*units :=
    (Nat.le_add_right cost overhead).trans (Nat.le_mul_of_pos_right _ hu)
  rw [hx,hy,hz,ht,Nat.add_zero,Nat.mul_one]
  exact (Nat.add_le_add_right (Nat.add_le_add (part checks left hl)
    (part payload right hr)) overhead).trans (Nat.le_mul_of_pos_right _ hw)

set_option maxHeartbeats 1600000 in
theorem vacant_pair_tariff (A : HistoryPartyBatch.Layout) (input : Memory W) (s e k b d : ℕ) :
    (vacantChecks A input).staticCost+(vacantPayload A input).staticCost+HistoryPartyPairExec.overhead A W ≤
      partyTariff s e k b d*(W+1)^3*(1+0) := by
  have units_pos (l g f pins : ℕ) : 0<batchUnits l g f d pins := by
    unfold batchUnits
    omega
  exact vacant_tariff_bound (vacantChecks A input).staticCost (vacantPayload A input).staticCost
    (HistoryPartyPairExec.overhead A W) (batchRate true) (batchRate false) gatherRate
    (batchUnits (e*k+s) s 1 d (e*k)) (batchUnits (b+(e*d+e*d)) e d d (b+e*d))
    (partyTariff s e k b d) ((W+1)^3)
    (build_batch_rate (vacantChecks A input) true rfl) (build_batch_rate (vacantPayload A input) false rfl)
    (pair_overhead_rate A W) rfl (units_pos _ _ _ _) (units_pos _ _ _ _) (Nat.pow_pos (Nat.succ_pos W))

end VacantTariff


end
end ThreeFlat.RAM.HistoryRefreshEmitter

end OAI
