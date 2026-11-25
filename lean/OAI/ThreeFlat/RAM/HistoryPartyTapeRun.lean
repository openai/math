import OAI.ThreeFlat.RAM.HistoryReadyTape
import OAI.ThreeFlat.RAM.HistorySelectedRead
import OAI.ThreeFlat.RAM.HistoryLeafOutputs
import OAI.ThreeFlat.RAM.HistoryMotifMapCorrect
import OAI.ThreeFlat.RAM.HistoryPartySpecialization
import OAI.ThreeFlat.RAM.WordQuotients

namespace OAI
/-! # The three selected operations for each child of a physical motif batch -/

namespace ThreeFlat.RAM.HistoryPartyTapeRun
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr DescriptorScan BitNetwork.Ordered
open HistoryReadyTape HistoryCompiledRows
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type*} {w p h : ℕ} (T : HistoryBatchTape.Header) {arity : Fin (T.r+T.s) → ℕ}
variable (N : ∀ i,BitNetwork F (arity i)) (wire : ∀ i,Fin (arity i) → BitSource h p)
variable (id : ((Fin 3 → Bool) → F) → ℕ)

private def metadataWord (n : ℕ) (entry : Fin n → Fin 4 → ℕ) (start address : ℕ) : Word w :=
  let delta := address-start
  if hrow : delta/4<n then (entry ⟨delta/4,hrow⟩ ⟨delta % 4, Nat.mod_lt delta (by decide : 0 < 4)⟩:Word w) else 0

private theorem atMetadata (n : ℕ) (entry : Fin n → Fin 4 → ℕ) (start : ℕ) (r : Fin n) (j : Fin 4) :
    metadataWord (w:=w) n entry start (start+(4*r.val+j.val))=(entry r j:Word w) := by
  have row : (4*r.val+j.val)/4=r.val := by rw [Nat.mul_add_div (by decide : 0<4),Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  simp [metadataWord,row,r.isLt,Nat.mod_eq_of_lt j.isLt]

/-- Actual words of the new physical pin image for a single child. -/
def pinAddress (i : Fin (T.r+T.s)) (z : ℕ) :=
  if hz : z<arity i then BitLayout.sourceAddress (resolve N wire i (.pin ⟨z,hz⟩)) else 0

def leafJob (i : Fin (T.r+T.s)) : Job w :=
  ⟨(T.row i.val).source,(T.row i.val).count,
    metadataWord (N i).cells (metadata id (N i)) (T.row i.val).source⟩

def mapJob (i : Fin (T.r+T.s)) : Job w :=
  ⟨(T.row i.val).map,T.arity i.val,fun a => (pinAddress T N wire i (a-(T.row i.val).map):Word w)⟩

def joinJob (i : Fin (T.r+T.s)) : Job w :=
  ⟨(T.row i.val).dest,(T.row i.val).count,
    metadataWord (N i).cells (fun r j => metadata id (glue N wire) (finSigmaFinEquiv ⟨i,r⟩) j)
      (T.row i.val).dest⟩

def group (i : Fin (T.r+T.s)) : List (Job w) :=
  [leafJob T N id i,mapJob T N wire i,joinJob T N wire id i]

def jobs : List (Job w) := (List.finRange (T.r+T.s)).flatMap (group T N wire id)

@[simp] theorem group_length (i : Fin (T.r+T.s)) : (group (w:=w) T N wire id i).length=3 := rfl

private theorem grouped_length (xs : List (Fin (T.r+T.s))) :
    (xs.flatMap (group (w:=w) T N wire id)).length=3*xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [List.flatMap_cons,ih,Nat.mul_add]; omega

theorem jobs_length : (jobs (w:=w) T N wire id).length=3*(T.r+T.s) := by
  rw [jobs,grouped_length,List.length_finRange]

theorem group_bounds (i : Fin (T.r+T.s)) (j : Fin 3) :
    let x := (group (w:=w) T N wire id i).get j
    HistoryBatchTape.command T i.val j 1=x.start ∧ HistoryBatchTape.command T i.val j 6=x.finish := by
  fin_cases j <;> exact ⟨rfl,rfl⟩

/-- The child-copy dimensions supplied by the two actual party batch specializations. -/
structure Shape : Prop where
  count : ∀ i : Fin (T.r+T.s),(T.row i.val).count=4*(N i).cells
  pins : ∀ i : Fin (T.r+T.s),T.arity i.val=arity i
  parent : T.parentPins=p
  offset : ∀ i : Fin (T.r+T.s),T.shared+(T.row i.val).bitPrefix =
    h+∑ z : Fin i.val,(N (Fin.castLE i.isLt.le z)).internal

private def joinHeader (i : Fin (T.r+T.s)) : HistoryJoinScan.Header ℕ :=
  ⟨(T.row i.val).source,(T.row i.val).dest,(T.row i.val).map,T.arity i.val,T.parentPins,
    T.shared+(T.row i.val).bitPrefix⟩

private theorem cursorIndex (base size : ℕ) (a : Word w) (lo : base≤a.val) (hi : a.val<base+4*size) :
    ∃ (r : Fin size) (j : Fin 4),a.val=base+(4*r.val+j.val) := by
  let d := a.val-base
  have hd : d<4*size := by dsimp [d];omega
  refine ⟨⟨d/4,by omega⟩,⟨d%4,Nat.mod_lt _ (by decide)⟩,?_⟩
  have := Nat.mod_add_div d 4
  change a.val=base+(4*(d/4)+d%4)
  dsimp [d] at *
  omega

def kindAt (i : ℕ) : HistoryMotifMaps.Kind :=
  if T.checks then (if i<T.r then .localTest else .counter)
  else if i<T.r then .tile else .stream

def partAt (i : ℕ) := if i<T.r then i else i-T.r
def quotaAt (raw : ℕ → ℕ) (i : ℕ) := if T.checks ∧ ¬i<T.r then raw (T.hist+partAt T i) else 0

def mapRegs (raw : ℕ→ℕ) (i x : ℕ) :=
  HistoryMotifMaps.values (kindAt T i) x (partAt T i) T.r T.b T.e T.d T.alphabet (quotaAt T raw i)

private theorem map_read {k : ℕ} (init : Term w k 4) (gates : List (Term w 1 13)) (data : Fin (k+1) → Word w)
    (mem : Memory w) (a : Word w) (raw : ℕ→ℕ) (i x : ℕ)
    (size : 12+gates.length≤2^w) (op : HistorySelectedOps.tag data mem=4)
    (args : ∀ j, HistoryOperandScan.input mem (HistorySelectedOps.operandPointer data mem) a 1
      (HistoryOperandScan.motifOperands j)=(mapRegs T raw i x j : Word w))
    (fit : HistoryMotifMaps.formula.Fits w (fun _ => (HistorySelectedOps.operandPointer data mem).val)
      (fun a => (mem a).val) (mapRegs T raw i x)) :
    (HistorySelectedOps.rows init gates).eval data mem (fun _ => a)=
    (HistoryMotifMaps.word (kindAt T i) x (partAt T i) T.r T.b T.e T.d T.alphabet (quotaAt T raw i):Word w) := by
  let z : Fin (HistorySelectedOps.entries init gates).length :=
    ⟨4,by rw [HistorySelectedOps.entries_length]; omega⟩
  rw [HistorySelectedOps.active init gates data mem _ z size op]
  change (HistoryCommandParameter.onlyBlock (Fin.last k) (HistoryOperandScan.motif w)).eval _ _ _=_
  rw [HistoryCommandParameter.onlyBlock_eval,HistoryOperandScan.motif,HistoryOperandScan.eval]
  change (HistoryMotifMaps.program w).eval (fun _ => HistorySelectedOps.operandPointer data mem) mem
    (fun j => HistoryOperandScan.input mem _ a 1 (HistoryOperandScan.motifOperands j))=_
  refine (congrArg (fun vs : Fin 9 → Word w =>
    (HistoryMotifMaps.program w).eval (fun _ => HistorySelectedOps.operandPointer data mem) mem vs)
    (funext args)).trans ?_
  have h := HistoryMotifMaps.eval w (fun _ => (HistorySelectedOps.operandPointer data mem).val)
    (fun z => (mem z).val) (kindAt T i) x (partAt T i) T.r T.b T.e T.d T.alphabet (quotaAt T raw i) fit
  simpa only [Fin.cast_val_eq_self,mapRegs] using h

private theorem fill_mem (x : Job w) (m : Memory w) (a : ℕ) (lo : x.start≤a) (hi : a<x.finish) :
    fillSegment x.start x.count x.word m a=x.word a := by
  simp [fillSegment,lo,show a<x.start+x.count from hi]

private theorem written (ctrl : Word w) (x : Job w) (m : Memory w) (a : ℕ) (different : a≠ctrl.val)
    (lo : x.start≤a) (hi : a<x.finish) : after ctrl [x] m a=x.word a := by
  simp [HistoryReadyTape.after,HistoryJoinController.bumpMemory,writeMemory,different,fill_mem x m a lo hi]

/-- The input tape and operand bank are the words generated by the batch-header emitter. -/
structure Banks (bank : ℕ) (raw : ℕ→ℕ) (m : Memory w) : Prop where
  commands : ∀ (i : Fin (T.r+T.s)) (j : Fin 3) (a : Fin 7),
    m (bank+21*i.val+7*j.val+a.val)=(HistoryBatchTape.command T i.val j a:Word w)
  arguments : ∀ (i : Fin (T.r+T.s)) (a : Fin 23),
    m (T.args+23*i.val+a.val)=(HistoryBatchTape.arguments T raw i.val a:Word w)

private def separated (a n : ℕ) (x : Job w) : Prop := a+n≤x.start ∨ x.finish≤a

private theorem away_at {a n x : ℕ} {j : Job w} (h : separated a n j)
    (lo : a≤x) (hi : x<a+n) : x<j.start ∨ j.finish≤x := by
  unfold separated at h
  omega

variable [CommRing F] [Fintype F] {z B D : ℕ}
variable (L : HistoryStaticArchive.Catalog F z B) (page : Fin z) (power : Fin (D+1)) (logical : ℕ)
variable (fixedBase compactBase : ℕ)

/-- The row identifications are ordinary finite-network identities of
the selected LUT and shortened dyadic compactor. -/
structure Models (raw : ℕ→ℕ) : Prop where
  lut : T.lut=![fixedBase,HistoryStaticArchive.stride B,page.val]
  comp : T.comp=![2^power.val,logical,StableCompactROMNative.pageBase D compactBase power.val]
  small : logical≤2^power.val
  leftSize (i : Fin (T.r+T.s)) (left : i.val<T.r) : (N i).cells=(L.rows page).cells
  leftRows (i : Fin (T.r+T.s)) (left : i.val<T.r) (r : Fin (N i).cells) (j : Fin 4) :
    metadata id (N i) r j=metadata (fun g => (Fintype.equivFin _ g).val) (L.rows page)
      (Fin.cast (leftSize i left) r) j
  rightSize (i : Fin (T.r+T.s)) (right : ¬i.val<T.r) : (N i).cells=((Routing.StableCompaction.restrictRows (Routing.StableCompactNative.network F power.val) logical)).cells
  rightRows (i : Fin (T.r+T.s)) (right : ¬i.val<T.r) (r : Fin (N i).cells) (j : Fin 4) :
    metadata id (N i) r j=metadata id (Routing.StableCompaction.restrictRows (Routing.StableCompactNative.network F power.val) logical) (Fin.cast (rightSize i right) r) j
  mapWords (i : Fin (T.r+T.s)) (x : Fin (arity i)) :
    HistoryMotifMaps.word (kindAt T i.val) x.val (partAt T i.val) T.r T.b T.e T.d T.alphabet
      (quotaAt T raw i.val)=pinAddress T N wire i x.val

/-- Persistent advice words addressed by the fixed native leaf readers. -/
structure Archive (m : Memory w) : Prop where
  fixed : L.Stores fixedBase m
  compact : ∀ x : Fin (StableCompactROMNative.size D),m (compactBase+x.val)=StableCompactROMNative.data D id x

/-- The native leaf result on each candidate is the actual corresponding child metadata. -/
private theorem leaf_read {k : ℕ} (initial : Term w k 4) (gates : List (Term w 1 13))
    (data : Fin (k+1)→Word w) (mem : Memory w) (raw : ℕ→ℕ) (i : Fin (T.r+T.s))
    (a : Word w) (r : Fin (N i).cells) (j : Fin 4)
    (model : Models T N wire id L page power logical fixedBase compactBase raw)
    (image : Archive (w:=w) id L fixedBase (D:=D) compactBase mem)
    (size : 12+gates.length≤2^w) (space : StableCompactNativeBudget.budget power<2^w)
    (fixedFit : fixedBase+HistoryStaticArchive.size z B≤2^w) (compactFit : compactBase+StableCompactROMNative.size D≤2^w)
    (tag : HistorySelectedOps.tag data mem=0)
    (args : HistoryLeafDispatch.memory (HistorySelectedOps.operandPointer data mem) mem=
      ⟨(if i.val<T.r then 1 else 2),(if i.val<T.r then T.lut 0 else T.comp 0 : ℕ),
       (if i.val<T.r then T.lut 1 else T.comp 1 : ℕ),(if i.val<T.r then T.lut 2 else T.comp 2 : ℕ),
       ((T.row i.val).source:Word w)⟩)
    (key : a.val=(T.row i.val).source+(4*r.val+j.val)) :
    (HistorySelectedOps.rows initial gates).eval data mem (fun _ => a)=(metadata id (N i) r j:Word w) := by
  rw [HistorySelectedOps.leaf_read initial gates data mem _ size tag,args]
  have delta : a-((T.row i.val).source:Word w)=((4*r.val+j.val:ℕ):Word w) := by
    rw [show a=(((T.row i.val).source+(4*r.val+j.val):ℕ):Word w) by rw [←key,Fin.cast_val_eq_self],Nat.cast_add]
    abel
  have h1 : (1:Word w).val=1 := Fin.val_cast_of_lt (by omega : 1<2^w)
  have h2 : (2:Word w).val=2 := Fin.val_cast_of_lt (by omega : 2<2^w)
  have nz₁ : (1 : Word w) ≠ 0 := by
    intro eq
    have bad := congrArg (fun v : Word w => v.val) eq
    rw [h1, Fin.val_zero] at bad
    omega
  have nz₂ : (2 : Word w) ≠ 0 := by
    intro eq
    have bad := congrArg (fun v : Word w => v.val) eq
    rw [h2, Fin.val_zero] at bad
    omega
  have ne₂ : (2 : Word w) ≠ 1 := by
    intro eq
    have bad := congrArg (fun v : Word w => v.val) eq
    rw [h2, h1] at bad
    omega
  by_cases l : i.val<T.r
  · simp only [ite_eq_left l,model.lut,Matrix.cons_val_zero,model.leftRows i l]
    exact HistoryLeafDispatch.fixed_readWord L page _ j _ _ mem fixedBase _ a
      nz₁ image.fixed fixedFit delta
  · simp only [ite_eq_right l,model.comp,Matrix.cons_val_zero,model.rightRows i l]
    exact HistoryLeafDispatch.compact_readWord power logical model.small _ j _ _ mem compactBase _ a
      nz₂ ne₂ id (StableCompactROMNative.stores_of_read D compactBase id mem image.compact) space compactFit delta

private theorem fetch_at (m : Memory w) (base i : ℕ) (hi : base+i<2^w) :
    m ((base:Word w)+(i:Word w)).val=m (base+i) := by rw [←Nat.cast_add,Fin.val_cast_of_lt hi]

private def commandOffset : Fin 3 → ℕ := ![0,6,16]
private def commandTag : Fin 3 → ℕ := ![0,4,1]

private theorem Banks.current {bank : ℕ} {raw : ℕ→ℕ} {mem : Memory w} (M : Banks T bank raw mem)
    {k : ℕ} (data : Fin (k+1)→Word w) (i : Fin (T.r+T.s)) (j : Fin 3)
    (size : bank+21*(T.r+T.s)≤2^w) (room : 12≤2^w)
    (atCursor : mem (data (Fin.last k)).val=((bank+21*i.val+7*j.val:ℕ):Word w)) :
    HistorySelectedOps.tag data mem=commandTag j ∧ HistorySelectedOps.operandPointer data mem=
      ((T.args+23*i.val+commandOffset j:ℕ):Word w) := by
  let pc := bank+21*i.val+7*j.val
  have pcFit : pc+2<2^w := by have := i.isLt;have := j.isLt;dsimp [pc];omega
  have opAddr : (mem (data (Fin.last k)).val+2).val=pc+2 := by
    change (mem (data (Fin.last k)).val+(2:ℕ)).val=_
    rw [atCursor,←Nat.cast_add,Fin.val_cast_of_lt pcFit]
  have opRead : mem (pc+2)=(commandTag j:Word w) := by
    have vs := M.commands i j (2:Fin 7)
    fin_cases j <;> exact vs
  have ptrRead : mem pc=((T.args+23*i.val+commandOffset j:ℕ):Word w) := by
    have vs := M.commands i j (0:Fin 7)
    fin_cases j <;> simpa [HistoryBatchTape.command,commandOffset,pc] using vs
  constructor
  · change (mem (mem (data (Fin.last k)).val+2).val).val=_
    have tagBound : commandTag j ≤ 4 := by fin_cases j <;> decide
    have tagFit : commandTag j < 2^w := tagBound.trans_lt (by omega)
    rw [opAddr,opRead,Fin.val_cast_of_lt tagFit]
  · change mem (mem (data (Fin.last k)).val).val=_
    rw [atCursor,Fin.val_cast_of_lt (by omega : pc<2^w)]
    exact ptrRead

private theorem Banks.slice {bank : ℕ} {raw : ℕ→ℕ} {mem : Memory w} (M : Banks T bank raw mem)
    (i : Fin (T.r+T.s)) (origin : Word w) (offset slot : ℕ)
    (base : origin=((T.args+23*i.val+offset:ℕ):Word w)) (col : offset+slot<23)
    (room : T.args+23*(T.r+T.s)≤2^w) :
    mem (origin+(slot:Word w)).val=(HistoryBatchTape.arguments T raw i.val ⟨offset+slot,col⟩:Word w) := by
  have fit : T.args+23*i.val+offset+slot<2^w := by have := i.isLt;omega
  rw [base,fetch_at mem (T.args+23*i.val+offset) slot fit]
  simpa only [Nat.add_assoc] using M.arguments i ⟨offset+slot,col⟩

private theorem Banks.leaf {bank : ℕ} {raw : ℕ→ℕ} {mem : Memory w} (M : Banks T bank raw mem)
    (i : Fin (T.r+T.s)) (origin : Word w) (base : origin=((T.args+23*i.val+0:ℕ):Word w))
    (room : T.args+23*(T.r+T.s)≤2^w) :
    HistoryLeafDispatch.memory origin mem=
      ⟨(if i.val<T.r then 1 else 2),(if i.val<T.r then T.lut 0 else T.comp 0:ℕ),
       (if i.val<T.r then T.lut 1 else T.comp 1:ℕ),(if i.val<T.r then T.lut 2 else T.comp 2:ℕ),
       ((T.row i.val).source:Word w)⟩ := by
  have q (n : ℕ) (hc : n<23) := Banks.slice T M i origin 0 n base (by omega) room
  unfold HistoryLeafDispatch.memory
  simp only [q 0 (by decide),q 1 (by decide),q 2 (by decide),q 3 (by decide),q 4 (by decide)]
  by_cases l : i.val<T.r <;> simp [HistoryBatchTape.arguments,l]

private theorem Banks.pins {bank : ℕ} {raw : ℕ→ℕ} {mem : Memory w} (M : Banks T bank raw mem)
    (i : Fin (T.r+T.s)) (origin a : Word w) (base : origin=((T.args+23*i.val+6:ℕ):Word w))
    (x : ℕ) (atOut : a.val=(T.row i.val).map+x) (room : T.args+23*(T.r+T.s)≤2^w)
    (word : 1<2^w) :
    ∀ j,HistoryOperandScan.input mem origin a 1 (HistoryOperandScan.motifOperands j) =
      (mapRegs T raw i.val x j:Word w) := by
  have q (n : ℕ) (hc : 6+n<23) := Banks.slice T M i origin 6 n base hc room
  have first : mem origin.val=((T.row i.val).map:Word w) := by
    simpa [HistoryBatchTape.arguments] using q 0 (by decide)
  have av : a=(((T.row i.val).map+x:ℕ):Word w) := by rw [←atOut,Fin.cast_val_eq_self]
  have xv : x<2^w := by have := a.isLt;omega
  have quotient : BinaryOp.div.eval (a-mem origin.val) (1:Word w)=(x:Word w) := by
    rw [first,av,Nat.cast_add,add_sub_cancel_left]
    simpa using WordQuotients.div_at x 1 xv word
  have rd2 : mem (origin+2).val = _ := q 2 (by decide)
  have rd3 : mem (origin+3).val = _ := q 3 (by decide)
  have rd4 : mem (origin+4).val = _ := q 4 (by decide)
  have rd5 : mem (origin+5).val = _ := q 5 (by decide)
  have rd6 : mem (origin+6).val = _ := q 6 (by decide)
  have rd7 : mem (origin+7).val = _ := q 7 (by decide)
  have rd8 : mem (origin+8).val = _ := q 8 (by decide)
  have rd9 : mem (origin+9).val = _ := q 9 (by decide)
  intro j
  cases c : T.checks <;> by_cases l : i.val<T.r <;> fin_cases j <;>
    simp [HistoryOperandScan.motifOperands,HistoryOperandScan.input,mapRegs,HistoryMotifMaps.values,
      kindAt,partAt,quotaAt,HistoryMotifMaps.Kind.tag,rd2,rd3,rd4,rd5,rd6,rd7,rd8,rd9,
      HistoryBatchTape.arguments,quotient,c,l]

private theorem Banks.join {bank : ℕ} {raw : ℕ→ℕ} {mem : Memory w} (M : Banks T bank raw mem)
    (i : Fin (T.r+T.s)) (origin : Word w) (base : origin=((T.args+23*i.val+16:ℕ):Word w))
    (room : T.args+23*(T.r+T.s)≤2^w) :
    HistoryJoinScan.fetch origin mem=(joinHeader T i).words := by
  have q (n : ℕ) (hc : 16+n<23) := Banks.slice T M i origin 16 n base hc room
  have rd0 : mem (origin+0).val = _ := q 0 (by decide)
  have rd1 : mem (origin+1).val = _ := q 1 (by decide)
  have rd2 : mem (origin+2).val = _ := q 2 (by decide)
  have rd3 : mem (origin+3).val = _ := q 3 (by decide)
  have rd4 : mem (origin+4).val = _ := q 4 (by decide)
  have rd5 : mem (origin+5).val = _ := q 5 (by decide)
  unfold HistoryJoinScan.fetch HistoryJoinScan.Header.words joinHeader
  rw [rd0,rd1,rd2,rd3,rd4,rd5]
  simp [HistoryBatchTape.arguments]

private def span (a n x : ℕ) := a≤x ∧ x<a+n

def immutable (bank : ℕ) (a : ℕ) :=
  span bank (21*(T.r+T.s)) a ∨ span T.args (23*(T.r+T.s)) a ∨
    span fixedBase (HistoryStaticArchive.size z B) a ∨ span compactBase (StableCompactROMNative.size D) a

/-- Disjointness is expressed in actual word intervals of the three operations.
The distinct-child condition protects the finished parent stream. -/
structure Space (ctrl : Word w) (bank : ℕ) : Prop where
  tape : bank+21*(T.r+T.s)≤2^w
  argv : T.args+23*(T.r+T.s)≤2^w
  lut : fixedBase+HistoryStaticArchive.size z B≤2^w
  comp : compactBase+StableCompactROMNative.size D≤2^w
  ctrlInput : ∀ a,immutable (z:=z) (B:=B) (D:=D) T fixedBase compactBase bank a → a≠ctrl.val
  inputs : ∀ a,immutable (z:=z) (B:=B) (D:=D) T fixedBase compactBase bank a →
    ∀ x∈jobs (w:=w) T N wire id,a<x.start ∨ x.finish≤a
  ctrlOutput : ∀ x∈jobs (w:=w) T N wire id,ctrl.val<x.start ∨ x.finish≤ctrl.val
  split : ∀ i i' : Fin (T.r+T.s), ∀ j j' : Fin 3,(i,j)≠(i',j') →
    separated ((group (w:=w) T N wire id i).get j).start ((group (w:=w) T N wire id i).get j).count
      ((group (w:=w) T N wire id i').get j')
  finishes : ∀ x∈jobs (w:=w) T N wire id,x.finish<2^w

/-- Total staging rows and tile pin words, before the batch's translated second stream. -/
def batchRows := T.r*T.left.rows+T.s*T.right.rows
def batchPins := T.r*T.left.arity+T.s*T.right.arity

private theorem prefix_mono (r u v:ℕ) {i j:ℕ} (ij:i≤j) :
    Diagonal.HistoryContraction.Tree.BatchRows.span r u v i≤
      Diagonal.HistoryContraction.Tree.BatchRows.span r u v j := by
  unfold Diagonal.HistoryContraction.Tree.BatchRows.span
  exact Nat.add_le_add (Nat.mul_le_mul_right _ (min_le_min_right _ ij)) (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right ij _))

private theorem prefix_step (r u v i:ℕ) :
    Diagonal.HistoryContraction.Tree.BatchRows.span r u v i+(if i<r then u else v)=
      Diagonal.HistoryContraction.Tree.BatchRows.span r u v (i+1) := by
  simp only [←Diagonal.HistoryContraction.Tree.BatchRows.span_range,Finset.sum_range_succ]

private theorem prefix_end (r s u v:ℕ) :
    Diagonal.HistoryContraction.Tree.BatchRows.span r u v (r+s)=r*u+s*v := by
  simp [Diagonal.HistoryContraction.Tree.BatchRows.span]

private def axisBase (j : Fin 3) : ℕ := ![T.stream,T.maps,T.stream+4*batchRows T] j
private def axisPrefix (j : Fin 3) (i:ℕ) : ℕ :=
  let R:=Diagonal.HistoryContraction.Tree.BatchRows.span T.r T.left.rows T.right.rows i
  let P:=Diagonal.HistoryContraction.Tree.BatchRows.span T.r T.left.arity T.right.arity i
  ![4*R,P,4*R] j

omit [CommRing F] [Fintype F] in
private theorem indexed_job (i:Fin (T.r+T.s)) (j:Fin 3) :
    let x:=(group (w:=w) T N wire id i).get j
    x.start=axisBase T j+axisPrefix T j i.val ∧ x.finish=axisBase T j+axisPrefix T j (i.val+1) := by
  let rows:=fun a=>Diagonal.HistoryContraction.Tree.BatchRows.span T.r T.left.rows T.right.rows a
  let pins:=fun a=>Diagonal.HistoryContraction.Tree.BatchRows.span T.r T.left.arity T.right.arity a
  have h₁ : rows i.val+(if i.val<T.r then T.left.rows else T.right.rows)=rows (i.val+1):=prefix_step ..
  have h₂ : pins i.val+(if i.val<T.r then T.left.arity else T.right.arity)=pins (i.val+1):=prefix_step ..
  fin_cases j
  · exact ⟨rfl,by change T.stream+4*rows i.val+4*(if i.val<T.r then T.left.rows else T.right.rows)=T.stream+4*rows (i.val+1);omega⟩
  · exact ⟨rfl,by change T.maps+pins i.val+(if i.val<T.r then T.left.arity else T.right.arity)=T.maps+pins (i.val+1);omega⟩
  · exact ⟨rfl,by change T.stream+4*batchRows T+4*rows i.val+4*(if i.val<T.r then T.left.rows else T.right.rows)=
           T.stream+4*batchRows T+4*rows (i.val+1);omega⟩

private theorem axis_mono (j:Fin 3) {i k:ℕ} (lt:i≤k) : axisPrefix T j i≤axisPrefix T j k:=by
  have rows:=prefix_mono T.r T.left.rows T.right.rows lt
  have pins:=prefix_mono T.r T.left.arity T.right.arity lt
  fin_cases j <;> first | exact pins | exact Nat.mul_le_mul_left 4 rows

private theorem axis_end (j:Fin 3) :
    axisPrefix T j (T.r+T.s)=(![4*batchRows T,batchPins T,4*batchRows T]:Fin 3→ℕ) j := by
  fin_cases j <;> simp [axisPrefix,batchRows,batchPins,prefix_end]

omit [CommRing F] [Fintype F] in
theorem job_placement (x:Job w) (mem:x∈jobs T N wire id) :
    (T.stream≤x.start ∧ x.finish≤T.stream+8*batchRows T) ∨
      (T.maps≤x.start ∧ x.finish≤T.maps+batchPins T) := by
  obtain ⟨i,_,hx⟩:=List.mem_flatMap.mp mem
  obtain ⟨j,e⟩:=List.mem_iff_get.mp hx
  have pos:=indexed_job T N wire id (w:=w) i j
  have h:=axis_mono T j (show i.val+1≤T.r+T.s from i.isLt)
  rw [axis_end T j] at h
  rw [←e]
  have region (v : Fin 3) (a b : ℕ) (start : a=axisBase T v+axisPrefix T v i.val)
      (finish : b=axisBase T v+axisPrefix T v (i.val+1))
      (bound : axisPrefix T v (i.val+1)≤(![4*batchRows T,batchPins T,4*batchRows T] : Fin 3→ℕ) v) :
      (T.stream≤a ∧ b≤T.stream+8*batchRows T) ∨ (T.maps≤a ∧ b≤T.maps+batchPins T) := by
    fin_cases v <;> dsimp [axisBase] at start finish bound <;> omega
  exact region j _ _ pos.1 pos.2 h

omit [CommRing F] [Fintype F] in
/-- All distinct leaf, affine-map, and translated rows are disjoint by their actual
piecewise-constant prefix sums. Zero-width entries need no separate case. -/
theorem jobs_separate (disjoint : T.stream+8*batchRows T≤T.maps ∨ T.maps+batchPins T≤T.stream)
    (i k : Fin (T.r+T.s)) (j l : Fin 3) (ne : (i,j)≠(k,l)) :
    separated ((group (w:=w) T N wire id i).get j).start ((group (w:=w) T N wire id i).get j).count
      ((group (w:=w) T N wire id k).get l) := by
  let x:=(group (w:=w) T N wire id i).get j
  let y:=(group (w:=w) T N wire id k).get l
  change x.finish≤y.start ∨ y.finish≤x.start
  have p : x.start=axisBase T j+axisPrefix T j i.val ∧ x.finish=axisBase T j+axisPrefix T j (i.val+1):=
    indexed_job T N wire id i j
  have q : y.start=axisBase T l+axisPrefix T l k.val ∧ y.finish=axisBase T l+axisPrefix T l (k.val+1):=
    indexed_job T N wire id k l
  by_cases e:j=l
  · subst l
    have diff : i≠k:=fun h=>ne (by rw [h])
    rcases lt_or_gt_of_ne diff with ik|ki
    · exact .inl (by have z:=axis_mono T j (show i.val+1≤k.val from ik);omega)
    · exact .inr (by have z:=axis_mono T j (show k.val+1≤ i.val from ki);omega)
  · have px:=axis_mono T j (show i.val+1≤T.r+T.s from i.isLt)
    have qx:=axis_mono T l (show k.val+1≤T.r+T.s from k.isLt)
    rw [axis_end] at px qx
    fin_cases j <;> fin_cases l <;> first | exact (e rfl).elim |
      (dsimp [axisBase] at p q px qx;omega)

omit [CommRing F] [Fintype F] in
/-- Construct the concrete batch space from the two S12/S18 write extents and
numerical protection of the four input ranges. No pairwise job hypothesis is needed. -/
theorem space_of_windows (ctrl:Word w) (bank:ℕ)
    (tape : bank+21*(T.r+T.s)≤2^w) (args : T.args+23*(T.r+T.s)≤2^w)
    (lut : fixedBase+HistoryStaticArchive.size z B≤2^w) (comp : compactBase+StableCompactROMNative.size D≤2^w)
    (rows : T.stream+8*batchRows T<2^w) (pins : T.maps+batchPins T<2^w)
    (windows : T.stream+8*batchRows T≤T.maps ∨ T.maps+batchPins T≤T.stream)
    (ctrlRows : ctrl.val<T.stream ∨ T.stream+8*batchRows T≤ctrl.val)
    (ctrlPins : ctrl.val<T.maps ∨ T.maps+batchPins T≤ctrl.val)
    (source : ∀ x,
      ((bank≤x ∧ x<bank+21*(T.r+T.s)) ∨ (T.args≤x ∧ x<T.args+23*(T.r+T.s)) ∨
       (fixedBase≤x ∧ x<fixedBase+HistoryStaticArchive.size z B) ∨
       (compactBase≤x ∧ x<compactBase+StableCompactROMNative.size D)) →
      x≠ctrl.val ∧ (x<T.stream ∨ T.stream+8*batchRows T≤x) ∧ (x<T.maps ∨ T.maps+batchPins T≤x)) :
    Space (z:=z) (B:=B) (D:=D) T N wire id fixedBase compactBase ctrl bank := by
  refine ⟨tape,args,lut,comp,fun x h=>(source x h).1,?_,?_,jobs_separate T N wire id windows,?_⟩
  · intro a valid x mem
    have protected_:=source a valid
    rcases job_placement T N wire id x mem with p|p <;> omega
  · intro x mem
    rcases job_placement T N wire id x mem with p|p <;> omega
  · intro x mem
    rcases job_placement T N wire id x mem with p|p <;> omega

structure Mount (bank : ℕ) (raw : ℕ→ℕ) (m : Memory w) : Prop where
  banks : Banks T bank raw m
  archive : Archive (D:=D) id L fixedBase compactBase m

variable {bank : ℕ} {ctrl : Word w} {raw : ℕ→ℕ}

private theorem Mount.frame {m out : Memory w} (M : Mount T id L (D:=D) fixedBase compactBase bank raw m)
    (keep : ∀a, immutable (z:=z) (B:=B) (D:=D) T fixedBase compactBase bank a → out a=m a) :
    Mount T id L (D:=D) fixedBase compactBase bank raw out := by
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro i j f
    rw [keep _ (Or.inl (by have := i.isLt;have := j.isLt;have := f.isLt; dsimp [span];omega)),M.banks.commands]
  · intro i f
    rw [keep _ (Or.inr (Or.inl (by have := i.isLt;have := f.isLt;dsimp [span];omega))),M.banks.arguments]
  · intro f
    rw [keep _ (Or.inr (Or.inr (Or.inl (by have := f.isLt;dsimp [span];omega)))),M.archive.fixed]
  · intro f
    rw [keep _ (Or.inr (Or.inr (Or.inr (by have := f.isLt;dsimp [span];omega)))),M.archive.compact]

omit [CommRing F] [Fintype F] in
private theorem group_mem (i : Fin (T.r+T.s)) : ∀ x∈group (w:=w) T N wire id i,x∈jobs T N wire id :=
  fun _x h => List.mem_flatMap.mpr ⟨i,List.mem_finRange i,h⟩

theorem cursor_after {xs : List (Job w)} {m : Memory w} (ctrl : Word w)
    (out : ∀ x ∈ xs,ctrl.val<x.start ∨ x.finish≤ctrl.val) :
    after ctrl xs m ctrl.val=m ctrl.val+(7*xs.length:ℕ) := by
  induction xs generalizing m with
  | nil => simp [HistoryReadyTape.after]
  | cons x xs ih =>
    have h := out x (List.mem_cons_self ..)
    have keep : fillSegment x.start x.count x.word m ctrl.val=m ctrl.val := by
      simp [fillSegment,show ¬(x.start≤ctrl.val ∧ ctrl.val<x.start+x.count) by
        change ¬(x.start≤ctrl.val ∧ ctrl.val<x.finish);omega]
    rw [HistoryReadyTape.after,ih (m:=HistoryJoinController.bumpMemory ctrl _) (fun y h => out y (List.mem_cons_of_mem _ h))]
    simp [HistoryJoinController.bumpMemory,writeMemory,keep,List.length_cons,Nat.mul_add,Nat.cast_add]
   ; abel

private theorem Mount.previous {m : Memory w} (M : Mount T id L (D:=D) fixedBase compactBase bank raw m)
    (S : Space (z:=z) (B:=B) (D:=D) T N wire id fixedBase compactBase ctrl bank)
    (xs : List (Job w)) (included : ∀ x∈xs,x∈jobs T N wire id) :
    Mount T id L (D:=D) fixedBase compactBase bank raw (after ctrl xs m) :=
  Mount.frame T id L fixedBase compactBase M fun a ha => after_away ctrl xs m a (S.ctrlInput a ha) (fun x hx => S.inputs a ha x (included x hx))

private theorem Mount.during {m out : Memory w} (M : Mount T id L (D:=D) fixedBase compactBase bank raw m)
    (S : Space (z:=z) (B:=B) (D:=D) T N wire id fixedBase compactBase ctrl bank)
    (x : Job w) (memX : x∈jobs T N wire id) (frame : agreesOutside x.start x.finish out m) :
    Mount T id L (D:=D) fixedBase compactBase bank raw out :=
  Mount.frame T id L fixedBase compactBase M fun a ha => frame a (S.inputs a ha x memX)

private theorem addrParts (start count a : ℕ) (x : Job w) (apart : separated start count x)
    (lo : start≤a) (hi : a < start+count) : a<x.start ∨ x.finish≤a := away_at apart lo hi

variable {k : ℕ} (initial : Term w k 4) (gates : List (Term w 1 13)) (data : Fin (k+1)→Word w)

private theorem read_group (model : Models T N wire id L page power logical fixedBase compactBase raw)
    (shape : (Shape (p:=p) (h:=h) T N)) (space : (Space (z:=z) (B:=B) (D:=D) T N wire id fixedBase compactBase (data (Fin.last k)) bank))
    (ops : 12+gates.length≤2^w) (work : StableCompactNativeBudget.budget power<2^w)
    (pinFit : ∀ i : Fin (T.r+T.s),2+arity i<2^w)
    (tagFit : ∀ i (r : Fin (N i).cells) j,metadata id (N i) r j<2^w)
    (mapFit : ∀ i : Fin (T.r+T.s), ∀ x : Fin (arity i),∀ d : ℕ,∀ mem : ℕ→ℕ,
      HistoryMotifMaps.formula.Fits w (fun _ => d) mem (mapRegs T raw i.val x.val))
    (i : Fin (T.r+T.s)) (m : Memory w) (installed : (Mount (w:=w) T id L (D:=D) fixedBase compactBase bank raw) m)
    (cursor : m ((data (Fin.last k))).val=((bank+21*i.val:ℕ):Word w)) :
    readJobs (HistorySelectedOps.rows initial gates) data (data (Fin.last k)) (group T N wire id i) m := by
  let a : Job w := leafJob T N id i
  let b : Job w := mapJob T N wire i
  let c : Job w := joinJob T N wire id i
  let m₁ := after (data (Fin.last k)) [a] m
  let m₂ := after (data (Fin.last k)) [a,b] m
  have ma : a∈jobs T N wire id := group_mem T N wire id i _ (by simp [group,a])
  have mb : b∈jobs T N wire id := group_mem T N wire id i _ (by simp [group,b])
  have mc : c∈jobs T N wire id := group_mem T N wire id i _ (by simp [group,c])
  have m₁ok : (Mount (w:=w) T id L (D:=D) fixedBase compactBase bank raw) m₁ := installed.previous T N wire id L fixedBase compactBase space _ (by simpa using ma)
  have m₂ok : (Mount (w:=w) T id L (D:=D) fixedBase compactBase bank raw) m₂ := installed.previous T N wire id L fixedBase compactBase space _
    (by
      intro y hy
      rcases List.mem_cons.mp hy with rfl|hy
      · exact ma
      · rcases List.mem_singleton.mp hy with rfl
        exact mb)
  have c₁ : m₁ ((data (Fin.last k))).val=((bank+21*i.val+7:ℕ):Word w) := by
    rw [show m₁ ((data (Fin.last k))).val=m ((data (Fin.last k))).val+(7*[a].length:ℕ) from cursor_after (data (Fin.last k)) (by simpa using space.ctrlOutput a ma),cursor]
    push_cast; simp
  have c₂ : m₂ ((data (Fin.last k))).val=((bank+21*i.val+14:ℕ):Word w) := by
    have disjoint : ∀ x∈[a,b],((data (Fin.last k))).val<x.start ∨ x.finish≤((data (Fin.last k))).val := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl|hx
      · exact space.ctrlOutput a ma
      · rcases List.mem_singleton.mp hx with rfl
        exact space.ctrlOutput b mb
    rw [show m₂ ((data (Fin.last k))).val=m ((data (Fin.last k))).val+(7*[a,b].length:ℕ) from cursor_after (data (Fin.last k)) disjoint,cursor]
    push_cast; simp; ring
  have rows : a.count=4*(N i).cells := shape.count i
  have maps : b.count=arity i := shape.pins i
  have counts : c.count=4*(N i).cells := shape.count i
  have ab : separated a.start a.count b := space.split i i 0 1 (by simp)
  have ac : separated a.start a.count c := space.split i i 0 2 (by simp)
  have bc : separated b.start b.count c := space.split i i 1 2 (by simp)
  change _ ∧ _ ∧ _ ∧ True
  refine ⟨?_,?_,?_,trivial⟩
  · intro ptr mem lo hi frame
    have M := installed.during T N wire id L fixedBase compactBase space a ma frame
    have cur : mem ((data (Fin.last k))).val=((bank+21*i.val+7*(0:ℕ):ℕ):Word w) := by
      rw [frame _ (space.ctrlOutput a ma),cursor];simp
    have cm := M.banks.current T data i 0 space.tape (by omega) cur
    change ptr.val < a.start+a.count at hi
    rw [rows] at hi
    obtain ⟨r,j,hptr⟩ := cursorIndex a.start (N i).cells ptr lo hi
    have header := M.banks.leaf T i _ cm.2 space.argv
    have read := leaf_read T N wire id L page power logical fixedBase compactBase initial gates data mem raw i
      ptr r j model M.archive ops work space.lut space.comp cm.1 header hptr
    exact read.trans (by change _=metadataWord _ _ a.start ptr.val;rw [hptr,atMetadata])
  · intro ptr mem lo hi frame
    have M := m₁ok.during T N wire id L fixedBase compactBase space b mb frame
    have cur : mem ((data (Fin.last k))).val=((bank+21*i.val+7*(1:ℕ):ℕ):Word w) := by
      exact (frame _ (space.ctrlOutput b mb)).trans c₁
    have cm := M.banks.current T data i 1 space.tape (by omega) cur
    change b.start ≤ ptr.val at lo
    change ptr.val < b.start+b.count at hi
    rw [maps] at hi
    let x : Fin (arity i) := ⟨ptr.val-b.start,by omega⟩
    have atPtr : ptr.val=b.start+x.val := by dsimp [x];omega
    have read := map_read T initial gates data mem ptr raw i.val x.val ops cm.1
      (M.banks.pins T i _ ptr cm.2 x.val atPtr space.argv (by omega)) (mapFit i x _ _)
    exact read.trans (congrArg (fun z : ℕ => (z:Word w)) (model.mapWords i x))
  · intro ptr mem lo hi frame
    have M := m₂ok.during T N wire id L fixedBase compactBase space c mc frame
    have cur : mem ((data (Fin.last k))).val=((bank+21*i.val+7*(2:ℕ):ℕ):Word w) := by
      exact (frame _ (space.ctrlOutput c mc)).trans c₂
    have cm := M.banks.current T data i 2 space.tape (by omega) cur
    change ptr.val < c.start+c.count at hi
    rw [counts] at hi
    obtain ⟨r,j,hptr⟩ := cursorIndex c.start (N i).cells ptr lo hi
    have header := M.banks.join T i _ cm.2 space.argv
    have child : Records id (N i) a.start mem := by
      intro u f
      let atRow := a.start+(4*u.val+f.val)
      have start : a.start≤atRow := Nat.le_add_right ..
      have stop : atRow<a.finish := by change atRow<a.start+a.count;rw [rows];dsimp [atRow];have := u.isLt;have := f.isLt;omega
      have ne : atRow≠((data (Fin.last k))).val := by have := space.ctrlOutput _ ma;omega
      have qb : atRow<b.start ∨ b.finish≤atRow := addrParts _ _ _ _ ab start stop
      change mem atRow=_
      rw [frame _ (addrParts _ _ _ _ ac start stop)]
      change after (data (Fin.last k)) [b] m₁ atRow=_
      rw [after_away (data (Fin.last k)) [b] m₁ atRow ne (by simpa using qb),show m₁ atRow=a.word atRow from written (data (Fin.last k)) a m atRow ne start stop]
      exact atMetadata _ _ _ u f
    have pins : ∀ t,t<b.count → mem (b.start+t)=(pinAddress T N wire i t:Word w) := by
      intro idx hidx
      let atPin := b.start+idx
      have start : b.start≤atPin := Nat.le_add_right ..
      have stop : atPin<b.finish := Nat.add_lt_add_left hidx _
      have ne : atPin≠((data (Fin.last k))).val := by have := space.ctrlOutput _ mb;omega
      change mem atPin=_
      rw [frame _ (addrParts _ _ _ _ bc start stop)]
      change after (data (Fin.last k)) [b] m₁ atPin=_
      rw [written (data (Fin.last k)) b m₁ atPin ne start stop]
      change (pinAddress T N wire i (b.start+idx-b.start):Word w)=_
      simp
    have eval := HistorySelectedOps.copy_record initial gates data mem (fun _ => ptr) N wire id (joinHeader T i)
      i r j (pinAddress T N wire i) ops cm.1 header ((Fin.cast_val_eq_self ptr).symm.trans
        (congrArg (fun v : ℕ => (v : Word w)) hptr))
      (fun u => by simp [pinAddress,u.isLt]) ⟨maps,shape.parent,shape.offset i⟩
      (by have := space.finishes _ ma;change a.start+a.count<2^w at this;rw [rows] at this;exact this.le)
      (space.finishes _ mb).le (by simpa only [joinHeader,shape.pins] using pinFit i)
      (tagFit i r j) child pins
    apply eval.trans
    change _ = metadataWord (N i).cells
      (fun v f => metadata id (glue N wire) (finSigmaFinEquiv ⟨i,v⟩) f) c.start ptr.val
    rw [hptr, atMetadata]

theorem before_index {n : ℕ} {i : Fin n} {before rest : List (Fin n)}
    (order : List.finRange n=before++i::rest) : before.length=i.val := by
  have room : before.length<(List.finRange n).length := by rw [order,List.length_append,List.length_cons];omega
  have here : (List.finRange n)[before.length]?=some i := by
    rw [order,List.getElem?_append_right le_rfl]
    simp
  rw [List.getElem?_eq_getElem room] at here
  simpa using congrArg Fin.val (Option.some.inj here)

/-- All three commands for all physical children execute in order, with the
same underlying source, map and copied-record writes as the semantic jobs. -/
theorem read_jobs (model : Models T N wire id L page power logical fixedBase compactBase raw)
    (shape : (Shape (p:=p) (h:=h) T N)) (space : (Space (z:=z) (B:=B) (D:=D) T N wire id fixedBase compactBase (data (Fin.last k)) bank))
    (ops : 12+gates.length≤2^w) (work : StableCompactNativeBudget.budget power<2^w)
    (pins : ∀ i : Fin (T.r+T.s),2+arity i<2^w)
    (small : ∀ i (r : Fin (N i).cells) j,metadata id (N i) r j<2^w)
    (mapFit : ∀ i : Fin (T.r+T.s), ∀ x : Fin (arity i),∀ d : ℕ,∀ mem : ℕ→ℕ,
      HistoryMotifMaps.formula.Fits w (fun _ => d) mem (mapRegs T raw i.val x.val))
    (m : Memory w) (installed : (Mount (w:=w) T id L (D:=D) fixedBase compactBase bank raw) m) (cursor : m ((data (Fin.last k))).val=(bank:Word w)) :
    readJobs (HistorySelectedOps.rows initial gates) data (data (Fin.last k)) (jobs T N wire id) m := by
  apply read_children
  intro before i rest order
  let earlier := before.flatMap (group (w:=w) T N wire id)
  have included : ∀ x∈earlier, x∈jobs T N wire id := by
    intro x hx
    rw [jobs,order,List.flatMap_append]
    exact List.mem_append_left _ hx
  have m' := installed.previous T N wire id L fixedBase compactBase space earlier included
  apply read_group T N wire id L page power logical fixedBase compactBase initial gates data
    model shape space ops work pins small mapFit i _ m'
  have effect := cursor_after (m:=m) (data (Fin.last k)) (xs:=earlier) (fun x hx => space.ctrlOutput x (included x hx))
  have count : earlier.length=3*i.val := (grouped_length T N wire id before).trans (congrArg (3*·) (before_index order))
  rw [effect,count,cursor,←Nat.cast_add]
  congr 1
  ring

omit [CommRing F] [Fintype F] in
/-- The final command of every child writes a complete parent interval.
Later child outputs occupy disjoint intervals of the same assembled stream. -/
theorem records_after (shape : (Shape (p:=p) (h:=h) T N)) (space : Space (z:=z) (B:=B) (D:=D) T N wire id fixedBase compactBase ctrl bank)
    (base : ℕ) (placement : ∀ i,(T.row i.val).dest=base+4*Diagonal.HistoryContraction.Tree.before
      (fun j => (N j).cells) i) (m : Memory w) :
    Records id (glue N wire) base (after ctrl (jobs T N wire id) m) := by
  apply records_of_intervals
  intro i r j
  obtain ⟨before,rest,order⟩ := List.append_of_mem (List.mem_finRange i)
  let groups := group (w:=w) T N wire id
  let a := leafJob (w:=w) T N id i
  let b := mapJob (w:=w) T N wire i
  let c := joinJob (w:=w) T N wire id i
  let addr := c.start+(4*r.val+j.val)
  have lo : c.start≤addr := Nat.le_add_right ..
  have hi : addr<c.finish := by change addr<c.start+(T.row i.val).count;rw [shape.count];have := r.isLt;have := j.isLt;dsimp [addr];omega
  have cm := group_mem T N wire id i c (by simp [c,group])
  have ne : addr≠ctrl.val := by have := space.ctrlOutput c cm;omega
  have afterRest (y) (hy : y∈rest.flatMap groups) : addr<y.start ∨ y.finish≤addr := by
    obtain ⟨z,hz,hy⟩ := List.mem_flatMap.mp hy
    have notI : i∉rest := by
      have h := List.nodup_finRange (T.r+T.s)
      rw [order,List.nodup_append] at h
      exact (List.nodup_cons.mp h.2.1).1
    have diff : i≠z := fun e => notI (e ▸ hz)
    obtain ⟨op,hop⟩ := List.mem_iff_get.mp hy
    have sep := space.split i z (2:Fin 3) op (fun h => diff (congrArg Prod.fst h))
    rw [←hop]
    exact away_at sep lo hi
  rw [←placement i]
  change after ctrl (jobs T N wire id) m addr=_
  rw [jobs,order,List.flatMap_append,List.flatMap_cons,after_append,after_append]
  rw [after_away _ _ _ addr ne afterRest]
  change after ctrl [c] (after ctrl [a,b] (after ctrl (before.flatMap groups) m)) addr=_
  rw [written _ _ _ _ ne lo hi]
  exact atMetadata (w:=w) (N i).cells
    (fun row col => metadata id (glue N wire) (finSigmaFinEquiv ⟨i,row⟩) col)
    (T.row i.val).dest r j

end

end ThreeFlat.RAM.HistoryPartyTapeRun

namespace ThreeFlat.RAM.HistoryPartyTapeRun

open HistoryCompiledRows HistoryPartySpecialization HistoryPartyHeader
open Diagonal Diagonal.MotifOrderedCells Diagonal.MotifOuterTerms Diagonal.MotifSelectorChecks
open private component_left component_right from OAI.ThreeFlat.Diagonal.MotifSelectorChecks
open private pieces_left pieces_right from OAI.ThreeFlat.Diagonal.MotifOrderedCells
open scoped Classical BigOperators
noncomputable section

variable {F : Type} [CommRing F] [Fintype F]
variable {r s e k b d B n ar h p : ℕ}

private abbrev tableId (g : (Fin 3 → Bool) → F) : ℕ := (Fintype.equivFin _ g).val

private def sameRows {a b : ℕ} (X : BitNetwork F a) (Y : BitNetwork F b) : Prop :=
  ∃ size : X.cells=Y.cells, ∀ (r : Fin X.cells) (j : Fin 4),
    metadata tableId X r j=metadata tableId Y (Fin.cast size r) j

omit [CommRing F] in
private theorem sameRows_refl {a : ℕ} (X : BitNetwork F a) : sameRows X X :=
  ⟨rfl, fun _ _ => rfl⟩

omit [CommRing F] in
private theorem sameRows_heq {a b : ℕ} {X : BitNetwork F a} {Y : BitNetwork F b}
    (width : a=b) (net : HEq X Y) : sameRows X Y := by
  subst b
  obtain rfl := eq_of_heq net
  exact sameRows_refl _

private theorem models_of_split (T : HistoryBatchTape.Header) (raw : ℕ→ℕ) (hr : T.r=r) (hs : T.s=s)
    {arities : Fin (r+s)→ℕ} (nets : ∀ i, BitNetwork F (arities i))
    (wires : ∀ i, Fin (arities i) → BitSource h p) (L : HistoryStaticArchive.Catalog F n ar)
    (page : Fin n) (power : Fin (B+1)) (logical fixedBase compactBase : ℕ)
    (lut : T.lut=![fixedBase,HistoryStaticArchive.stride ar,page.val])
    (comp : T.comp=![2^power.val,logical,StableCompactROMNative.pageBase B compactBase power.val])
    (small : logical≤2^power.val)
    (left : ∀ i : Fin r,sameRows (nets (i.castAdd s)) (L.rows page))
    (right : ∀ j : Fin s,sameRows (nets (Fin.natAdd r j)) (MotifNativeCompactors.partialInput F logical power.val))
    (maps : ∀ (j : Fin (r+s)) (x : Fin (arities j)), HistoryMotifMaps.word (kindAt T j.val) x.val
      (partAt T j.val) T.r T.b T.e T.d T.alphabet (quotaAt T raw j.val)=BitLayout.sourceAddress (wires j x)) :
    let I := Fin.cast (congrArg₂ Nat.add hr hs)
    Models T (fun i => nets (I i)) (fun i => wires (I i)) tableId L page power logical fixedBase compactBase raw := by
  let I := Fin.cast (congrArg₂ Nat.add hr hs)
  have la (i : Fin (T.r+T.s)) (hlt : i.val<T.r) : sameRows (nets (I i)) (L.rows page) := by
    let j : Fin r := ⟨i.val, by omega⟩
    have hi : I i=j.castAdd s := Fin.ext rfl
    rw [hi]
    exact left j
  have ra (i : Fin (T.r+T.s)) (hge : ¬i.val<T.r) :
      sameRows (nets (I i)) (MotifNativeCompactors.partialInput F logical power.val) := by
    let j : Fin s := ⟨i.val-r, by have := i.isLt; omega⟩
    have hi : I i=Fin.natAdd r j := Fin.ext (by change i.val=r+(i.val-r); omega)
    rw [hi]
    exact right j
  refine ⟨lut,comp,small,fun i hi => (la i hi).choose,fun i hi => (la i hi).choose_spec,
    fun i hi => (ra i hi).choose,fun i hi => (ra i hi).choose_spec,?_⟩
  intro i x
  rw [pinAddress,dite_eq_left x.isLt,HistoryCompiledRows.pin_address]
  exact maps (I i) x

variable {H : Type*} (tile : Tile F H e d b) (good : (Fin (e*k)→Bool)→Prop)
    (letter : (Fin (e*k)→Bool)→Fin s) (tp : b+(e*d+e*d)≤ar) (sp : e*k+s≤ar)
    (A : Registers) (raw : ℕ→ℕ) (t : Fin (B+1)) (read : Reads A raw (HistoryStaticArchive.all F ar) r t)


/-- The check batch uses the selected bounded check LUT, the shortened counter network,
and the individual quota loaded from each occupied histogram coordinate. -/
theorem checks_models (z : Histogram (Fin s) r) (small : r≤2^t.val)
    (lutStride : A.lutStride=HistoryStaticArchive.stride ar)
    (compStride : A.compStride=StableCompactROMPool.page B 12)
    (quota : ∀ a : Fin s,raw (raw (A.incident+1)+a.val)=(z.val a).val) :
    let dims := checks_fields tile good letter tp sp A raw t read
    let I := Fin.cast (congrArg₂ Nat.add dims.1 dims.2.1)
    let X := components good letter (MotifNativeCompactors.partialInput F r t.val) z
    Models (batch A (HistoryPartySpecialization.kind tile good letter tp sp) raw true) (fun i => (X (I i)).net) (fun i => (X (I i)).wire) tableId
      (HistoryStaticArchive.all F ar) (HistoryStaticArchive.index F ar sp (checkLut (F:=F) good letter)) t r A.lutBase A.compBase raw := by
  let dims := checks_fields tile good letter tp sp A raw t read
  let X := components good letter (MotifNativeCompactors.partialInput F r t.val) z
  apply models_of_split (batch A (HistoryPartySpecialization.kind tile good letter tp sp) raw true) raw dims.1 dims.2.1 (fun i => (X i).net) (fun i => (X i).wire)
    (HistoryStaticArchive.all F ar) (HistoryStaticArchive.index F ar sp (checkLut (F:=F) good letter)) t r A.lutBase A.compBase
  · simp only [batch,HistoryPartySpecialization.kind,ite_true,lutStride]
  · simp [batch,HistoryPartySpecialization.kind,read.copies,read.exponent,read.dyadic,compStride,
      StableCompactROMNative.pageBase,Nat.mul_comm]
  · exact small
  · intro i
    dsimp only [X]
    rw [component_left good letter (MotifNativeCompactors.partialInput F r t.val) z i]
    exact sameRows_heq (HistoryStaticArchive.arity_index F ar sp _).symm
      (HistoryStaticArchive.row_index F ar sp _).symm
  · intro i
    dsimp only [X]
    rw [component_right good letter (MotifNativeCompactors.partialInput F r t.val) z i]
    exact sameRows_refl _
  · refine Fin.addCases ?_ ?_
    · intro i
      dsimp only [X]
      rw [component_left good letter (MotifNativeCompactors.partialInput F r t.val) z i]
      simpa [kindAt,partAt,quotaAt,batch,HistoryPartySpecialization.kind,read.copies,i.isLt]
        using (fun x : Fin (e*k+s) => HistoryMotifMaps.localTest_source i x e d 0)
    · intro a
      dsimp only [X]
      rw [component_right good letter (MotifNativeCompactors.partialInput F r t.val) z a]
      simpa [kindAt,partAt,quotaAt,batch,HistoryPartySpecialization.kind,read.copies,quota a]
        using (fun x : Fin (r+(r+r)) => HistoryMotifMaps.counter_source (b:=e*k) z a x e d)

/-- The payload batch uses the canonical checked tile page and restricts every stream
compactor to the active number of digit positions. -/
theorem payload_models (small : r*d≤2^t.val)
    (lutStride : A.lutStride=HistoryStaticArchive.stride ar)
    (compStride : A.compStride=StableCompactROMPool.page B 12) :
    let dims := payload_fields tile good letter tp sp A raw t read
    let I := Fin.cast (congrArg₂ Nat.add dims.1 dims.2.1)
    let X := pieces (checkedTile tile.rule tile.table) (MotifNativeCompactors.partialInput F (r*d) t.val)
    Models (batch A (HistoryPartySpecialization.kind tile good letter tp sp) raw false) (fun i => (X (I i)).N) (fun i => (X (I i)).wire) tableId
      (HistoryStaticArchive.all F ar) (HistoryStaticArchive.index F ar tp (tileTable tile)) t (r*d) A.lutBase A.compBase raw := by
  let dims := payload_fields tile good letter tp sp A raw t read
  let X := pieces (checkedTile tile.rule tile.table) (MotifNativeCompactors.partialInput F (r*d) t.val)
  apply models_of_split (batch A (HistoryPartySpecialization.kind tile good letter tp sp) raw false) raw dims.1 dims.2.1 (fun i => (X i).N) (fun i => (X i).wire)
    (HistoryStaticArchive.all F ar) (HistoryStaticArchive.index F ar tp (tileTable tile)) t (r*d) A.lutBase A.compBase
  · simp only [batch,HistoryPartySpecialization.kind,Bool.false_eq_true,ite_false,lutStride]
  · simp [batch,HistoryPartySpecialization.kind,read.copies,read.exponent,read.dyadic,compStride,
      StableCompactROMNative.pageBase,Nat.mul_comm]
  · exact small
  · intro i
    dsimp only [X]
    rw [pieces_left (checkedTile tile.rule tile.table) (MotifNativeCompactors.partialInput F (r*d) t.val) i]
    simp only [tileTable_at]
    exact sameRows_heq (HistoryStaticArchive.arity_index F ar tp _).symm
      (HistoryStaticArchive.row_index F ar tp _).symm
  · intro a
    dsimp only [X]
    rw [pieces_right (checkedTile tile.rule tile.table) (MotifNativeCompactors.partialInput F (r*d) t.val) a]
    exact sameRows_refl _
  · refine Fin.addCases ?_ ?_
    · intro i
      dsimp only [X]
      rw [pieces_left (checkedTile tile.rule tile.table) (MotifNativeCompactors.partialInput F (r*d) t.val) i]
      simpa [kindAt,partAt,quotaAt,batch,HistoryPartySpecialization.kind,read.copies,i.isLt]
        using (fun x : Fin (b+(e*d+e*d)) => HistoryMotifMaps.tile_source i x s 0)
    · intro a
      dsimp only [X]
      rw [pieces_right (checkedTile tile.rule tile.table) (MotifNativeCompactors.partialInput F (r*d) t.val) a]
      simpa [kindAt,partAt,quotaAt,batch,HistoryPartySpecialization.kind,read.copies]
        using (fun x : Fin ((r*d)+(r*d+r*d)) => HistoryMotifMaps.stream_source (b:=b) a x s 0)


end
end ThreeFlat.RAM.HistoryPartyTapeRun

end OAI
