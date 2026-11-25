import OAI.Hierarchy.DescentZipBook
import OAI.Hierarchy.DescentDatedReturnMetadata
import OAI.Hierarchy.DescentBundleTerminal
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Reset occupancy and flattened arity from the funded site and scalar span pages -/
namespace Hierarchy.DescentResetMetadataInputs
open DescentSIMDLookup DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {N K H G M w a b c : ℕ}

def increment (x : Cell b) (acc : Cell c) : Cell c := if x=0 then acc else acc+1
def occupied (j : Fin N) (paid : Cell a) (_ : Cell 0) : Cell c := if j.val<paid.val then 1 else 0
def gates (N a b c : ℕ) : Fin (N+1)→Book.Gate :=
  Fin.cases ⟨b,c,c,increment⟩ (fun i=>⟨a,0,c,occupied i⟩)
def unit (a b c : ℕ) :=max a (b+c)
def words (N a b c M : ℕ) :=(N+1)*(2*2^(unit a b c*M))
def endAddress (floor N a b c M : ℕ) :=floor+words N a b c M
def program (floor N a b c M w : ℕ) :=Book.install (gates N a b c) (unit a b c) M w floor
def image (floor N a b c M : ℕ) (m : Memory w) :=Book.image (gates N a b c) (unit a b c) M floor m
def clock (N a b c M : ℕ) :=4+10*words N a b c M
def table (floor N a b c M : ℕ) :=Book.tables (gates N a b c) (unit a b c) M floor
private theorem caps (j : Fin (N+1)) : (gates N a b c j).left+(gates N a b c j).right≤unit a b c :=by
  refine Fin.cases (Nat.le_max_right ..) (fun i=>?_) j
  change a+0≤ max a (b+c)
  simp

theorem any (floor N a b c M : ℕ) (m : Memory w) (space : endAddress floor N a b c M<2^w) :
    (program floor N a b c M w).Exec m (image floor N a b c M m) (clock N a b c M) ∧
    CheapCode (program floor N a b c M w) ∧
    ∀t,t<floor ∨ endAddress floor N a b c M≤t→image floor N a b c M m t=m t :=by
  obtain ⟨run,_,frame,cpu⟩:=Book.mount (gates N a b c) (unit a b c) M floor m caps space
  exact ⟨run,cpu,frame⟩

def tally (tab : Tables) (f6 : Fin K→Expr) : List (Fin K)→Expr
  | []=>.lit 0
  | i::is=>tab.read (f6 i) (tally tab f6 is)

def exprs {B : ℕ} (floor N a b c M : ℕ) (paid : Fin B→Expr) (f6 : Fin B→Fin N→Fin K→Expr)
    (field : Fin 2) (x : Fin B) (node : Fin N) : Expr :=
  if field=0 then (table floor N a b c M node.succ).read (paid x) (.lit 0)
  else tally (table floor N a b c M 0) (f6 x node) (List.finRange K)

def countOn (state : Fin K→Cell b) (ls : List (Fin K)) : ℕ := (ls.filter (fun j=>state j≠0)).length

private theorem zero (c : ℕ) (m : Memory w) :
    Source (.lit 0) (fun (_ : Fin H) (_ : Fin G)=>(0:Cell c)) M m :=by
  intro z
  change (0:Word w)=((data (fun _ : Fin H=>fun _ : Fin G=>(0:Cell c)) z).val:Word w)
  have h : (data (fun _ : Fin H=>fun _ : Fin G=>(0:Cell c)) z).val=0 :=by
    change (finFunctionFinEquiv (fun i : Fin M=>if _ : z.2.val*M+i.val<G then (0:Cell c) else 0)).val=0
    simp
  rw [h,Nat.cast_zero]

private theorem tally_source (tab : Tables) (a₀ : Fin K→Expr) (m : Memory w) (top : ℕ)
    (fit : ∀j,(a₀ j).Fits w top) (vals : Fin K→Fin H→Fin G→Cell b) (seen : ∀j,Source (a₀ j) (vals j) M m)
    (shift : tab.shift.Fits w top) (applyRoom : tab.apply.Fits w top) (sh : tab.shift.bits=b*M)
    (ap : tab.apply.bits=(b+c)*M) (static : Static tab (increment (b:=b) (c:=c)) M m) (ls : List (Fin K)) :
    (tally tab a₀ ls).Fits w top ∧
    Source (tally tab a₀ ls) (fun h g=>(countOn (fun j=>vals j h g) ls : Cell c)) M m := by
  induction ls with
  | nil=>exact ⟨trivial,zero c m⟩
  | cons i is ih=>
    have geom : Fits tab (a₀ i) (tally tab a₀ is) b c M top w:=⟨fit i,ih.1,shift,applyRoom,sh,ap⟩
    refine ⟨⟨geom.apply,geom.right,geom.shift,geom.left⟩,?_⟩
    have read:=read_data tab _ _ top geom increment (by simp [increment]) m static _ _ (seen i) ih.2
    have value : (fun h : Fin H => fun g : Fin G =>
        (countOn (fun j=>vals j h g) (i::is) : Cell c)) =
        (fun h g=>increment (vals i h g) (countOn (fun j=>vals j h g) is : Cell c)) := by
      funext h g
      by_cases z : vals i h g=0 <;> simp [countOn,increment,z,Nat.cast_add,Nat.cast_one]
    rw [value]
    exact read

/-- The same finite book handles every successor block. The expressions read arbitrary
previously emitted packed fields, including a directly retained f6 before the pointer join. -/
theorem issued {B : ℕ} (floor N a b c M : ℕ) (m : Memory w) (paid : Fin B→Expr)
    (f6 : Fin B→Fin N→Fin K→Expr) (amount : Fin B→Fin H→Fin G→Cell a)
    (spans : Fin B→Fin N→Fin K→Fin H→Fin G→Cell b)
    (heldPaid : ∀x,(paid x).Fits w floor) (heldSpan : ∀x n j,(f6 x n j).Fits w floor)
    (paidRead : ∀x,Source (paid x) (amount x) M m) (spanRead : ∀x n j,Source (f6 x n j) (spans x n j) M m)
    (space : endAddress floor N a b c M<2^w) (f : Fin 2) (x : Fin B) (n : Fin N) :
    let op:=exprs floor N a b c M paid f6 f x n
    op.Fits w (endAddress floor N a b c M) ∧ Source op (fun h g=>if f=0 then occupied n (amount x h g) 0 else
      (countOn (fun j=>spans x n j h g) (List.finRange K):Cell c)) M (image floor N a b c M m) :=by
  let top:=endAddress floor N a b c M
  let mem:=image floor N a b c M m
  let t:=table floor N a b c M
  have mounted:=Book.mount (gates N a b c) (unit a b c) M floor m caps space
  have geom (j : Fin (N+1)):=Book.geometry (gates N a b c) (unit a b c) M floor j
    (out:=top) le_rfl space (caps j)
  have prior {T : ℕ} (e : Expr) (v : Fin H→Fin G→Cell T) (ok : e.Fits w floor) (yes : Source e v M m) :
      e.Fits w top ∧ Source e v M mem:=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) ok,
     fun z=>(eval_below e ((row H G M z).val:Word w) m mem ok (fun p h=>mounted.2.2.1 p (.inl h))).trans (yes z)⟩
  by_cases first : f=0
  · simp only [exprs,first,ite_true]
    have p₀:=prior _ _ (heldPaid x) (paidRead x)
    have dimensions : Fits (t n.succ) (paid x) (.lit 0) a 0 M top w:=
      ⟨p₀.1,trivial,(geom n.succ).1,(geom n.succ).2,rfl,rfl⟩
    exact ⟨⟨dimensions.apply,dimensions.right,dimensions.shift,dimensions.left⟩,
      read_data _ _ _ top dimensions (occupied n) (by simp [occupied]) mem
        (mounted.2.1 n.succ) _ _ p₀.2 (zero 0 mem)⟩
  · simp only [exprs,first,ite_false]
    have each j:=prior _ _ (heldSpan x n j) (spanRead x n j)
    exact tally_source (t 0) (f6 x n) mem top (fun j=>(each j).1) (spans x n) (fun j=>(each j).2)
      (geom 0).1 (geom 0).2 rfl rfl (mounted.2.1 0) (List.finRange K)

theorem expr_work {B : ℕ} (floor N a b c M q : ℕ) (paid : Fin B→Expr) (f6 : Fin B→Fin N→Fin K→Expr)
    (cheap : ∀x,(paid x).work≤q) (cost : ∀x n j,(f6 x n j).work≤q) (f : Fin 2) (x : Fin B) (n : Fin N) :
    (exprs floor N a b c M paid f6 f x n).work≤(q+13)+(q+11)*K :=by
  have walk (ls : List (Fin K)) : (tally (table floor N a b c M 0) (f6 x n) ls).work≤1+ls.length*(q+11):=by
    induction ls with
    | nil=>simp [tally,Expr.work]
    | cons j is ih=>have hj:=cost x n j;simp only [tally,List.length_cons,Nat.succ_mul,work] at *;omega
  by_cases ff : f=0
  · simp only [exprs,ff,ite_true,work,Expr.work]
    have:=cheap x
    omega
  · simp only [exprs,ff,ite_false]
    have hw:=walk (List.finRange K)
    simp only [List.length_finRange] at hw
    rw [Nat.mul_comm (q+11) K]
    omega

theorem expr_fits {B : ℕ} (floor N a b c M : ℕ) (paid : Fin B→Expr)
    (f6 : Fin B→Fin N→Fin K→Expr) (paidFit : ∀x,(paid x).Fits w floor)
    (spanFit : ∀x n j,(f6 x n j).Fits w floor) (space : endAddress floor N a b c M<2^w)
    (f : Fin 2) (x : Fin B) (n : Fin N) :
    (exprs floor N a b c M paid f6 f x n).Fits w (endAddress floor N a b c M) :=by
  let top:=endAddress floor N a b c M
  let t:=table floor N a b c M
  have geom (j : Fin (N+1)):=Book.geometry (gates N a b c) (unit a b c) M floor j
    (out:=top) le_rfl space (caps j)
  have before : floor≤top:=Nat.le_add_right ..
  by_cases ff : f=0
  · simp only [exprs,ff,ite_true]
    exact ⟨(geom n.succ).2,trivial,(geom n.succ).1,ProtocolRAMGeneratedWrite.fits_mono _ before (paidFit x)⟩
  · simp only [exprs,ff,ite_false]
    have walk (is : List (Fin K)) : (tally (t 0) (f6 x n) is).Fits w top:=by
      induction is with
      | nil=>trivial
      | cons j js ih=>exact ⟨(geom 0).2,ih,(geom 0).1,ProtocolRAMGeneratedWrite.fits_mono _ before (spanFit x n j)⟩
    exact walk (List.finRange K)

/-- One count digit for each actual scalar pointer, in exactly the operand order.
In particular a slice containing five p-words contributes *five* positive digits. -/
def argumentSpans {p : ℕ} {U V : Type} {width : V→ℕ} {r : DescentKernelHistory.BitRecipe U V width}
    (shape : DescentBundleHistory.Shape p r) (u : r.Node) : List ℕ :=
  (shape.rows u).flatMap (List.flatMap (fun s=>List.replicate s.count s.count))

theorem spans_length {p : ℕ} (hp : 0<p) {U V : Type} {width : V→ℕ} {r : DescentKernelHistory.BitRecipe U V width}
    (shape : DescentBundleHistory.Shape p r) (u : r.Node) :
    (argumentSpans shape u).length=(shape.recipe hp).arity u := by
  simp [argumentSpans,DescentBundleHistory.Shape.recipe,DescentBundleHistory.Shape.keys,
    List.length_flatMap,DescentBundleHistory.Slice.names]

theorem positive_span {p : ℕ} {U V : Type} {width : V→ℕ} {r : DescentKernelHistory.BitRecipe U V width}
    (shape : DescentBundleHistory.Shape p r) (u : r.Node) {s : ℕ} (member : s∈argumentSpans shape u) : 0<s := by
  obtain ⟨row,_,part⟩:=List.mem_flatMap.mp member
  obtain ⟨slot,_,copies⟩:=List.mem_flatMap.mp part
  have eqn : s=slot.count :=List.eq_of_mem_replicate copies
  subst s
  by_contra empty
  have zero : slot.count=0:=Nat.eq_zero_of_not_pos empty
  simp [zero] at copies

def argumentSpan {p : ℕ} {U V : Type} {width : V→ℕ} {r : DescentKernelHistory.BitRecipe U V width}
    (shape : DescentBundleHistory.Shape p r) (u : r.Node) (j : ℕ) :=
  ((argumentSpans shape u)[j]?).getD 0

theorem span_occupied {p : ℕ} (hp : 0<p) {U V : Type} {width : V→ℕ} {r : DescentKernelHistory.BitRecipe U V width}
    (shape : DescentBundleHistory.Shape p r) (u : r.Node) (arg : ℕ) :
    0<argumentSpan shape u arg ↔ arg<(shape.recipe hp).arity u := by
  rw [←spans_length hp]
  by_cases live : arg<(argumentSpans shape u).length
  · simpa only [argumentSpan,List.getElem?_eq_getElem live,Option.getD_some,live,iff_true] using
      positive_span shape u (List.getElem_mem (l:=argumentSpans shape u) live)
  · simp [argumentSpan,live]

/-- Lowering the primitive's actual (group,slice,count) header to scalar f6 emits
each count on all of its own occurrences. Inactive addresses past the header read zero. -/
def scalarSpans (fields : List (List DescentBundleHistory.SliceCode)) : List ℕ :=
  fields.flatMap (List.flatMap (fun s=>List.replicate s.count s.count))

theorem tag_spans {p : ℕ} (hp : 0<p) {U V : Type} {width : V→ℕ} {r : DescentKernelHistory.BitRecipe U V width}
    (shape : DescentBundleHistory.Shape p r) (u : r.Node) :
    scalarSpans ((shape.recipe hp).tag u).2=argumentSpans shape u :=by
  simp [scalarSpans,argumentSpans,DescentBundleHistory.Shape.recipe,List.flatMap_map,
    DescentBundleHistory.Slice.code]

/-- When the actor order and scalar pointer publisher provide their original values,
the activity test needed for the compact two-field checkpoint follows with no
additional bitmap. This includes nullary nodes and missing actors. -/
theorem actual_span {p : ℕ} (hp : 0<p) {U V : Type} {width : V→ℕ} {r : DescentKernelHistory.BitRecipe U V width}
    (shape : DescentBundleHistory.Shape p r) (atNode : Option r.Node) (slot : ℕ) (actual : Cell b)
    (source : actual.val=atNode.elim 0 (fun u=>((scalarSpans ((shape.recipe hp).tag u).2)[slot]?).getD 0)) :
    actual≠0 ↔ atNode.isSome ∧ slot<atNode.elim 0 ((shape.recipe hp).arity) :=by
  cases atNode with
  | none=>simp only [Option.elim_none] at source;simp [Fin.ext_iff,source]
  | some u=>
    rw [Option.elim_some,tag_spans] at source
    change actual.val=argumentSpan shape u slot at source
    constructor
    · intro active
      refine ⟨rfl,(span_occupied hp shape u slot).mp ?_⟩
      rw [←source]
      exact Nat.pos_of_ne_zero (fun eqn=>active (Fin.ext eqn))
    · intro present gone
      have positive := (span_occupied hp shape u slot).mpr present.2
      have zero : actual.val=0 := congrArg Fin.val gone
      omega

theorem count_exact (spans : Fin K→Cell b) (arity : ℕ) (room : arity≤K)
    (real : ∀j,spans j≠0 ↔ j.val<arity) : countOn spans (List.finRange K)=arity :=by
  let xs:=(List.finRange K).filter (fun j=>spans j≠0)
  let lift : Fin arity↪Fin K:=Fin.castLEEmb room
  have same : xs.toFinset=Finset.univ.map lift:=by
    ext i
    have inside : i∈Finset.univ.map lift ↔ i.val<arity :=by
      constructor
      · intro yes;obtain ⟨j,_,rfl⟩:=Finset.mem_map.mp yes;exact j.isLt
      · intro ok;exact Finset.mem_map.mpr ⟨⟨i.val,ok⟩,Finset.mem_univ _,Fin.ext rfl⟩
    rw [inside]
    simp [xs,real]
  have nd : xs.Nodup:=List.Nodup.filter _ (List.nodup_finRange K)
  change xs.length=arity
  rw [←List.toFinset_card_of_nodup nd,same,Finset.card_map,Finset.card_univ,Fintype.card_fin]

/-- Convert the measured expressions to checkpoint words on every receiver and group.
The span observation is on each emitted argument coordinate, including absent nodes and
the padding following the final real argument. -/
theorem issued_exact {B : ℕ} (floor N a b c M : ℕ) (m : Memory w) (paid : Fin B→Expr)
    (f6 : Fin B→Fin N→Fin K→Expr) (amount : Fin B→Fin H→Fin G→Cell a)
    (spans : Fin B→Fin N→Fin K→Fin H→Fin G→Cell b) (arity : Fin B→Fin N→Fin H→Fin G→ℕ)
    (bounded : ∀x n h g,arity x n h g≤K)
    (actual : ∀x n j h g,spans x n j h g≠0 ↔ n.val<(amount x h g).val ∧ j.val<arity x n h g)
    (heldPaid : ∀x,(paid x).Fits w floor) (heldSpan : ∀x n j,(f6 x n j).Fits w floor)
    (paidRead : ∀x,Source (paid x) (amount x) M m) (spanRead : ∀x n j,Source (f6 x n j) (spans x n j) M m)
    (space : endAddress floor N a b c M<2^w) (f : Fin 2) (x : Fin B) (n : Fin N) :
    let e:=exprs floor N a b c M paid f6 f x n
    e.Fits w (endAddress floor N a b c M) ∧ Source e
      (fun h g=>if n.val<(amount x h g).val then if f=0 then (1:Cell c) else (arity x n h g:Cell c) else 0) M
      (image floor N a b c M m) :=by
  obtain ⟨fits,source⟩:=issued floor N a b c M m paid f6 amount spans heldPaid heldSpan paidRead spanRead space f x n
  refine ⟨fits,?_⟩
  convert source using 1
  funext h g
  by_cases live : n.val<(amount x h g).val
  · have count:=count_exact (fun j=>spans x n j h g) (arity x n h g) (bounded x n h g)
      (fun j=>by simpa [live] using actual x n j h g)
    simp [live,occupied,count]
  · have count:=count_exact (fun j=>spans x n j h g) 0 (Nat.zero_le _) (fun j=>by simpa [live] using actual x n j h g)
    simp [live,occupied,count]

def paidBank (out H G M : ℕ) {B : ℕ} (x : Fin B) : Bank :=
  ⟨out+x.val*(H*chunks G M),Nat.clog 2 (H*chunks G M+1)⟩

theorem compact_paid {B : ℕ} (out floor : ℕ) (m : Memory w) (x : Fin B) (q : Fin H→Fin G→Cell a)
    (fits : (paidBank out H G M x).Fits w floor)
    (attained : ∀z : Row H G M,m (out+x.val*(H*chunks G M)+(row H G M z).val)=((data q z).val:Word w)) :
    Source (.lookup (paidBank out H G M x) .row) q M m :=
  source_column _ floor fits m q ((Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)) attained

theorem affine (floor N a b c M : ℕ) : endAddress floor N a b c M=floor+endAddress 0 N a b c M :=by simp [endAddress]

theorem headerEnd_eq (v : DescentDatedAddressBook.MetadataReturn) (floor : ℕ) :
    v.headerEnd floor=endAddress floor v.chart.nodes v.paidBits v.spanBits v.chart.bits v.chart.lanes :=rfl

theorem names (floor N a b c M w : ℕ) : DescentStaticWordColumn.names (program floor N a b c M w)=
    15*(words N a b c M+1) :=Book.names ..

end
end Hierarchy.DescentResetMetadataInputs

end OAI
