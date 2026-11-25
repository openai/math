import OAI.ThreeFlat.RAM.NavigationNodeRowProgram
import OAI.ThreeFlat.RAM.HistoryNodeDirectory

namespace OAI
/-! # Chronological publication of physical node headers and scheduler charges

The first pass has recorded the selected children, parent ordinal, motif counts and all
incident widths. Reading them after all stages have returned permits each node to publish
both its dynamic parent and the accumulated work and pair count of its subtree.
-/

namespace ThreeFlat.RAM.NavigationNodeRows

open Computability.VPVNP.BurstRAM PhysicalPinsExpr PhysicalProcedure MotifRows
open scoped Fin.CommRing
variable {W : ℕ}


private theorem test_eq (x y : ℕ) : natTest .eq x y = true ↔ x = y := by
  simp [natTest]

private theorem test_lt (x y : ℕ) : natTest .lt x y = true ↔ x < y := by
  simp [natTest]

/-- Numerically identical to the initial pair slice of a true cursor-zero bucket. -/
theorem leafPairs_read (b : Banks) (mem : ℕ → ℕ) (data : Param → ℕ) (vs : Fin 1 → ℕ) (row : Expr) :
    let i := row.natural W data mem vs
    (leafPairs b row).natural W data mem vs =
      if mem (mem b.current+6)=0 ∧ i<b.lanes then min (b.totalPairs-i*b.perLanePairs) b.perLanePairs else 0 := by
  intro i
  simp only [leafPairs,traceLeaf,h,field,Formula.natural,test_eq,test_lt,natOp]
  dsimp only [i]
  by_cases stage : mem (mem b.current+6)=0 <;>
    by_cases insideLane : row.natural W data mem vs < b.lanes <;>
    by_cases room : b.totalPairs-row.natural W data mem vs*b.perLanePairs<b.perLanePairs <;>
    simp [stage,insideLane,room,min_def] <;> omega

open scoped BigOperators
namespace Banks

def column (b : Banks) (mem : ℕ→ℕ) (j : ℕ) := mem (mem b.current+j)

def childSum (b : Banks) (mem : ℕ→ℕ) (row cap col : ℕ) :=
  ∑ i : Fin cap, if i.val<b.column mem 7 then
    mem (b.charges+mem (b.column mem 8+row*b.column mem 7+i.val)*2+col) else 0

def widthSum (b : Banks) (mem : ℕ→ℕ) (row cap : ℕ) :=
  let base := b.column mem 10+row*2
  ∑ i : Fin cap, if i.val<mem (base+0) then mem (mem (base+1)+(4*i.val+2)) else 0

def copiesSum (b : Banks) (mem : ℕ→ℕ) (row cap : ℕ) :=
  let base := b.column mem 9+row*5
  if b.column mem 6=0 then 0 else
    ∑ i : Fin cap, if i.val<mem (base+3) then mem (mem (base+4)+(6*i.val+3)) else 0

def clippedPairs (b : Banks) (mem : ℕ→ℕ) (row : ℕ) :=
  if b.column mem 6=0 ∧ row<b.lanes then min (b.totalPairs-row*b.perLanePairs) b.perLanePairs else 0

end Banks

open scoped BigOperators
variable (b : Banks) (mem : ℕ→ℕ) (data : Param→ℕ) (vs : Fin 1→ℕ)
local notation "V" => Formula.natural W data mem vs

theorem fromChildren_read (row : Expr) (cap col : ℕ) :
    V (fromChildren b row cap col)=b.childSum mem (V row) cap col := by
  rw [fromChildren,totals_value,List.map_map]
  simp only [←List.ofFn_id,List.map_ofFn,Function.comp_def,List.sum_ofFn,Formula.natural,natOp,test_lt,
    ix,h,plus,field,Banks.childSum,Banks.column,id_eq];
    apply Finset.sum_congr rfl
  all_goals
    intro i _
    by_cases used : i.val < mem (mem b.current+7) <;> simp [used]

theorem incidentWidth_read (row : Expr) (cap : ℕ) :
    V (incidentWidth b row cap)=b.widthSum mem (V row) cap := by
  simp only [incidentWidth,totals_value,←List.ofFn_id,List.map_ofFn,Function.comp_def,List.sum_ofFn,
    Formula.natural,natOp,test_lt,ix,h,field,Banks.widthSum,Banks.column,id_eq,Nat.add_zero];
    apply Finset.sum_congr rfl
  all_goals
    intro i _
    by_cases used : i.val < mem (mem (mem b.current+10) + V row*2) <;> simp [used]

theorem motifCopies_read (row : Expr) (cap : ℕ) :
    V (motifCopies b row cap)=b.copiesSum mem (V row) cap := by
  simp only [motifCopies,Formula.natural,test_eq,test_lt,totals_value,←List.ofFn_id,List.map_ofFn,Function.comp_def,List.sum_ofFn,natOp,ix,h,field,
    Banks.copiesSum,Banks.column,id_eq,Nat.add_zero];
    by_cases seed : mem (mem b.current+6)=0 <;> simp [seed];
    apply Finset.sum_congr rfl
  all_goals
    intro i _
    by_cases used : i.val < mem (mem (mem b.current+9) + V row*5+3) <;> simp [used]

/-- Each real charge row adds its children's stored charges to the actual parsed motif
counts and incident widths. The paired endpoint column counts only the original occupied
cursor buckets and sums their counts without multiplying by the work tariff. -/
theorem charge_read (children halves motifs j : ℕ) (base : vs 0=b.column mem 0+j) :
    let row := j/2
    let pairs := b.clippedPairs mem row
    let work := if b.column mem 6=0 ∧ row<b.lanes then b.traceWork else 0
    V (charge b children halves motifs) =
      if j%2=0 then b.unitWork*(1+(b.widthSum mem row halves+(b.copiesSum mem row motifs+(pairs+work))))+
        b.childSum mem row children 0 else pairs+b.childSum mem row children 1 := by
  intro row pairs work
  have z : V (.cut (.reg 0) (h b 0))=j := by
    change vs 0-b.column mem 0=_
    rw [base,Nat.add_sub_cancel_left]
  simp only [charge,Formula.natural,test_eq,test_lt,natOp,plus,fromChildren_read,incidentWidth_read,
    motifCopies_read,leafPairs_read,traceLeaf,h,field] at *
  simp only [base,Banks.column,Nat.add_sub_cancel_left,row,pairs,Banks.clippedPairs,work]
  by_cases parity : j%2=0 <;> by_cases seed : mem (mem b.current+6)=0 <;>
    by_cases insideLane : j/2<b.lanes <;> simp [parity,seed,insideLane]

end ThreeFlat.RAM.NavigationNodeRows

namespace ThreeFlat.RAM.NavigationNodeRows

open PhysicalPinsExpr MotifRows

/-- The eight words of a published navigation node, read from the current layer directory. -/
def Banks.nodeRecord (b : Banks) (mem : ℕ → ℕ) (row : ℕ) : HistoryNodeDirectory.Node ℕ :=
  let id := b.column mem 5 + row
  { kind := b.column mem 6
    parent := if b.column mem 11=1 then id else b.column mem 12 + mem (b.column mem 13+row)
    ordinal := row
    childPtr := b.column mem 8 + row*b.column mem 7
    childCount := b.column mem 7
    kernelPtr := b.column mem 9 + row*5
    incidentPtr := b.column mem 10 + row*2
    externalCount := 2*mem (b.charges+id*2+1) }

theorem node_read {W : ℕ} (b : Banks) (mem : ℕ → ℕ) (data : Param → ℕ) (vs : Fin 1 → ℕ)
    (row : ℕ) (col : Fin 8) (addr : vs 0=b.column mem 2+8*row+col.val) :
    (node b).natural W data mem vs = (b.nodeRecord mem row).words col := by
  have c := col.isLt
  have quot : (vs 0 - mem (mem b.current+2))/8 = row := by
    change (vs 0 - b.column mem 2)/8 = row
    omega
  have rem : (vs 0 - mem (mem b.current+2))%8 = col.val := by
    change (vs 0 - b.column mem 2)%8 = col.val
    omega
  fin_cases col <;>
    simp [node,pick,List.zipIdx,Formula.natural,natOp,h,field,ix,plus,Banks.nodeRecord,
      Banks.column,HistoryNodeDirectory.Node.words,quot,rem,natTest];
    by_cases last : mem (mem b.current+11)=1 <;> simp [last]


end ThreeFlat.RAM.NavigationNodeRows

namespace ThreeFlat.RAM.NavigationNodeRows

open Computability.VPVNP.BurstRAM PhysicalPinsExpr MotifRows

/-- Address rectangles read when the navigation pass publishes a layer of
node records. The last layer's self-parent branch never reads an owner. -/
structure NodeRoom (W : ℕ) (b : Banks) (mem : ℕ→ℕ) (count : ℕ) : Prop where
  wide : 8<2^W
  control : b.current<2^W
  header : mem b.current+13<2^W
  nodes : b.column mem 2+8*count≤2^W
  owners : b.column mem 11≠1 → b.column mem 13+count≤2^W
  charges : b.charges+2*(b.column mem 5+count)≤2^W
  flag : b.column mem 11<2^W

variable {W : ℕ} (b : Banks) (mem : ℕ→ℕ) (data : Param→ℕ) (vs : Fin 1→ℕ)
local notation "E" => Formula.natural W data mem vs
local notation "Good" => Formula.Fits W data mem vs

private theorem pick_rows_fits (ls : List Expr) (index : Expr) (iok : Good index) (small : E index<2^W)
    (length : ls.length≤2^W) (fields : ∀ f∈ls, Good f) : Good (pick ls index) := by
  have fold (ks : List (Expr×ℕ)) (all : ∀ kv∈ks, Good kv.1 ∧ kv.2<2^W) :
      Good (ks.foldr (fun kv rest => .select .eq index (.lit kv.2) kv.1 rest) (.lit 0)) := by
    induction ks with
    | nil => trivial
    | cons kv ks ih =>
      have one := all kv List.mem_cons_self
      have rest := ih (fun x hx => all x (List.mem_cons_of_mem _ hx))
      exact ⟨iok,trivial,small,one.2,by split <;> first | exact one.1 | exact rest⟩
  apply fold
  rw [List.forall_mem_iff_getElem]
  intro i hi
  have bound : i<ls.length := by simpa only [List.length_zipIdx] using hi
  simpa only [List.getElem_zipIdx,Nat.zero_add] using
    And.intro (fields ls[i] (List.getElem_mem bound)) (bound.trans_le length)

/-- Each real output word of the eight-column node scan is defined at
native word width throughout its selected branch. -/
theorem node_fits (count row : ℕ) (col : Fin 8) (room : NodeRoom W b mem count)
    (hr : row<count) (addr : vs 0=b.column mem 2+8*row+col.val) :
    Good (node b) := by
  have hf (j : ℕ) (hj : j≤13) : Good (h b j) := by
    refine ⟨⟨⟨trivial,room.control⟩,trivial,trivial⟩,?_⟩
    change mem b.current+j<2^W
    have := room.header
    omega
  let z : Expr := .cut (.reg 0) (h b 2)
  let rr : Expr := .op .div z (.lit 8)
  let idx : Expr := .op .mod z (.lit 8)
  let idn := plus (h b 5) rr
  let par : Expr := .select .eq (h b 11) (.lit 1) idn
    (plus (h b 12) (.load (plus (h b 13) rr)))
  have c8 := col.isLt
  have out := room.nodes
  have zval : E z=8*row+col.val := by
    change vs 0-b.column mem 2=_
    omega
  have zsmall : E z<2^W := by rw [zval]; omega
  have zfit : Good z := ⟨trivial,hf 2 (by decide),(by omega : vs 0<2^W),
    (by change b.column mem 2<2^W; omega)⟩
  have rfit : Good rr := ⟨zfit,trivial,zsmall,room.wide⟩
  have idxfit : Good idx := ⟨zfit,trivial,zsmall,room.wide⟩
  have rvalue : E rr=row := by change E z/8=row; rw [zval]; omega
  have idxsmall : E idx<2^W := (Nat.mod_lt (E z) (by decide : 0<8)).trans room.wide
  have idfit : Good idn := ⟨hf 5 (by decide),rfit,trivial⟩
  have idvalue : E idn=b.column mem 5+row := congrArg (b.column mem 5+·) rvalue
  have pfit : Good par := by
    refine ⟨hf 11 (by decide),trivial,room.flag,(by have := room.wide; omega : 1<2^W),?_⟩
    change (if natTest .eq (b.column mem 11) 1 then Good idn else
      Good (plus (h b 12) (.load (plus (h b 13) rr))))
    by_cases last : b.column mem 11=1
    · simpa [natTest,last] using idfit
    · simp only [natTest,decide_eq_true_eq,ite_eq_right last]
      refine ⟨hf 12 (by decide),⟨⟨hf 13 (by decide),rfit,trivial⟩,?_⟩,trivial⟩
      change b.column mem 13+E rr<2^W
      have bound := room.owners last
      omega
  have ixfit (base reg : Expr) (stride off : ℕ) (baseOK : Good base) (regOK : Good reg) :
      Good (ix base reg stride off) :=
    ⟨⟨baseOK,⟨regOK,trivial,trivial⟩,trivial⟩,trivial,trivial⟩
  have pair : Good (.load (ix (.lit b.charges) idn 2 1)) := by
    refine ⟨ixfit _ _ _ _ trivial idfit,?_⟩
    change b.charges+E idn*2+1<2^W
    have bound := room.charges
    omega
  have ptr : Good (plus (h b 8) (.op .mul rr (h b 7))) :=
    ⟨hf 8 (by decide),⟨rfit,hf 7 (by decide),trivial⟩,trivial⟩
  have pins : Good (.op .mul (.lit 2) (.load (ix (.lit b.charges) idn 2 1))) :=
    ⟨trivial,pair,trivial⟩
  change Good (pick [h b 6,par,rr,plus (h b 8) (.op .mul rr (h b 7)),h b 7,
    ix (h b 9) rr 5 0,ix (h b 10) rr 2 0,.op .mul (.lit 2) (.load (ix (.lit b.charges) idn 2 1))] idx)
  apply pick_rows_fits mem data vs _ _ idxfit idxsmall (by exact room.wide.le)
  intro f inList
  simp only [List.mem_cons,List.not_mem_nil,or_false] at inList
  rcases inList with eq|eq|eq|eq|eq|eq|eq|eq <;> subst f
  · exact hf 6 (by decide)
  · exact pfit
  · exact rfit
  · exact ptr
  · exact hf 7 (by decide)
  · exact ixfit _ _ _ _ (hf 9 (by decide)) rfit
  · exact ixfit _ _ _ _ (hf 10 (by decide)) rfit
  · exact pins

end ThreeFlat.RAM.NavigationNodeRows

namespace ThreeFlat.RAM.NavigationNodeRows
open Computability.VPVNP.BurstRAM
open scoped BigOperators


structure LayerData.Reads {s : Layer} (d : LayerData s) (mem : ℕ→ℕ) : Prop where
  child : ∀ j i, mem (s.children+j.val*s.childCount+i.val) = d.child j i
  halves : ∀ j, mem (s.incident+j.val*2) = (d.halfWidth j).length
  width : ∀ j (i : Fin (d.halfWidth j).length),
    mem (mem (s.incident+j.val*2+1)+(4*i.val+2))=(d.halfWidth j)[i]
  motifs : s.kind≠0 → ∀ j, mem (s.kernels+j.val*5+3) = (d.motifCopies j).length
  copies : s.kind≠0 → ∀ j (i : Fin (d.motifCopies j).length),
    mem (mem (s.kernels+j.val*5+4)+(6*i.val+3))=(d.motifCopies j)[i]

structure LayerData.Below {s : Layer} (d : LayerData s) (limit : ℕ) (mem : ℕ→ℕ) : Prop where
  child : ∀ (j : Fin s.count) (i : Fin s.childCount), s.children+j.val*s.childCount+i.val<limit
  halves : ∀ (j : Fin s.count),s.incident+j.val*2+1<limit
  width : ∀ j (i : Fin (d.halfWidth j).length),mem (s.incident+j.val*2+1)+(4*i.val+2)<limit
  motifs : s.kind≠0 → ∀ (j : Fin s.count),s.kernels+j.val*5+4<limit
  copies : s.kind≠0 → ∀ j (i : Fin (d.motifCopies j).length),
    mem (s.kernels+j.val*5+4)+(6*i.val+3)<limit


theorem LayerData.Reads.of_agree {s : Layer} {d : LayerData s} {limit : ℕ} {m m' : ℕ→ℕ}
    (r : d.Reads m) (low : d.Below limit m) (same : ∀ x, x<limit → m' x=m x) : d.Reads m' where
  child j i := (same _ (low.child j i)).trans (r.child j i)
  halves j := (same _ (by have := low.halves j; omega)).trans (r.halves j)
  width j i := by rw [same _ (low.halves j),same _ (low.width j i)]; exact r.width j i
  motifs h j := (same _ (by have := low.motifs h j; omega)).trans (r.motifs h j)
  copies h j i := by rw [same _ (low.motifs h j),same _ (low.copies h j i)]; exact r.copies h j i


end ThreeFlat.RAM.NavigationNodeRows

namespace ThreeFlat.RAM.NavigationNodeRows

open PhysicalPinsExpr
open scoped BigOperators

private theorem zero_padded_sum (f : ℕ→ℕ) {n cap : ℕ} (enough : n≤cap) :
    (∑ i : Fin cap, if i.val<n then f i.val else 0)=∑ i : Fin n,f i.val := by
  induction cap,enough using Nat.le_induction with
  | base => exact Finset.sum_congr rfl (fun i _ => ite_eq_left i.isLt)
  | succ cap cover ih =>
    rw [Fin.sum_univ_castSucc]
    simpa only [Fin.val_castSucc,Fin.val_last,ite_eq_right (Nat.not_lt.mpr cover),Nat.add_zero] using ih

private theorem zero_padded_words (words : List ℕ) (cap : ℕ) (f : ℕ→ℕ) (enough : words.length≤cap)
    (correct : ∀ i : Fin words.length, f i.val=words[i]) :
    (∑ i : Fin cap, if i.val<words.length then f i.val else 0)=words.sum := by
  rw [zero_padded_sum f enough]
  have same : (fun i : Fin words.length => f i.val)=(fun i : Fin words.length => words[i]) :=
    funext correct
  rw [← List.sum_ofFn,same]
  exact congrArg List.sum (List.ofFn_get words)

/-- A physically mounted layer emits exactly its two recursive charge fields. -/
theorem LayerData.charge_natural {W : ℕ} {s : Layer} (d : LayerData s) (b : Banks)
    (p : Parent) (next : ℕ) (mem : ℕ→ℕ) (data : Param→ℕ) (vs : Fin 1→ℕ)
    (prior : ℕ→Fin 2→ℕ) (cc hc mc : ℕ) (j : Fin s.count) (col : Fin 2)
    (reads : d.Reads mem) (mounted : ∀ off<14, b.column mem off=header b s p next off)
    (childCap : s.childCount≤cc) (halves : (d.halfWidth j).length≤hc)
    (motifs : s.kind≠0→(d.motifCopies j).length≤mc)
    (issued : ∀ (i : Fin s.childCount) (c : Fin 2),
      mem (b.charges+2*d.child j i+c.val)=prior (d.child j i) c)
    (addr : vs 0=b.column mem 0+2*j.val+col.val) :
    (charge b cc hc mc).natural W data mem vs = d.cost b prior j col := by
  have h6 : b.column mem 6=s.kind := mounted 6 (by decide)
  have h7 : b.column mem 7=s.childCount := mounted 7 (by decide)
  have h8 : b.column mem 8=s.children := mounted 8 (by decide)
  have h9 : b.column mem 9=s.kernels := mounted 9 (by decide)
  have h10 : b.column mem 10=s.incident := mounted 10 (by decide)
  have child (c : Fin 2) : b.childSum mem j.val cc c.val = ∑ i,prior (d.child j i) c := by
    let f (i : ℕ) := mem (b.charges+mem (s.children+j.val*s.childCount+i)*2+c.val)
    simp only [Banks.childSum,h7,h8]
    change (∑ i : Fin cc,if i.val<s.childCount then f i.val else 0)=_
    rw [zero_padded_sum f childCap]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [f]
    rw [reads.child j i,Nat.mul_comm (d.child j i) 2,issued i c]
  have widths : b.widthSum mem j.val hc=(d.halfWidth j).sum := by
    simp only [Banks.widthSum,h10,Nat.add_zero,reads.halves]
    exact zero_padded_words (d.halfWidth j) hc
      (fun i=>mem (mem (s.incident+j.val*2+1)+(4*i+2))) halves (reads.width j)
  have copies : b.copiesSum mem j.val mc=(if s.kind=0 then 0 else (d.motifCopies j).sum) := by
    simp only [Banks.copiesSum,h6,h9]
    by_cases empty : s.kind=0
    · simp only [ite_eq_left empty]
    · simp only [ite_eq_right empty,reads.motifs empty j]
      exact zero_padded_words (d.motifCopies j) mc
        (fun i=>mem (mem (s.kernels+j.val*5+4)+(6*i+3))) (motifs empty) (reads.copies empty j)
  have zero : b.childSum mem j.val cc 0=∑ i,prior (d.child j i) 0 := child 0
  have one : b.childSum mem j.val cc 1=∑ i,prior (d.child j i) 1 := child 1
  have small := col.isLt
  have quo : (2*j.val+col.val)/2=j.val := by omega
  have rem : (2*j.val+col.val)%2=col.val := by omega
  have read := charge_read (W:=W) b mem data vs cc hc mc (2*j.val+col.val)
    (by simpa only [Nat.add_assoc] using addr)
  dsimp only at read
  rw [quo,rem,widths,copies,zero,one] at read
  fin_cases col <;> simpa [LayerData.cost,Banks.clippedPairs,h6,Nat.add_assoc] using read

end ThreeFlat.RAM.NavigationNodeRows

namespace ThreeFlat.RAM.NavigationNodeRows

open PhysicalPinsExpr MotifRows

theorem chargeHeader_fits {W : ℕ} (b : Banks) (mem : ℕ→ℕ) (data : Param→ℕ) (vs : Fin 1→ℕ)
    (current : b.current<2^W) (header : mem b.current+13<2^W) (j : ℕ) (hj : j≤13) :
    (h b j).Fits W data mem vs := by
  refine ⟨⟨⟨trivial,current⟩,trivial,trivial⟩,?_⟩
  change mem b.current+j<2^W
  omega

theorem chargeTotals_fits {W : ℕ} (mem : ℕ→ℕ) (data : Param→ℕ) (vs : Fin 1→ℕ)
    (xs : List Expr) (ok : ∀ f∈xs, f.Fits W data mem vs) : (totals xs).Fits W data mem vs := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨ok x List.mem_cons_self,ih (fun y hy => ok y (List.mem_cons_of_mem _ hy)),trivial⟩

/-- Whole-array bounds used by the chronological two-column charge scan.
Child charge pairs and pointed incident or motif payloads are bounded only
where an active record selects them. The last clause is needed for the
truncated subtraction in an original trace lane. -/
structure ChargeRoom (W : ℕ) (b : Banks) (mem : ℕ→ℕ) (count cc hc mc : ℕ) : Prop where
  wide : 2<2^W
  control : b.current<2^W
  header : mem b.current+13<2^W
  output : b.column mem 0+2*count≤2^W
  childCap : cc≤2^W
  halfCap : hc≤2^W
  motifCap : mc≤2^W
  kind : b.column mem 6<2^W
  childCount : b.column mem 7<2^W
  children : b.column mem 8+count*b.column mem 7≤2^W
  prior : ∀ r : Fin count, ∀ i : Fin cc, i.val<b.column mem 7 →
    b.charges+2*mem (b.column mem 8+r.val*b.column mem 7+i.val)+2≤2^W
  incident : b.column mem 10+2*count≤2^W
  halves : ∀ r : Fin count, mem (b.column mem 10+r.val*2)<2^W
  width : ∀ r : Fin count, ∀ i : Fin hc, i.val<mem (b.column mem 10+r.val*2) →
    mem (b.column mem 10+r.val*2+1)+(4*i.val+2)<2^W
  kernels : b.column mem 6≠0 → b.column mem 9+5*count≤2^W
  motifs : b.column mem 6≠0 → ∀ r : Fin count, mem (b.column mem 9+r.val*5+3)<2^W
  copies : b.column mem 6≠0 → ∀ r : Fin count, ∀ i : Fin mc, i.val<mem (b.column mem 9+r.val*5+3) →
    mem (b.column mem 9+r.val*5+4)+(6*i.val+3)<2^W
  lanes : b.column mem 6=0 → b.lanes<2^W
  pairs : b.totalPairs<2^W
  perLane : b.perLanePairs<2^W
  laneOffset : b.column mem 6=0 → ∀ r : Fin count, r.val<b.lanes → r.val*b.perLanePairs<2^W

end ThreeFlat.RAM.NavigationNodeRows

namespace ThreeFlat.RAM.NavigationNodeRows

open PhysicalPinsExpr MotifRows

theorem fromChildren_fits {W : ℕ} (b : Banks) (mem : ℕ → ℕ) (data : Param → ℕ)
    (vs : Fin 1 → ℕ) (row : Expr) (cap col : ℕ) (rowFits : row.Fits W data mem vs)
    (current : b.current < 2^W) (header : mem b.current+13 < 2^W) (capFits : cap ≤ 2^W)
    (countFits : b.column mem 7 < 2^W)
    (ptr : ∀ i : Fin cap, i.val<b.column mem 7 →
      b.column mem 8 + row.natural W data mem vs*b.column mem 7+i.val < 2^W)
    (child : ∀ i : Fin cap, i.val<b.column mem 7 →
      b.charges + mem (b.column mem 8 + row.natural W data mem vs*b.column mem 7+i.val)*2+col < 2^W) :
    (fromChildren b row cap col).Fits W data mem vs := by
  have count := chargeHeader_fits (W:=W) b mem data vs current header 7 (by decide)
  have first := chargeHeader_fits (W:=W) b mem data vs current header 8 (by decide)
  unfold fromChildren
  apply chargeTotals_fits
  intro f hf
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
  have iv := i.isLt.trans_le capFits
  have num (j : ℕ) : (h b j).natural W data mem vs = b.column mem j := rfl
  by_cases active : i.val < b.column mem 7
  · have p := ptr i active
    have c := child i active
    simp only [Formula.Fits, Formula.natural, natOp, natTest, opFits, field, ix, plus,
      num, decide_eq_true_eq, active, ite_true, rowFits, count, first, countFits, iv, p, c, and_self]
  · simp only [Formula.Fits, Formula.natural, natTest, num, decide_eq_true_eq, active,
      ite_false, count, countFits, iv, and_self]

end ThreeFlat.RAM.NavigationNodeRows

namespace ThreeFlat.RAM.NavigationNodeRows

open PhysicalPinsExpr MotifRows
variable {W : ℕ} (b : Banks) (mem : ℕ→ℕ) (data : Param→ℕ) (vs : Fin 1→ℕ)
local notation "V" => Formula.natural W data mem vs
local notation "Fit" => Formula.Fits W data mem vs

private theorem fittedChargeField (f : Expr) (j : ℕ) (valid : Fit f) (addr : V f+j<2^W) :
    Fit (field f j) := ⟨⟨valid,trivial,trivial⟩,addr⟩

private theorem guardedChargeField (f : Expr) (cnt ptr i off : ℕ) (valid : Fit f)
    (cntAddr : V f+cnt<2^W) (ptrAddr : V f+ptr<2^W) (idx : i<2^W)
    (count : mem (V f+cnt)<2^W) (payload : i<mem (V f+cnt) → mem (V f+ptr)+off<2^W) :
    Fit (.select .lt (.lit i) (field f cnt) (field (field f ptr) off) (.lit 0)) := by
  refine ⟨trivial,fittedChargeField mem data vs f cnt valid cntAddr,idx,count,?_⟩
  change if decide (i<mem (V f+cnt)) then Fit (field (field f ptr) off) else True
  split
  next yes =>
    exact fittedChargeField mem data vs _ _ (fittedChargeField mem data vs f ptr valid ptrAddr)
      (payload (of_decide_eq_true yes))
  next => trivial

theorem incidentWidth_fits (row : Expr) (cap : ℕ) (frow : Fit row)
    (current : b.current<2^W) (header : mem b.current+13<2^W) (size : cap≤2^W)
    (head : b.column mem 10+V row*2+1<2^W) (count : mem (b.column mem 10+V row*2)<2^W)
    (payload : ∀ i : Fin cap, i.val<mem (b.column mem 10+V row*2) →
      mem (b.column mem 10+V row*2+1)+(4*i.val+2)<2^W) :
    Fit (incidentWidth b row cap) := by
  let f := ix (h b 10) row 2 0
  have vf : V f=b.column mem 10+V row*2 := rfl
  have valid : Fit f := by
    have ff := chargeHeader_fits (W:=W) b mem data vs current header 10 (by decide)
    exact ⟨⟨ff,⟨frow,trivial,trivial⟩,trivial⟩,trivial,trivial⟩
  unfold incidentWidth
  apply chargeTotals_fits (W:=W) mem data vs
  intro item member
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp member
  apply guardedChargeField mem data vs f 0 1 i.val (4*i.val+2) valid
  · rw [vf]; omega
  · simpa only [vf] using head
  · exact i.isLt.trans_le size
  · simpa only [vf,Nat.add_zero] using count
  · simpa only [vf,Nat.add_zero] using payload i

theorem motifCopies_fits (row : Expr) (cap : ℕ) (frow : Fit row)
    (current : b.current<2^W) (header : mem b.current+13<2^W) (size : cap≤2^W)
    (kind : b.column mem 6<2^W)
    (head : b.column mem 6≠0 → b.column mem 9+V row*5+4<2^W)
    (count : b.column mem 6≠0 → mem (b.column mem 9+V row*5+3)<2^W)
    (payload : b.column mem 6≠0 → ∀ i : Fin cap, i.val<mem (b.column mem 9+V row*5+3) →
      mem (b.column mem 9+V row*5+4)+(6*i.val+3)<2^W) :
    Fit (motifCopies b row cap) := by
  let f := ix (h b 9) row 5 0
  have vf : V f=b.column mem 9+V row*5 := rfl
  have ff := chargeHeader_fits (W:=W) b mem data vs current header 9 (by decide)
  have valid : Fit f := ⟨⟨ff,⟨frow,trivial,trivial⟩,trivial⟩,trivial,trivial⟩
  unfold motifCopies
  refine ⟨chargeHeader_fits (W:=W) b mem data vs current header 6 (by decide),trivial,kind,
    Nat.two_pow_pos _,?_⟩
  split
  next => trivial
  next off =>
    have zero : b.column mem 6≠0 := by
      intro hz
      apply off
      change decide (b.column mem 6=0)=true
      exact decide_eq_true hz
    apply chargeTotals_fits (W:=W) mem data vs
    intro item member
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp member
    apply guardedChargeField mem data vs f 3 4 i.val (6*i.val+3) valid
    · have hh := head zero
      rw [vf]
      omega
    · simpa only [vf] using head zero
    · exact i.isLt.trans_le size
    · simpa only [vf] using count zero
    · simpa only [vf] using payload zero i

end ThreeFlat.RAM.NavigationNodeRows

namespace ThreeFlat.RAM.NavigationNodeRows

open PhysicalPinsExpr MotifRows

private theorem trace_charge_fits {W : ℕ} (b : Banks) (mem : ℕ→ℕ) (data : Param→ℕ) (vs : Fin 1→ℕ)
    (row yes no : Expr) (rowFits : row.Fits W data mem vs) (small : row.natural W data mem vs<2^W)
    (kindFits : (h b 6).Fits W data mem vs) (kind : b.column mem 6<2^W)
    (lanes : b.column mem 6=0 → b.lanes<2^W) (absent : no.Fits W data mem vs)
    (active : b.column mem 6=0 → row.natural W data mem vs<b.lanes → yes.Fits W data mem vs) :
    (traceLeaf b row yes no).Fits W data mem vs := by
  refine ⟨kindFits,trivial,kind,Nat.two_pow_pos _,?_⟩
  change (if natTest .eq (b.column mem 6) 0 then
    (Formula.select .lt row (.lit b.lanes) yes no).Fits W data mem vs else no.Fits W data mem vs)
  by_cases init : b.column mem 6=0
  · simp only [natTest,decide_eq_true_eq,ite_eq_left init]
    refine ⟨rowFits,trivial,small,lanes init,?_⟩
    change (if natTest .lt (row.natural W data mem vs) b.lanes then yes.Fits W data mem vs else no.Fits W data mem vs)
    by_cases leaf : row.natural W data mem vs<b.lanes
    · simpa [natTest,leaf] using active init leaf
    · simpa [natTest,leaf] using absent
  · simpa only [natTest,decide_eq_true_eq,ite_eq_right init] using absent

private theorem pair_charge_fits {W : ℕ} (b : Banks) (mem : ℕ→ℕ) (data : Param→ℕ) (vs : Fin 1→ℕ)
    {count cc hc mc : ℕ} (room : ChargeRoom W b mem count cc hc mc) (j : Fin count) (row : Expr)
    (frow : row.Fits W data mem vs) (read : row.natural W data mem vs=j.val) (small : j.val<2^W) :
    (leafPairs b row).Fits W data mem vs := by
  let used : Expr := .op .mul row (.lit b.perLanePairs)
  let av : Expr := .cut (.lit b.totalPairs) used
  apply trace_charge_fits b mem data vs row (.select .lt av (.lit b.perLanePairs) av (.lit b.perLanePairs))
    (.lit 0) frow (by simpa only [read] using small)
    (chargeHeader_fits b mem data vs room.control room.header 6 (by decide)) room.kind room.lanes trivial
  intro init lane
  have value : used.natural W data mem vs=j.val*b.perLanePairs :=
    congrArg (·*b.perLanePairs) read
  have outside := room.laneOffset init j (read ▸ lane)
  have fits : av.Fits W data mem vs :=
    ⟨trivial,⟨frow,trivial,trivial⟩,room.pairs,value.trans_lt outside⟩
  have bound : av.natural W data mem vs<2^W := (Nat.sub_le _ _).trans_lt room.pairs
  exact ⟨fits,trivial,bound,room.perLane,by split <;> first | exact fits | trivial⟩

end ThreeFlat.RAM.NavigationNodeRows

namespace ThreeFlat.RAM.NavigationNodeRows

open PhysicalPinsExpr MotifRows

/-- Each selected comparison, subtraction and external read of the actual
two-column charge expression fits in the native word. The final arithmetic
uses the ring operations of the physical interpreter. -/
theorem charge_fits {W : ℕ} (b : Banks) (mem : ℕ→ℕ) (data : Param→ℕ) (vs : Fin 1→ℕ)
    (count cc hc mc row : ℕ) (col : Fin 2) (room : ChargeRoom W b mem count cc hc mc)
    (hr : row<count) (addr : vs 0=b.column mem 0+2*row+col.val) :
    (charge b cc hc mc).Fits W data mem vs := by
  let j : Fin count := ⟨row,hr⟩
  let z : Expr := .cut (.reg 0) (h b 0)
  let rr : Expr := .op .div z (.lit 2)
  let ix : Expr := .op .mod z (.lit 2)
  let Fit := Formula.Fits W data mem vs
  let E := Formula.natural W data mem vs
  have range := room.output
  have two := col.isLt
  have hf := chargeHeader_fits (W:=W) b mem data vs room.control room.header
  have zval : E z=2*row+col.val := by change vs 0-b.column mem 0=_; omega
  have zz : E z<2^W := by rw [zval]; omega
  have zfit : Fit z := ⟨trivial,hf 0 (by decide),(by omega : vs 0<2^W),
    (by change b.column mem 0<2^W; omega)⟩
  have rfit : Fit rr := ⟨zfit,trivial,zz,room.wide⟩
  have ixfit : Fit ix := ⟨zfit,trivial,zz,room.wide⟩
  have rvalue : E rr=row := by change E z/2=row; rw [zval]; omega
  have rsmall : row<2^W := by omega
  have imax : E ix<2^W := (Nat.mod_lt (E z) (by decide : 0<2)).trans room.wide
  have ch (c : Fin 2) : Fit (fromChildren b rr cc c.val) := by
    apply fromChildren_fits b mem data vs rr cc c.val rfit room.control room.header room.childCap room.childCount
    · intro i hit
      change b.column mem 8+E rr*b.column mem 7+i.val<2^W
      rw [rvalue]
      have endRow := Nat.mul_le_mul_right (b.column mem 7) (Nat.succ_le_of_lt hr)
      rw [Nat.succ_mul] at endRow
      have full := room.children
      omega
    · intro i hit
      change b.charges+mem (b.column mem 8+E rr*b.column mem 7+i.val)*2+c.val<2^W
      rw [rvalue]
      have full := room.prior j i hit
      change b.charges+2*mem (b.column mem 8+row*b.column mem 7+i.val)+2≤2^W at full
      have lim := c.isLt
      omega
  have widths : Fit (incidentWidth b rr hc) := by
    apply incidentWidth_fits b mem data vs rr hc rfit room.control room.header room.halfCap
    · change b.column mem 10+E rr*2+1<2^W
      have full := room.incident
      omega
    · change mem (b.column mem 10+E rr*2)<2^W
      rw [rvalue]
      exact room.halves j
    · change ∀ i : Fin hc, i.val<mem (b.column mem 10+E rr*2) →
        mem (b.column mem 10+E rr*2+1)+(4*i.val+2)<2^W
      rw [rvalue]
      exact room.width j
  have copies : Fit (motifCopies b rr mc) := by
    apply motifCopies_fits b mem data vs rr mc rfit room.control room.header room.motifCap room.kind
    · intro active
      change b.column mem 9+E rr*5+4<2^W
      have full := room.kernels active
      omega
    · change b.column mem 6≠0 → mem (b.column mem 9+E rr*5+3)<2^W
      rw [rvalue]
      exact fun active => room.motifs active j
    · change b.column mem 6≠0 → ∀ i : Fin mc,i.val<mem (b.column mem 9+E rr*5+3) →
        mem (b.column mem 9+E rr*5+4)+(6*i.val+3)<2^W
      rw [rvalue]
      exact fun active => room.copies active j
  have pairs := pair_charge_fits b mem data vs room j rr rfit rvalue rsmall
  have work := trace_charge_fits (W:=W) b mem data vs rr (.lit b.traceWork) (.lit 0)
    rfit (by change E rr<2^W; omega) (hf 6 (by decide)) room.kind room.lanes trivial (fun _ _=>trivial)
  let localSize := plus (.lit 1) (plus (incidentWidth b rr hc) (plus (motifCopies b rr mc)
    (plus (leafPairs b rr) (traceLeaf b rr (.lit b.traceWork) (.lit 0)))))
  have localOK : Fit localSize :=
    ⟨trivial,⟨widths,⟨copies,⟨pairs,work,trivial⟩,trivial⟩,trivial⟩,trivial⟩
  have right : Fit (plus (leafPairs b rr) (fromChildren b rr cc 1)) := ⟨pairs,ch 1,trivial⟩
  have left : Fit (plus (.op .mul (.lit b.unitWork) localSize) (fromChildren b rr cc 0)) :=
    ⟨⟨trivial,localOK,trivial⟩,ch 0,trivial⟩
  exact ⟨ixfit,trivial,imax,Nat.two_pow_pos _,by split <;> first | exact left | exact right⟩

end ThreeFlat.RAM.NavigationNodeRows

namespace ThreeFlat.RAM.NavigationNodeRows

/-- The selected read addresses of the three physical projections. Both words used
for every indirect lookup are included. The seed may reside above the output banks. -/
structure LayerData.Footprint {s : Layer} (d : LayerData s) (safe : ℕ→Prop) (m : ℕ→ℕ) : Prop where
  child : ∀ (j : Fin s.count) (i : Fin s.childCount),safe (s.children+j.val*s.childCount+i.val)
  halves : ∀ (j : Fin s.count),safe (s.incident+j.val*2)
  halfPtr : ∀ (j : Fin s.count),safe (s.incident+j.val*2+1)
  width : ∀ j (i : Fin (d.halfWidth j).length),safe (m (s.incident+j.val*2+1)+(4*i.val+2))
  motifs : s.kind≠0→∀ (j : Fin s.count),safe (s.kernels+j.val*5+3)
  motifPtr : s.kind≠0→∀ (j : Fin s.count),safe (s.kernels+j.val*5+4)
  copies : s.kind≠0→∀ j (i : Fin (d.motifCopies j).length),safe (m (s.kernels+j.val*5+4)+(6*i.val+3))

variable {s : Layer} {d : LayerData s} {safe safe' : ℕ→Prop} {m m' : ℕ→ℕ} {limit : ℕ}

theorem LayerData.Footprint.mono (f : d.Footprint safe m) (h : ∀ i,safe i→safe' i) : d.Footprint safe' m :=
  ⟨fun j i=>h _ (f.child j i),fun j=>h _ (f.halves j),fun j=>h _ (f.halfPtr j),
   fun j i=>h _ (f.width j i),fun nz j=>h _ (f.motifs nz j),fun nz j=>h _ (f.motifPtr nz j),
   fun nz j i=>h _ (f.copies nz j i)⟩

theorem LayerData.Below.footprint (f : d.Below limit m) : d.Footprint (·<limit) m :=
  ⟨f.child,fun j=>by have:=f.halves j;omega,f.halves,f.width,
    fun nz j=>by have:=f.motifs nz j;omega,f.motifs,f.copies⟩

theorem LayerData.Footprint.transfer (old : d.Footprint safe m) (f : d.Footprint safe' m)
    (h : ∀ x,safe' x→m' x=m x) : d.Footprint safe m' where
  child:=old.child
  halves:=old.halves
  halfPtr:=old.halfPtr
  width j i:=by rw [h _ (f.halfPtr j)];exact old.width j i
  motifs:=old.motifs
  motifPtr:=old.motifPtr
  copies nz j i:=by rw [h _ (f.motifPtr nz j)];exact old.copies nz j i

theorem LayerData.Reads.of_footprint (old : d.Reads m) (f : d.Footprint safe m)
    (h : ∀ x,safe x→m' x=m x) : d.Reads m' where
  child j i := (h _ (f.child j i)).trans (old.child j i)
  halves j := (h _ (f.halves j)).trans (old.halves j)
  width j i := by rw [h _ (f.halfPtr j),h _ (f.width j i)];exact old.width j i
  motifs nz j := (h _ (f.motifs nz j)).trans (old.motifs nz j)
  copies nz j i := by rw [h _ (f.motifPtr nz j),h _ (f.copies nz j i)];exact old.copies nz j i

theorem LayerData.Below.of_footprint (old : d.Below limit m) (f : d.Footprint safe m)
    (h : ∀ x,safe x→m' x=m x) : d.Below limit m' where
  child:=old.child
  halves:=old.halves
  width j i:=by rw [h _ (f.halfPtr j)];exact old.width j i
  motifs:=old.motifs
  copies nz j i:=by rw [h _ (f.motifPtr nz j)];exact old.copies nz j i

end ThreeFlat.RAM.NavigationNodeRows

namespace ThreeFlat.RAM.NavigationNodeRows

/-- The last native incidence row contains the incoming total bit prefix and the final
width. This reads the extra fourth word used by stage preparation. -/
def LayerData.Tail {s : Layer} (d : LayerData s) (read : ℕ→ℕ) := ∀ j : Fin s.count,
  0<(d.halfWidth j).length →
  let last:=read (s.incident+j.val*2+1)+4*((d.halfWidth j).length-1)
  read (last+3)+read (last+2)=(d.halfWidth j).sum

structure LayerData.TailCells {s : Layer} (d : LayerData s) (safe : ℕ→Prop) (read : ℕ→ℕ) : Prop where
  header : ∀ j : Fin s.count,∀ k : Fin 2,safe (s.incident+j.val*2+k.val)
  last : ∀ j : Fin s.count,0<(d.halfWidth j).length →
    let a:=read (s.incident+j.val*2+1)+4*((d.halfWidth j).length-1)
    safe (a+2) ∧ safe (a+3)

theorem LayerData.Tail.transfer {s : Layer} {d : LayerData s} {m m' : ℕ→ℕ} {safe : ℕ→Prop}
    (value : d.Tail m) (cells : d.TailCells safe m) (same : ∀ x,safe x→m' x=m x) : d.Tail m' := by
  intro j pos
  dsimp only
  have tail:=cells.last j pos
  have ptr : m' (s.incident+j.val*2+1)=m (s.incident+j.val*2+1) :=
    same _ (cells.header j (1 : Fin 2))
  rw [ptr,same _ tail.1,same _ tail.2]
  exact value j pos

theorem LayerData.TailCells.transfer {s : Layer} {d : LayerData s} {m m' : ℕ→ℕ} {safe : ℕ→Prop}
    (cells : d.TailCells safe m) (same : ∀ x,safe x→m' x=m x) : d.TailCells safe m' where
  header:=cells.header
  last j pos:=by
    dsimp only
    have ptr : m' (s.incident+j.val*2+1)=m (s.incident+j.val*2+1) :=
      same _ (cells.header j (1 : Fin 2))
    rw [ptr]
    exact cells.last j pos

theorem LayerData.TailCells.mono {s : Layer} {d : LayerData s} {m : ℕ→ℕ} {p q : ℕ→Prop}
    (cells : d.TailCells p m) (lift : ∀ x,p x→q x) : d.TailCells q m where
  header j k:=lift _ (cells.header j k)
  last j pos:=⟨lift _ (cells.last j pos).1,lift _ (cells.last j pos).2⟩

end ThreeFlat.RAM.NavigationNodeRows

end OAI
