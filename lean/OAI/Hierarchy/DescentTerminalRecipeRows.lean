import OAI.Hierarchy.DescentTerminalBinFormat
import OAI.Hierarchy.DescentKernelHistory
import OAI.Hierarchy.ProtocolRAMPortRanks

namespace OAI
/-! # The port and table positions of a surviving occurrence

The same external bundle name is used in the neighbor's port list and the
occurrence's list of arguments. Port groups start on row boundaries. Table
tuples occupy whole contiguous intervals in their original order.
-/

namespace Hierarchy.DescentTerminalRecipeRows
open ThreeFlat.Routing
open DescentTerminalBinReaddress DescentTerminalBinPack DescentTerminalBinFormat
open scoped BigOperators
noncomputable section

private def orderedNames {g : ℕ} (size : Fin g→ℕ) : List ((k : Fin g) × Fin (size k)) :=
  (List.finRange g).flatMap fun k=>List.ofFn fun a : Fin (size k) => ⟨k,a⟩

private theorem mem_names {g : ℕ} {size : Fin g→ℕ} (r : (k : Fin g) × Fin (size k)) :
    r ∈ orderedNames size :=
  List.mem_flatMap.mpr ⟨r.1,List.mem_finRange _,List.mem_ofFn.mpr ⟨r.2,rfl⟩⟩

private def findName {K : Type} [DecidableEq K] {g : ℕ} {size : Fin g→ℕ}
    (name : ((k : Fin g) × Fin (size k)) → K) (needle : K) (existsName : ∃r,name r=needle) :
    (k : Fin g) × Fin (size k) :=
  ((orderedNames size).find? (fun r=>decide (name r=needle))).get (by
    obtain ⟨r,hr⟩ := existsName
    exact List.find?_isSome.mpr ⟨r,mem_names r,decide_eq_true hr⟩)

private theorem foundName {K : Type} [DecidableEq K] {g : ℕ} {size : Fin g→ℕ}
    (name : ((k : Fin g) × Fin (size k)) → K) (needle : K) (existsName : ∃r,name r=needle) :
    name (findName name needle existsName)=needle := by
  have hit : (orderedNames size).find? (fun r=>decide (name r=needle))=some (findName name needle existsName) := by
    unfold findName
    exact (Option.some_get _).symm
  exact of_decide_eq_true (List.find?_some (p:=fun r=>decide (name r=needle)) hit)

/-- Groups are the distinct neighbors and the exterior port. Each group
uses the fixed block-then-wire ordering. Occurrences are in block order. -/
structure Site where
  groups : ℕ
  size : Fin groups → ℕ
  nodes : ℕ
  arity : Fin nodes → ℕ
  arg : (v : Fin nodes) → Fin (arity v) → (g : Fin groups) × Fin (size g)

namespace Site
/-- Resolve the displayed bundle names by bounded search in the actual
port vectors. A name may be an edge, block and within-block wire triple. -/
def ofNames {K : Type} [DecidableEq K] {groups nodes : ℕ} (size : Fin groups→ℕ)
    (catalog : ((g : Fin groups) × Fin (size g)) ↪ K) (arity : Fin nodes→ℕ)
    (args : (v : Fin nodes)→Fin (arity v)→K)
    (cover : ∀v j,∃r,catalog r=args v j) : Site :=
  ⟨groups,size,nodes,arity,fun v j=>findName catalog (args v j) (cover v j)⟩

theorem ofNames_arg {K : Type} [DecidableEq K] {groups nodes : ℕ} (size : Fin groups→ℕ)
    (catalog : ((g : Fin groups) × Fin (size g)) ↪ K) (arity : Fin nodes→ℕ)
    (args : (v : Fin nodes)→Fin (arity v)→K) (cover : ∀v j,∃r,catalog r=args v j)
    (v : Fin nodes) (j : Fin (arity v)) (r : (g : Fin groups) × Fin (size g)) :
    (ofNames size catalog arity args cover).arg v j=r ↔ catalog r=args v j := by
  have eqn := foundName catalog (args v j) (cover v j)
  change findName catalog (args v j) (cover v j)=r ↔ _
  exact ⟨fun h=>h ▸ eqn,fun h=>catalog.injective (eqn.trans h.symm)⟩

abbrev Name (t : Site) := (g : Fin t.groups) × Fin (t.size g)
abbrev Arg (t : Site) := (v : Fin t.nodes) × Fin (t.arity v)
def chunks (t : Site) (q : ℕ) := fun g => poolBatchCount (t.size g) q
def portRows (t : Site) (q : ℕ) := ∑g,t.chunks q g
def tableRows (t : Site) (q : ℕ) := bins q t.arity
def rows (t : Site) (q : ℕ) := t.portRows q+t.tableRows q+1

private def chunk {t : Site} {q : ℕ} (pos : 0<q) (a : t.Name) :
    Fin (t.chunks q a.1) := ⟨a.2.val/q,by
  apply (Nat.div_lt_iff_lt_mul pos).mpr
  exact a.2.isLt.trans_le (by simpa [chunks,Nat.mul_comm] using
    CallPool.count_le_batches_mul (t.size a.1) q pos)⟩

def source {t : Site} {q : ℕ} (pos : 0<q) (a : t.Name) : Fin (t.rows q) × Fin q :=
  let r := ProtocolRAMPortRanks.address (t.chunks q) Fin.val ⟨a.1,chunk pos a⟩
  (⟨r.val,by have h := r.isLt; change _<t.portRows q at h; unfold rows; omega⟩,
   ⟨a.2.val%q,Nat.mod_lt _ pos⟩)

theorem source_unique {t : Site} {q : ℕ} (pos : 0<q) :
    Function.Injective (source (t:=t) pos) := by
  rintro ⟨g,u⟩ ⟨k,v⟩ eqn
  have h1 := congrArg (fun z : Fin (t.rows q)×Fin q => z.1.val) eqn
  have h2 := congrArg (fun z : Fin (t.rows q)×Fin q => z.2.val) eqn
  have idx := ProtocolRAMPortRanks.injective (t.chunks q) Fin.val Fin.val_injective
    (Fin.ext h1 : ProtocolRAMPortRanks.address (t.chunks q) Fin.val ⟨g,chunk pos ⟨g,u⟩⟩ =
      ProtocolRAMPortRanks.address (t.chunks q) Fin.val ⟨k,chunk pos ⟨k,v⟩⟩)
  have groupEq : g=k := congrArg Sigma.fst idx
  subst k
  have chunkEq := sigma_mk_injective idx
  have hd : u.val/q=v.val/q := congrArg Fin.val chunkEq
  change u.val%q=v.val%q at h2
  apply congrArg (Sigma.mk g)
  apply Fin.ext
  exact (Nat.div_add_mod u.val q).symm.trans (by rw [hd,h2,Nat.div_add_mod])

def target {t : Site} {q : ℕ} (pos : 0<q) (a : t.Arg) : Fin (t.rows q) × Fin q :=
  let r : Fin (t.tableRows q) × Fin q := finProdFinEquiv.symm (rowIndex pos t.arity a)
  (⟨t.portRows q+r.1.val,by have h := r.1.isLt; unfold rows; omega⟩,r.2)

theorem target_unique {t : Site} {q : ℕ} (pos : 0<q) : Function.Injective (target (t:=t) pos) := by
  intro u v h
  have left := congrArg (fun z : Fin (t.rows q)×Fin q=>z.1.val) h
  have right := congrArg Prod.snd h
  apply (rowIndex pos t.arity).injective
  apply finProdFinEquiv.symm.injective
  exact Prod.ext (Fin.ext (Nat.add_left_cancel left)) right

/-- An empty argument tuple still has a real row for its scalar description. -/
def descriptor {t : Site} {q : ℕ} (pos : 0<q) (v : Fin t.nodes) : Fin (t.rows q) :=
  if h : 0<t.arity v then (target pos ⟨v,⟨0,h⟩⟩).1
  else ⟨t.portRows q+t.tableRows q,by simp [rows]⟩

theorem whole_tuple {t : Site} {q : ℕ} (pos : 0<q) (fit : ∀v,t.arity v ≤ q)
    (v : Fin t.nodes) (j : Fin (t.arity v)) : (target pos ⟨v,j⟩).1=descriptor pos v := by
  have live : 0<t.arity v := (Nat.zero_le _).trans_lt j.isLt
  rw [descriptor,dite_eq_left live]
  apply Fin.ext
  change t.portRows q+(first q t.arity v+j.val)/q=t.portRows q+(first q t.arity v+0)/q
  have inside := in_bin pos t.arity v (fit v)
  have lim := j.isLt
  have offsetFit : offset q t.arity v+j.val<q := by omega
  have zeroFit : offset q t.arity v<q := by omega
  rw [Nat.add_zero,first_eq q t.arity v,Nat.add_assoc,Nat.mul_comm (bin q t.arity v) q,
    Nat.mul_add_div pos,Nat.div_eq_of_lt offsetFit,Nat.mul_add_div pos,Nat.div_eq_of_lt zeroFit]

theorem rows_bound (t : Site) {q : ℕ} (_pos : 0<q) :
    t.rows q*q ≤ (∑g,t.size g)+t.groups*q+2*(∑v,t.arity v)+2*q := by
  have gr (g : Fin t.groups) : t.chunks q g*q ≤ t.size g+q := by
    exact (Nat.div_mul_le_self _ _).trans (Nat.sub_le ..)
  have gc := Finset.sum_le_sum (s:=Finset.univ) (fun g _ => gr g)
  have tc := paid q t.arity
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at gc
  rw [rows,Nat.add_mul,Nat.add_mul,Nat.one_mul,portRows,Finset.sum_mul]
  change bins q t.arity*q ≤ _ at tc
  unfold tableRows
  omega

end Site

variable {S W q : ℕ} (sites : Fin S→Site) (positive : 0<W) (slotPositive : 0<q)
abbrev counts := fun i=> (sites i).rows q
abbrev Bins := bins W (counts (q:=q) sites)
abbrev Named := (i : Fin S) × (sites i).Name
abbrev Argument := (i : Fin S) × (sites i).Arg
abbrev Local := (i : Fin S) × (Fin ((sites i).rows q) × Fin q)

/-- Scatter a position-local coordinate directly to its allocated bin. -/
def global (a : Local (q:=q) sites) : Fin (Bins (W:=W) (q:=q) sites) × Slot W q :=
  let r := finProdFinEquiv.symm (rowIndex positive (counts (q:=q) sites) ⟨a.1,a.2.1⟩)
  (r.1,(r.2,a.2.2))

theorem global_unique : Function.Injective (global (q:=q) sites positive) := by
  rintro ⟨i,ri,ci⟩ ⟨j,rj,cj⟩ eqn
  have atRow := congrArg (fun x : Fin (Bins (W:=W) (q:=q) sites)×Slot W q=>(x.1,x.2.1)) eqn
  have same := (rowIndex positive (counts (q:=q) sites)).injective
    (finProdFinEquiv.symm.injective atRow)
  have atCol := congrArg (fun x : Fin (Bins (W:=W) (q:=q) sites)×Slot W q=>x.2.2) eqn
  cases same
  cases atCol
  rfl

theorem global_bin (fit : ∀i,(sites i).rows q ≤ W) (a : Local (q:=q) sites) :
    (global sites positive a).1.val=bin W (counts (q:=q) sites) a.1 := by
  change (first W (counts (q:=q) sites) a.1+a.2.1.val)/W=_
  have inBin := in_bin positive (counts (q:=q) sites) a.1 (fit a.1)
  have slot : a.2.1.val<counts (q:=q) sites a.1:=a.2.1.isLt
  rw [first_eq W (counts (q:=q) sites) a.1,Nat.add_assoc,Nat.mul_comm (bin ..) W,Nat.mul_add_div positive]
  rw [Nat.div_eq_of_lt (by omega),Nat.add_zero]

def source (a : Named sites) := global sites positive ⟨a.1,Site.source slotPositive a.2⟩
def target (a : Argument sites) := global sites positive ⟨a.1,Site.target slotPositive a.2⟩
def sourceName (a : Argument sites) : Named sites := ⟨a.1,(sites a.1).arg a.2.1 a.2.2⟩

theorem target_unique : Function.Injective (target sites positive slotPositive) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have eqn := global_unique sites positive h
  have ij : i=j := congrArg Sigma.fst eqn
  subst j
  exact congrArg (Sigma.mk i) (Site.target_unique slotPositive (sigma_mk_injective (β:=fun k:Fin S=>Fin ((sites k).rows q)×Fin q) eqn))

theorem source_unique : Function.Injective (source sites positive slotPositive) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have eqn := global_unique sites positive h
  have ij : i=j := congrArg Sigma.fst eqn
  subst j
  exact congrArg (Sigma.mk i) (Site.source_unique slotPositive (sigma_mk_injective (β:=fun k:Fin S=>Fin ((sites k).rows q)×Fin q) eqn))

def arguments : List (Argument sites) :=
  (List.finRange S).flatMap fun i => (List.finRange (sites i).nodes).flatMap fun v =>
    List.ofFn fun j : Fin ((sites i).arity v) => ⟨i,v,j⟩

theorem mem_arguments (a : Argument sites) : a ∈ arguments sites := by
  rcases a with ⟨i,v,j⟩
  exact List.mem_flatMap.mpr ⟨i,List.mem_finRange i,List.mem_flatMap.mpr
    ⟨v,List.mem_finRange v,List.mem_ofFn.mpr ⟨j,rfl⟩⟩⟩

theorem argument_count : (arguments sites).length=∑i,∑v,(sites i).arity v := by
  simp [arguments,List.length_flatMap,←List.ofFn_eq_map,List.sum_ofFn]

include positive slotPositive in
theorem scatter_budget : (arguments sites).length ≤ purchased W (counts (q:=q) sites)*q := by
  have h := Fintype.card_le_of_injective _ (target_unique sites positive slotPositive)
  simpa [argument_count,Argument,Site.Arg,Fintype.card_sigma,Slot,Bins,purchased,Nat.mul_assoc] using h

def ordinal {K : ℕ} (p : Fin K×Slot W q) : Fin (K*(W*q)) := finProdFinEquiv (p.1,finProdFinEquiv p.2)

private theorem ordinal_inj {K : ℕ} : Function.Injective (ordinal (K:=K) (W:=W) (q:=q)) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have eqn : (i,finProdFinEquiv a)=(j,finProdFinEquiv b):=finProdFinEquiv.injective h
  have rows : i=j:=congrArg (fun z:Fin K×Fin (W*q)=>z.1) eqn
  have cols : finProdFinEquiv a=finProdFinEquiv b:=congrArg (fun z:Fin K×Fin (W*q)=>z.2) eqn
  exact Prod.ext rows (finProdFinEquiv.injective cols)

/-- From an initially empty vector, emit one destination pointer per live
occurrence argument. No bin-wide search through other positions occurs. -/
def scatter {A X : Type} {N : ℕ} (idx : A→Fin N) (value : A→X) (ls : List A) :
    Vector (Option X) N :=
  ls.foldr (fun a acc => acc.set (idx a).val (some (value a)) (idx a).isLt) (Vector.replicate _ none)

theorem scatter_live {A X : Type} {N : ℕ} (idx : A→Fin N) (value : A→X)
    (unique : Function.Injective idx) {a : A} (ls : List A) (mem : a∈ls) :
    (scatter idx value ls)[(idx a).val]=some (value a) := by
  induction ls with
  | nil => simp at mem
  | cons b tl ih =>
    change ((scatter idx value tl).set (idx b).val (some (value b)) (idx b).isLt)[(idx a).val]=_
    by_cases eqn : b=a
    · subst b; simp
    · rw [Vector.getElem_set_ne _ _ (fun ev => eqn (unique (Fin.ext ev)))]
      exact ih (List.mem_cons.mp mem |>.resolve_left (Ne.symm eqn))

theorem scatter_empty {A X : Type} {N : ℕ} (idx : A→Fin N) (value : A→X) (ls : List A)
    (j : Fin N) (empty : ∀a∈ls,idx a≠j) : (scatter idx value ls)[j.val]=none := by
  induction ls with
  | nil => simp [scatter]
  | cons a tl ih =>
    change ((scatter idx value tl).set (idx a).val (some (value a)) (idx a).isLt)[j.val]=_
    rw [Vector.getElem_set_ne _ _ (fun h => empty a (by simp) (Fin.ext h))]
    exact ih fun b hb => empty b (List.mem_cons_of_mem _ hb)

def routes (b : Fin (Bins (W:=W) (q:=q) sites)) (dst : Slot W q) : Option (Slot W q) :=
  let z := ordinal (b,dst)
  (scatter (fun a=>ordinal (target sites positive slotPositive a))
    (fun a=>(source sites positive slotPositive (sourceName sites a)).2) (arguments sites))[z.val]

def control (b : Fin (Bins (W:=W) (q:=q) sites)) := encode (routes sites positive slotPositive b)

theorem read_arg (a : Argument sites) :
    let t := target sites positive slotPositive a
    address W q (control sites positive slotPositive t.1) t.2=
      some (source sites positive slotPositive (sourceName sites a)).2 := by
  intro t
  rw [control,address_encode]
  exact scatter_live (W:=W) (q:=q) _ _ (ordinal_inj.comp (target_unique sites positive slotPositive))
    (arguments sites) (mem_arguments sites a)

theorem read_unused (b : Fin (Bins (W:=W) (q:=q) sites)) (dst : Slot W q)
    (vacant : ∀a,target sites positive slotPositive a≠(b,dst)) :
    address W q (control sites positive slotPositive b) dst=none := by
  rw [control,address_encode]
  exact scatter_empty (W:=W) (q:=q) _ _ _ _ (fun a _ h=>vacant a (ordinal_inj h))

theorem reassembled_arg {bits piece : ℕ} (room : sliceWidth W q piece ≤ bits)
    (fit : ∀i,(sites i).rows q ≤ W) (pay : Fin (Bins (W:=W) (q:=q) sites)→Payload W q piece)
    (a : Argument sites) (j : Fin (W*piece)) :
    let t := target sites positive slotPositive a
    let src := source sites positive slotPositive (sourceName sites a)
    read room (fun u=>entry bits piece (address W q) (control sites positive slotPositive t.1)
        (gather (pay t.1) u)) t.2 j=pay src.1 src.2 j := by
  intro t src
  have outBin:=global_bin sites positive fit ⟨a.1,Site.target slotPositive a.2⟩
  have inBin:=global_bin sites positive fit ⟨a.1,Site.source slotPositive (sourceName sites a).2⟩
  have same : t.1=src.1:=Fin.ext (outBin.trans inBin.symm)
  rw [reassembled,read_arg]
  exact congrArg (fun b=>pay b src.2 j) same

/-- The descriptor attached to a table row supplies its scalar, including
all hidden summations in each history and all arity-zero occurrences. -/
def Site.rowScalar {Tag F : Type} [CommSemiring F] {t : Site} {q p : ℕ}
    (pos : 0<q) (history : (v : Fin t.nodes) → DescentKernelHistory.Recipe Tag (Fin (t.arity v)))
    (dict : Tag → List (List Bool) → F) (r : Fin (t.rows q)) (data : Fin q→Fin p→Bool) : F :=
  ∏v : {v : Fin t.nodes // Site.descriptor pos v=r},
    (history v.val).value dict (fun j=>List.ofFn (data (Site.target pos ⟨v.val,j⟩).2))

theorem Site.scalar_product {Tag F : Type} [CommSemiring F] {t : Site} {q p : ℕ}
    (pos : 0<q) (fit : ∀v,t.arity v ≤ q)
    (history : (v : Fin t.nodes) → DescentKernelHistory.Recipe Tag (Fin (t.arity v)))
    (dict : Tag → List (List Bool) → F) (data : Fin (t.rows q)→Fin q→Fin p→Bool) :
    (∏r,Site.rowScalar pos history dict r (data r))=
      ∏v,(history v).value dict (fun j=>List.ofFn (data (Site.target pos ⟨v,j⟩).1
        (Site.target pos ⟨v,j⟩).2)) := by
  let f (v : Fin t.nodes) := (history v).value dict (fun j=>List.ofFn
    (data (Site.target pos ⟨v,j⟩).1 (Site.target pos ⟨v,j⟩).2))
  calc
    _ = ∏r,∏v : {v : Fin t.nodes // Site.descriptor pos v=r},f v.val := by
      apply Finset.prod_congr rfl
      intro r _
      apply Finset.prod_congr rfl
      intro v _
      simp only [f,Site.whole_tuple pos fit,v.property]
    _ = _ := Fintype.prod_fiberwise _ f

end
end Hierarchy.DescentTerminalRecipeRows

end OAI
