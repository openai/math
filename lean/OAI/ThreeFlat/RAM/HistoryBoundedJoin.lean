import OAI.ThreeFlat.RAM.HistoryBatchTape
import OAI.ThreeFlat.RAM.HistoryCompiledRows

namespace OAI
/-! # Bounded-degree selected joins with independently located old streams -/

namespace ThreeFlat.RAM.HistoryBoundedJoin

open Computability.VPVNP.BurstRAM DescriptorExpr PhysicalPinsExpr
open Diagonal.HistoryContraction
open scoped Fin.CommRing BigOperators

/-- Each locally prepared six-word link refers to a previously generated
root, its map and the opcode-specific operands of its map builder. -/
structure Child where
  node : ℕ
  map : ℕ
  opcode : ℕ
  operand : ℕ
  deriving DecidableEq

/-- Node records use [stream, public pin count, factor count, hidden count]. -/
structure Info where
  stream : ℕ
  pins : ℕ
  factors : ℕ
  hidden : ℕ
  deriving DecidableEq

def Info.words (z : Info) : Fin 4 → ℕ := ![z.stream,z.pins,z.factors,z.hidden]
def Child.words (z : Child) : Fin 4 → ℕ := ![z.node,z.map,z.opcode,z.operand]

structure Hub where
  stream : ℕ
  pins : ℕ
  shared : ℕ
  argc : ℕ
  children : ℕ
  arguments : ℕ

def Hub.words (z : Hub) : Fin 6 → ℕ := ![z.stream,z.pins,z.shared,z.argc,z.children,z.arguments]

def read (dest : ℕ) (m : ℕ → ℕ) : Info := ⟨m dest,m (dest+1),m (dest+2),m (dest+3)⟩
def child (h : Hub) (m : ℕ → ℕ) (i : ℕ) : Child :=
  let ptr := h.children+4*i
  ⟨m ptr,m (ptr+1),m (ptr+2),m (ptr+3)⟩

def total (h : Hub) (m : ℕ → ℕ) (i : ℕ) (f : Info→ℕ) :=
  ∑ j ∈ Finset.range i,f (read (child h m j).node m)

def moved (h : Hub) (m : ℕ → ℕ) (i : ℕ) := h.stream+4*total h m i Info.factors
def offset (h : Hub) (m : ℕ → ℕ) (i : ℕ) := h.shared+total h m i Info.hidden

/-- The first record builds the child's actual pin map. The second performs
the verified four-column trivalent source/ID relocation. -/
def command (h : Hub) (m : ℕ → ℕ) (i : ℕ) (join : Bool) : Fin 7 → ℕ :=
  let c := child h m i
  let x := read c.node m
  if join then ![h.arguments+7*i,moved h m i,1,0,0,0,moved h m i+4*x.factors]
  else ![c.operand,c.map,c.opcode,0,0,0,c.map+x.pins]

def arguments (h : Hub) (m : ℕ → ℕ) (i : ℕ) : Fin 7 → ℕ :=
  let c := child h m i
  let x := read c.node m
  ![x.stream,moved h m i,c.map,x.pins,h.pins,offset h m i,moved h m i+4*x.factors]

private abbrev E := Formula 13
private def hd (j : ℕ) : E := .load (add (.reg 0) (.lit j))
private def rel (i : E) (j : ℕ) : E := .load (add (add (hd 4) (mul (.lit 4) i)) (.lit j))
private def info (i : E) (j : ℕ) : E := .load (add (rel i 0) (.lit j))

private def «prefix» (i : E) (j : ℕ) : ℕ → E
  | 0 => .lit 0
  | c+1 => add («prefix» i j c) (lt (.lit c) i (info (.lit c) j) (.lit 0))

private abbrev field (j : E) (a : List E) : E := HistoryBatchTape.choose j a

def formula (cap : ℕ) (commands : Bool) : E :=
  let key : E := .reg 5
  let i := div key (.lit (if commands then 14 else 7))
  let pos := add (hd 0) (mul (.lit 4) («prefix» i 2 cap))
  let width := mul (.lit 4) (info i 2)
  let dest := add pos width
  let j := rem key (.lit 7)
  let join := field j [add (hd 5) (mul (.lit 7) i),pos,.lit 1,.lit 0,.lit 0,.lit 0,dest]
  let map := field j [rel i 3,rel i 1,rel i 2,.lit 0,.lit 0,.lit 0,add (rel i 1) (info i 1)]
  if commands then lt (rem key (.lit 14)) (.lit 7) map join else
    field j [info i 0,pos,rel i 1,info i 1,hd 1,add (hd 2) («prefix» i 3 cap),dest]

def program (W cap : ℕ) (commands : Bool) : Term W 1 13 := (formula cap commands).compile (fun _ => 0)

theorem program_size (W W' cap : ℕ) (check : Bool) :
    (program W cap check).binds=(program W' cap check).binds := by simp [program,Formula.binds_compile]

private theorem prefix_value (i : E) (j c W : ℕ) (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin 13→ℕ) :
    («prefix» i j c).natural W data mem vs=
      ∑ t ∈ Finset.range c, if t < i.natural W data mem vs then (info (.lit t) j).natural W data mem vs else 0 := by
  induction c with
  | zero => simp [«prefix»,Formula.natural]
  | succ c ih =>
    by_cases live : c < i.natural W data mem vs <;>
      simp [«prefix»,add,lt,Formula.natural,natOp,natTest,ih,Finset.sum_range_succ,live]

private theorem sum_cut (f : ℕ → ℕ) {c i : ℕ} (valid : i≤c) :
    (∑ t ∈ Finset.range c,if t < i then f t else 0)=∑ t ∈ Finset.range i,f t := by
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp [Finset.mem_range]
  omega

private theorem roots (W : ℕ) (T : Hub) (base : ℕ) (data : Param → ℕ) (mem : ℕ → ℕ)
    (vs : Fin 13 → ℕ) (header : ∀ j : Fin 6, mem (base+j.val)=T.words j) (ptr : vs 0=base)
    (i : E) (j c : ℕ) (arg : i.natural W data mem vs≤c) :
    («prefix» i j c).natural W data mem vs=∑ t ∈ Finset.range (i.natural W data mem vs),
      mem ((child T mem t).node+j) := by
  have head := header (4:Fin 6)
  change mem (base+4)=T.children at head
  rw [prefix_value]
  simp only [info,rel,hd,add,mul,Formula.natural,natOp,ptr,head,Nat.add_zero]
  rw [sum_cut _ arg]
  rfl

set_option maxHeartbeats 1200000 in
/-- One 14-word command pair or seven-word relocation argument record. The
same word is read by the native scanner at every party, motif and stage join. -/
theorem make_word (W c : ℕ) (T : Hub) (base : ℕ) (params : Param→ℕ)
    (m : ℕ→ℕ) (vs : Fin 13→ℕ) (i : ℕ) (j : Fin 7) (commands join : Bool)
    (bound : i≤c) (ptr : vs 0=base) (bank : ∀ j : Fin 6,m (base+j.val)=T.words j)
    (key : vs 5=if commands then 14*i+7*join.toNat+j.val else 7*i+j.val) :
    (formula c commands).natural W params m vs=
      if commands then command T m i join j else arguments T m i j := by
  let idx : E := div (.reg 5) (.lit (if commands then 14 else 7))
  have which : idx.natural W params m vs=i := by
    have h := j.isLt
    cases commands <;> cases join <;> simp [idx,Formula.natural,natOp,key] <;> omega
  have total2 : («prefix» idx 2 c).natural W params m vs=total T m i Info.factors := by
    rw [roots W T base params m vs bank ptr idx 2 c (by rwa [which]),which];rfl
  have total3 : («prefix» idx 3 c).natural W params m vs=total T m i Info.hidden := by
    rw [roots W T base params m vs bank ptr idx 3 c (by rwa [which]),which];rfl
  have h0 := bank (0:Fin 6);have h1 := bank (1:Fin 6);have h2 := bank (2:Fin 6)
  have h4 := bank (4:Fin 6);have h5 := bank (5:Fin 6)
  change m (base+0)=T.stream at h0
  change m (base+1)=T.pins at h1
  change m (base+2)=T.shared at h2
  change m (base+4)=T.children at h4
  change m (base+5)=T.arguments at h5
  simp only [Nat.add_zero] at h0
  have ordinal : vs 5 / (if commands then 14 else 7) = i := which
  have residue : vs 5 % 7 = j.val := by
    have hj := j.isLt
    cases commands <;> cases join <;> simp at key <;> omega
  have half : commands = true → ((vs 5 % 14 < 7) ↔ join = false) := by
    have hj := j.isLt
    cases commands <;> cases join <;> simp at key ⊢ <;> omega
  clear key which
  cases commands <;> cases join <;> fin_cases j
  all_goals simp [idx,div] at total2 total3
  all_goals simp at ordinal residue half
  all_goals
    simp_all [formula,field,HistoryBatchTape.choose,Formula.natural,natOp,natTest,
      lt,eqz,add,sub,mul,div,rem,info,rel,hd,command,arguments,moved,offset,child,read]
  all_goals
    intro selected
    exact ((Nat.not_lt_of_ge half) (of_decide_eq_true selected)).elim


private theorem prefix_fits (W : ℕ) (d : Param → ℕ) (m : ℕ → ℕ) (vs : Fin 13 → ℕ)
    (idx : E) (j cap : ℕ) (fi : idx.Fits W d m vs) (small : idx.natural W d m vs < 2^W)
    (room : cap ≤ 2^W) (active : ∀ t < idx.natural W d m vs, (info (.lit t) j).Fits W d m vs) :
    («prefix» idx j cap).Fits W d m vs := by
  induction cap with
  | zero => trivial
  | succ t ih =>
    refine ⟨ih (by omega),⟨trivial,fi,show t < 2^W by omega,small,?_⟩,trivial⟩
    change if natTest .lt t (idx.natural W d m vs) then (info (.lit t) j).Fits W d m vs else True
    by_cases live : t < idx.natural W d m vs
    · simpa [natTest,live] using active t live
    · simp [natTest,live]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 800000 in
/-- The selected child and its live predecessors address four-word links and four-word roots.
The prefix may contain inactive literal slots beyond the actual number of children. -/
theorem formula_fits (W cap : ℕ) (T : Hub) (base : ℕ) (d : Param → ℕ) (m : ℕ → ℕ)
    (vs : Fin 13 → ℕ) (commands : Bool) (i : Fin T.argc)
    (col : Fin (if commands then 14 else 7))
    (ptr : vs 0=base) (bank : ∀ j : Fin 6, m (base+j.val)=T.words j)
    (key : vs 5=(if commands then 14 else 7)*i.val+col.val)
    (hubRoom : base+6 < 2^W) (small : 14 < 2^W) (keyRoom : vs 5 < 2^W) (capRoom : cap ≤ 2^W)
    (linkRoom : T.children+4*T.argc ≤ 2^W)
    (rootRoom : ∀ k : Fin T.argc, (child T m k.val).node+3 < 2^W) :
    (formula cap commands).Fits W d m vs := by
  let idx : E := div (.reg 5) (.lit (if commands then 14 else 7))
  let pos : E := add (hd 0) (mul (.lit 4) («prefix» idx 2 cap))
  let dest : E := add pos (mul (.lit 4) (info idx 2))
  let column : E := rem (.reg 5) (.lit 7)
  have seven : 7 < 2^W := by omega
  have one : 1 < 2^W := by omega
  have stride : (if commands then 14 else 7 : ℕ) < 2^W := by split <;> omega
  have fidx : idx.Fits W d m vs := ⟨trivial,trivial,keyRoom,stride⟩
  have sidx : idx.natural W d m vs < 2^W := (Nat.div_le_self _ _).trans_lt keyRoom
  have index : idx.natural W d m vs = i.val := by
    change vs 5 / (if commands then 14 else 7) = i.val
    have positive : 0 < (if commands then 14 else 7 : ℕ) := by split <;> decide
    rw [key,Nat.mul_add_div positive,Nat.div_eq_of_lt col.isLt,Nat.add_zero]
  have head : m (base+4)=T.children := bank 4
  have hdFit (j : ℕ) (h : j<6) : (hd j).Fits W d m vs := by
    exact ⟨⟨trivial,trivial,trivial⟩,show vs 0+j<2^W by rw [ptr]; omega⟩
  have linkFit (x : E) (fx : x.Fits W d m vs) (k : Fin T.argc)
      (hx : x.natural W d m vs=k.val) (j : ℕ) (hj : j<4) : (rel x j).Fits W d m vs := by
    have addr : T.children+4*k.val+j < 2^W := by have := k.isLt; omega
    refine ⟨⟨⟨hdFit 4 (by decide),⟨trivial,fx,trivial⟩,trivial⟩,trivial,trivial⟩,?_⟩
    simpa only [hd,add,mul,Formula.natural,natOp,ptr,head,hx] using addr
  have infoFit (x : E) (fx : x.Fits W d m vs) (k : Fin T.argc)
      (hx : x.natural W d m vs=k.val) (j : ℕ) (hj : j<4) : (info x j).Fits W d m vs := by
    have addr : (child T m k.val).node+j < 2^W := by have := rootRoom k; omega
    refine ⟨⟨linkFit x fx k hx 0 (by decide),trivial,trivial⟩,?_⟩
    simpa only [rel,hd,add,mul,Formula.natural,natOp,ptr,head,hx,Nat.add_zero,child] using addr
  have pre (j : ℕ) (hj : j<4) : («prefix» idx j cap).Fits W d m vs := by
    apply prefix_fits W d m vs idx j cap fidx sidx capRoom
    intro t ht
    have live : t<T.argc := by rw [index] at ht; exact ht.trans i.isLt
    exact infoFit (.lit t) trivial ⟨t,live⟩ rfl j hj
  have link (j : ℕ) (hj : j<4 := by decide) := linkFit idx fidx i index j hj
  have root (j : ℕ) (hj : j<4 := by decide) := infoFit idx fidx i index j hj
  have place : pos.Fits W d m vs := ⟨hdFit 0 (by decide),⟨trivial,pre 2 (by decide),trivial⟩,trivial⟩
  have finish : dest.Fits W d m vs := ⟨place,⟨trivial,root 2,trivial⟩,trivial⟩
  have fc : column.Fits W d m vs := ⟨trivial,trivial,keyRoom,seven⟩
  have sc : column.natural W d m vs < 2^W := (Nat.mod_lt _ (by decide : 0<7)).trans seven
  have row (xs : List E) (rows : ∀ x ∈ xs, x.Fits W d m vs) : (field column xs).Fits W d m vs :=
    HistoryBatchTape.choose_fits W d m vs column xs one fc sc rows
  let maps : E := field column [rel idx 3,rel idx 1,rel idx 2,.lit 0,.lit 0,.lit 0,add (rel idx 1) (info idx 1)]
  let join : E := field column [add (hd 5) (mul (.lit 7) idx),pos,.lit 1,.lit 0,.lit 0,.lit 0,dest]
  let args : E := field column [info idx 0,pos,rel idx 1,info idx 1,hd 1,add (hd 2) («prefix» idx 3 cap),dest]
  have fmap : maps.Fits W d m vs := by
    apply row
    simp [add,Formula.Fits,opFits,link 1,link 2,link 3,root 1]
  have fjoin : join.Fits W d m vs := by
    apply row
    simp [add,mul,Formula.Fits,opFits,hdFit 5 (by decide),fidx,place,finish]
  have fargs : args.Fits W d m vs := by
    apply row
    simp [add,Formula.Fits,opFits,root 0,root 1,link 1,hdFit 1 (by decide),
      hdFit 2 (by decide),pre 3 (by decide),place,finish]
  change (if commands then lt (rem (.reg 5) (.lit 14)) (.lit 7) maps join else args).Fits W d m vs
  split
  · refine ⟨⟨trivial,trivial,keyRoom,small⟩,trivial,(Nat.mod_lt _ (by decide : 0<14)).trans small,
      seven,?_⟩
    split <;> assumption
  · exact fargs

theorem program_word (W c : ℕ) (T : Hub) (base : ℕ) (params : Fin 1→ℕ)
    (m : ℕ→ℕ) (vs : Fin 13→ℕ) (i : ℕ) (j : Fin 7) (commands join : Bool)
    (bound : i≤c) (ptr : vs 0=base) (bank : ∀ j : Fin 6,m (base+j.val)=T.words j)
    (key : vs 5=if commands then 14*i+7*join.toNat+j.val else 7*i+j.val)
    (fit : (formula c commands).Fits W (fun _ => params 0) m vs) :
    (program W c commands).eval (fun j => (params j:Word W)) (fun j => (m j:Word W))
      (fun j => (vs j:Word W))=
        ((if commands then command T m i join j else arguments T m i j : ℕ):Word W) := by
  rw [program,Formula.eval_compile]
  change (formula c commands).value (fun _ => (params 0 : Word W))
    (fun j => (m j : Word W)) (fun j => (vs j : Word W)) = _
  exact (Formula.value_eq_natural _ _ _ _ fit).trans
    (congrArg (fun x : ℕ => (x : Word W)) (make_word W c T base _ m vs i j commands join bound ptr bank key))

theorem moved_eq {F : Type*} {p fresh n : ℕ} {arity : Fin n→ℕ}
    (N : ∀ i,BitNetwork F (arity i)) (_wire : ∀ i,Fin (arity i)→BitSource fresh p)
    (T : Hub) (m : ℕ→ℕ) (i : Fin n) (shared : T.shared=fresh)
    (records : ∀ j : Fin n, read (child T m j.val).node m =
      ⟨(read (child T m j.val).node m).stream,arity j,(N j).cells,(N j).internal⟩) :
    moved T m i.val=T.stream+4*Tree.before (fun j => (N j).cells) i ∧
    offset T m i.val=fresh+Tree.before (fun j => (N j).internal) i := by
  have sum (f : Info→ℕ) : total T m i.val f=∑ j : Fin i.val, f (read (child T m j.val).node m) := by
    exact Finset.sum_range fun t => f (read (child T m t).node m)
  constructor
  · rw [moved,sum]
    congr 2
    exact Finset.sum_congr rfl fun j _ => congrArg Info.factors (records (Fin.castLE i.isLt.le j))
  · rw [offset,shared,sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => congrArg Info.hidden (records (Fin.castLE i.isLt.le j))

end ThreeFlat.RAM.HistoryBoundedJoin

end OAI
