import OAI.ThreeFlat.RAM.HistoryBatchProgram
import OAI.ThreeFlat.RAM.HistoryMotifMaps

namespace OAI
/-! # Generating the three executable commands per operand of an actual motif batch -/

namespace ThreeFlat.RAM.HistoryBatchTape

open Computability.VPVNP.BurstRAM DescriptorExpr PhysicalPinsExpr Diagonal.HistoryContraction.Tree
open scoped Fin.CommRing

/-- The two homogeneous groups in a real selector or payload batch. The
fields `lut` and `comp` are the three read-only words consumed by the real
leaf decoders. The per-symbol quotas are continuous histogram words. -/
structure Header where
  args : ℕ
  stream : ℕ
  maps : ℕ
  r : ℕ
  s : ℕ
  left : BatchRows.Size
  right : BatchRows.Size
  parentPins : ℕ
  shared : ℕ
  checks : Bool
  b : ℕ
  e : ℕ
  d : ℕ
  alphabet : ℕ
  hist : ℕ
  lut : Fin 3 → ℕ
  comp : Fin 3 → ℕ

def Header.words (T : Header) : Fin 26 → ℕ :=
  ![T.args,T.stream,T.maps,T.r,T.s,T.left.arity,T.left.rows,T.left.bits,
    T.right.arity,T.right.rows,T.right.bits,T.parentPins,T.shared,T.checks.toNat,T.b,T.e,T.d,
    T.alphabet,T.hist,T.lut 0,T.lut 1,T.lut 2,T.comp 0,T.comp 1,T.comp 2,0]

def Header.row (T : Header) (i : ℕ) :=
  BatchRows.record ⟨T.stream,T.maps,0,0⟩ T.r T.s T.left T.right i

def Header.arity (T : Header) (i : ℕ) := if i<T.r then T.left.arity else T.right.arity

/-- [leaf, public-pin gather, join]. Every branch may run immediately after
its predecessor, including when one of the ranges is empty. -/
def command (T : Header) (i : ℕ) (j : Fin 3) : Fin 7 → ℕ :=
  let a := T.row i
  let work := T.args+23*i
  match j.val with
  | 0 => ![work,a.source,0,0,0,0,a.source+a.count]
  | 1 => ![work+6,a.map,4,0,0,0,a.map+T.arity i]
  | _ => ![work+16,a.dest,1,0,0,0,a.dest+a.count]

/-- [six leaf words, ten map words, seven join words]. No address is inferred
from a Fintype enumeration during the actual native scan. -/
def arguments (T : Header) (m : ℕ → ℕ) (i : ℕ) : Fin 23 → ℕ :=
  let a := T.row i
  let left := i<T.r
  let lut := if left then T.lut else T.comp
  let part := if left then i else i-T.r
  let tag := (if T.checks then 2 else 0)+(if left then 0 else 1)
  let quota := if T.checks ∧ ¬left then m (T.hist+part) else 0
  ![if left then 1 else 2,lut 0,lut 1,lut 2,a.source,a.count,
    a.map,T.arity i,tag,part,T.r,T.b,T.e,T.d,T.alphabet,quota,
    a.source,a.dest,a.map,T.arity i,T.parentPins,T.shared+a.bitPrefix,a.dest+a.count]

private abbrev E := Formula 3
private def num (v : ℕ) : E := .lit v
private def reg (v : Fin 3) : E := .reg v
private def get (v : ℕ) : E := .load (add (reg 0) (num v))
private def left (a b : E) := lt (reg 1) (get 3) a b
private def span (j : ℕ) : E :=
  add (mul (lt (reg 1) (get 3) (reg 1) (get 3)) (get j)) (mul (sub (reg 1) (get 3)) (get (j+3)))
private def source : E := add (get 1) (mul (num 4) (span 6))
private def dest : E := add (add (get 1) (mul (num 4) (add (mul (get 3) (get 6)) (mul (get 4) (get 9))))) (mul (num 4) (span 6))
private def maps : E := add (get 2) (span 5)
private def count : E := mul (num 4) (left (get 6) (get 9))
private def pins : E := left (get 5) (get 8)
def choose {n : ℕ} (j : Formula n) (a : List (Formula n)) : Formula n :=
  match a with
  | [] => .lit 0
  | x::xs => eqz j (.lit 0) x (choose (sub j (.lit 1)) xs)

def rawCommand : E :=
  let op := div (reg 2) (num 7)
  let x := rem (reg 2) (num 7)
  let start := eqz op (num 0) source (eqz op (num 1) maps dest)
  let width := eqz op (num 1) pins count
  let ptr := add (get 0) (mul (num 23) (reg 1))
  choose x [add ptr (eqz op (num 0) (num 0) (eqz op (num 1) (num 6) (num 16))),start,
    eqz op (num 0) (num 0) (eqz op (num 1) (num 4) (num 1)),num 0,num 0,num 0,add start width]

def rawArguments : E :=
  let part := left (reg 1) (sub (reg 1) (get 3))
  let q := eqz (get 13) (num 0) (num 0) (left (num 0) (.load (add (get 18) part)))
  let tag := add (eqz (get 13) (num 0) (num 0) (num 2)) (left (num 0) (num 1))
  choose (reg 2) [left (num 1) (num 2),left (get 19) (get 22),left (get 20) (get 23),
    left (get 21) (get 24),source,count,maps,pins,tag,part,get 3,get 14,get 15,get 16,get 17,q,
    source,dest,maps,pins,get 11,add (get 12) (span 7),add dest count]

def program (w : ℕ) (commandBank : Bool) : Term w 1 3 :=
  (if commandBank then rawCommand else rawArguments).compile (fun _ => 0)

def values (base i col : ℕ) : Fin 3 → ℕ := ![base,i,col]

private theorem header_at (W : ℕ) (pub : Param → ℕ) (mem : ℕ → ℕ) (T : Header)
    (base i col : ℕ) (stored : ∀ j : Fin 26, mem (base+j.val)=T.words j) (j : Fin 26) :
    (get j.val).natural W pub mem (values base i col)=T.words j := by
  simpa [get,add,num,reg,Formula.natural,natOp,values] using stored j

private theorem prefix_at (W : ℕ) (pub : Param → ℕ) (mem : ℕ → ℕ) (T : Header)
    (base i col j : ℕ) (hj : j+3<26) (stored : ∀ u : Fin 26,mem (base+u.val)=T.words u) :
    (span j).natural W pub mem (values base i col) =
      BatchRows.span T.r (T.words ⟨j,by omega⟩) (T.words ⟨j+3,hj⟩) i := by
  have g := header_at W pub mem T base i col stored
  have g3 := g (3:Fin 26)
  have gj := g ⟨j,by omega⟩
  have gj' := g ⟨j+3,hj⟩
  change (get 3).natural W pub mem (values base i col)=T.r at g3
  let rd (n : ℕ) := (get n).natural W pub mem (values base i col)
  change (if decide (i < rd 3) = true then i else rd 3) * rd j +
      (i - rd 3) * rd (j+3) = _
  change rd 3 = T.r at g3
  change rd j = T.words ⟨j,by omega⟩ at gj
  change rd (j+3) = T.words ⟨j+3,hj⟩ at gj'
  rw [g3,gj,gj']
  by_cases h : i < T.r
  · simp [h,BatchRows.span,Nat.min_eq_left h.le]
  · simp [h,BatchRows.span,Nat.min_eq_right (Nat.le_of_not_gt h)]

set_option maxHeartbeats 800000 in
private theorem pieces (W : ℕ) (pub : Param → ℕ) (mem : ℕ → ℕ) (T : Header)
    (base i col : ℕ) (stored : ∀ u : Fin 26,mem (base+u.val)=T.words u) :
    let ev (f : E) := f.natural W pub mem (values base i col)
    ev source=(T.row i).source ∧ ev dest=(T.row i).dest ∧ ev maps=(T.row i).map ∧
      ev count=(T.row i).count ∧ ev pins=T.arity i := by
  dsimp only
  have gh (j : ℕ) (ok : j<26 := by decide) := header_at W pub mem T base i col stored ⟨j,ok⟩
  have pr (j : ℕ) (ok : j+3<26 := by decide) := prefix_at W pub mem T base i col j ok stored
  let rd (n : ℕ) := (get n).natural W pub mem (values base i col)
  let sp (n : ℕ) := (span n).natural W pub mem (values base i col)
  change rd 1 + 4 * sp 6 = _ ∧
    rd 1 + 4 * (rd 3 * rd 6 + rd 4 * rd 9) + 4 * sp 6 = _ ∧
    rd 2 + sp 5 = _ ∧
    4 * (if decide (i < rd 3) = true then rd 6 else rd 9) = _ ∧
    (if decide (i < rd 3) = true then rd 5 else rd 8) = _
  have g (n : ℕ) (hn : n < 26) : rd n = T.words ⟨n,hn⟩ := gh n hn
  have f (n : ℕ) (hn : n+3 < 26) :
      sp n = BatchRows.span T.r (T.words ⟨n,by omega⟩) (T.words ⟨n+3,hn⟩) i := pr n hn
  rw [g 1 (by decide),g 2 (by decide),g 3 (by decide),g 4 (by decide),g 5 (by decide),
    g 6 (by decide),g 8 (by decide),g 9 (by decide),f 5 (by decide),f 6 (by decide)]
  simp only [decide_eq_true_eq]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1000000 in
theorem command_value (W : ℕ) (pub : Param → ℕ) (mem : ℕ → ℕ) (T : Header)
    (base i : ℕ) (step : Fin 3) (col : Fin 7) (stored : ∀ u : Fin 26,mem (base+u.val)=T.words u) :
    rawCommand.natural W pub mem (values base i (7*step.val+col.val))=command T i step col := by
  let x := 7*step.val+col.val
  have ps := pieces W pub mem T base i x stored
  have addr := header_at W pub mem T base i x stored (0:Fin 26)
  change (get 0).natural W pub mem (values base i x)=T.args at addr
  fin_cases step <;> fin_cases col <;>
    simp [command,rawCommand,choose,eqz,div,rem,add,mul,sub,Formula.natural,natOp,natTest,
      num,reg,values] <;>
    first
    | exact addr
    | exact ps.1
    | exact ps.2.1
    | exact ps.2.2.1
    | exact congrArg₂ Nat.add ps.1 ps.2.2.2.1
    | exact congrArg₂ Nat.add ps.2.2.1 ps.2.2.2.2
    | exact congrArg₂ Nat.add ps.2.1 ps.2.2.2.1

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
theorem argument_value (W : ℕ) (pub : Param → ℕ) (mem : ℕ → ℕ) (T : Header)
    (base i : ℕ) (col : Fin 23) (stored : ∀ u : Fin 26,mem (base+u.val)=T.words u) :
    rawArguments.natural W pub mem (values base i col.val)=arguments T mem i col := by
  let ev (c : ℕ) (f : E) := f.natural W pub mem (values base i c)
  have rd (c : ℕ) (j : Fin 26) : ev c (get j.val)=T.words j :=
    header_at W pub mem T base i c stored j
  have side (c : ℕ) (a b : E) : ev c (left a b) = if i<T.r then ev c a else ev c b :=by
    change (if decide (i < ev c (get 3)) = true then ev c a else ev c b) = _
    have r : ev c (get 3)=T.r := rd c 3
    simp only [r,decide_eq_true_eq]
  have symbol (c : ℕ) (j : Fin 3) (first second : ℕ)
      (f₁ : ev c (get first)=T.lut j) (f₂ : ev c (get second)=T.comp j) :
      ev c (left (get first) (get second)) = (if i<T.r then T.lut else T.comp) j :=by
    rw [side,f₁,f₂]
    split <;> rfl
  let part := left (reg 1) (sub (reg 1) (get 3))
  have number (c : ℕ) : ev c part = if i<T.r then i else i-T.r :=by
    rw [show ev c part = _ from side c (reg 1) (sub (reg 1) (get 3))]
    change (if i<T.r then i else i-ev c (get 3)) = _
    rw [show ev c (get 3)=T.r from rd c 3]
  have tag : ev 8 (add (eqz (get 13) (num 0) (num 0) (num 2)) (left (num 0) (num 1))) =
      (if T.checks then 2 else 0)+(if i<T.r then 0 else 1) :=by
    change (if decide (ev 8 (get 13)=0) = true then 0 else 2) + ev 8 (left (num 0) (num 1)) = _
    rw [show ev 8 (get 13)=T.checks.toNat from rd 8 13,side]
    cases T.checks <;> rfl
  have quota : ev 15 (eqz (get 13) (num 0) (num 0) (left (num 0) (.load (add (get 18) part)))) =
      if T.checks ∧ ¬ i < T.r then mem (T.hist+(if i<T.r then i else i-T.r)) else 0 :=by
    change (if decide (ev 15 (get 13)=0)=true then 0 else ev 15 (left (num 0) (.load (add (get 18) part)))) = _
    rw [show ev 15 (get 13)=T.checks.toNat from rd 15 13,side]
    change (if decide (T.checks.toNat=0)=true then 0 else
      if i<T.r then 0 else mem (ev 15 (get 18)+ev 15 part)) = _
    rw [show ev 15 (get 18)=T.hist from rd 15 18,number]
    cases T.checks <;> by_cases hi:i<T.r <;> simp [hi]
  have fields (c : ℕ) := pieces W pub mem T base i c stored
  have prefixBits : ev 21 (span 7)=(T.row i).bitPrefix := by
    have h := prefix_at W pub mem T base i 21 7 (by decide) stored
    change ev 21 (span 7) = BatchRows.span T.r T.left.bits T.right.bits i
    simpa [Header.words] using h
  fin_cases col
  · exact side 0 (num 1) (num 2)
  · exact symbol 1 0 19 22 (rd 1 19) (rd 1 22)
  · exact symbol 2 1 20 23 (rd 2 20) (rd 2 23)
  · exact symbol 3 2 21 24 (rd 3 21) (rd 3 24)
  · exact (fields 4).1
  · exact (fields 5).2.2.2.1
  · exact (fields 6).2.2.1
  · exact (fields 7).2.2.2.2
  · exact tag
  · exact number 9
  · exact rd 10 3
  · exact rd 11 14
  · exact rd 12 15
  · exact rd 13 16
  · exact rd 14 17
  · exact quota
  · exact (fields 16).1
  · exact (fields 17).2.1
  · exact (fields 18).2.2.1
  · exact (fields 19).2.2.2.2
  · exact rd 20 11
  · exact congrArg₂ Nat.add (show ev 21 (get 12)=T.shared from rd 21 12) prefixBits
  · exact congrArg₂ Nat.add (fields 22).2.1 (fields 22).2.2.2.1

theorem choose_fits {n : ℕ} (W : ℕ) (pub : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin n → ℕ)
    (j : Formula n) (xs : List (Formula n)) (one : 1 < 2^W) (fj : j.Fits W pub mem vs)
    (small : j.natural W pub mem vs < 2^W) (entries : ∀ e ∈ xs, e.Fits W pub mem vs) :
    (choose j xs).Fits W pub mem vs := by
  induction xs generalizing j with
  | nil => trivial
  | cons a xs ih =>
    change j.Fits W pub mem vs ∧ True ∧ j.natural W pub mem vs < 2^W ∧ 0 < 2^W ∧
      (if natTest .eq (j.natural W pub mem vs) 0 then a.Fits W pub mem vs
       else (choose (sub j (.lit 1)) xs).Fits W pub mem vs)
    refine ⟨fj, trivial, small, by omega, ?_⟩
    split
    · exact entries a (by simp)
    · apply ih (j := sub j (.lit 1))
      · exact ⟨fj,trivial,small,one⟩
      · change j.natural W pub mem vs - 1 < 2^W
        omega
      · intro e he
        exact entries e (List.mem_cons_of_mem _ he)

private theorem row_fits (W : ℕ) (pub : Param → ℕ) (mem : ℕ → ℕ) (T : Header)
    (base i col : ℕ) (stored : ∀ k : Fin 26, mem (base+k.val)=T.words k)
    (room : base+26 < 2^W) (child : i < 2^W) (splitSize : T.r < 2^W) :
    let fits (f : E) := f.Fits W pub mem (values base i col)
    fits source ∧ fits dest ∧ fits maps ∧ fits count ∧ fits pins ∧ fits (span 7) := by
  have ar (j : ℕ) (h : j < 26) : base+j < 2^W := by omega
  have r : mem (base+3)=T.r := stored 3
  dsimp only
  simp (disch := omega) [source,dest,maps,count,pins,span,left,get,add,mul,sub,lt,num,reg,
    Formula.Fits,Formula.natural,opFits,natOp,natTest,values,r,ar,child,splitSize]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 800000 in
/-- The command stream uses bounded operands for division, comparisons, and
header addresses. Its pointer sums and products are written directly as words. -/
theorem command_fits (W : ℕ) (pub : Param → ℕ) (mem : ℕ → ℕ) (T : Header)
    (base i : ℕ) (step : Fin 3) (col : Fin 7) (stored : ∀ k : Fin 26, mem (base+k.val)=T.words k)
    (room : base+26 < 2^W) (child : i < 2^W) (splitSize : T.r < 2^W) :
    rawCommand.Fits W pub mem (values base i (7*step.val+col.val)) := by
  let x := 7*step.val+col.val
  have column : x < 2^W := by dsimp [x]; have := step.isLt; have := col.isLt; omega
  have op : x / 7 < 2^W := lt_of_le_of_lt (Nat.div_le_self _ _) column
  have remSmall : x % 7 < 2^W := by omega
  have seven : 7 < 2^W := by omega
  have one : 1 < 2^W := by omega
  have zero : 0 < 2^W := by omega
  have baseRoom : base < 2^W := by omega
  obtain ⟨hs,hd,hm,hc,hp,_⟩ := row_fits W pub mem T base i x stored room child splitSize
  dsimp only [values] at hs hd hm hc hp
  change rawCommand.Fits W pub mem (values base i x)
  unfold rawCommand
  apply choose_fits (one := one)
  · simp [num,reg,Formula.Fits,opFits,Formula.natural,values,column,seven]
  · exact remSmall
  · by_cases first : x < 7 <;> by_cases middle : x / 7 = 1 <;>
      simp [eqz,num,reg,add,mul,div,get,Formula.Fits,opFits,Formula.natural,natOp,natTest,
        values,hs,hd,hm,hc,hp,column,op,seven,one,zero,baseRoom,first,middle]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 800000 in
/-- Only a checked right child probes the histogram. Its quota address is the
histogram base plus its ordinal within the right group. -/
theorem argument_fits (W : ℕ) (pub : Param → ℕ) (mem : ℕ → ℕ) (T : Header)
    (base i : ℕ) (col : Fin 23) (stored : ∀ k : Fin 26, mem (base+k.val)=T.words k)
    (room : base+26 < 2^W) (child : i < 2^W) (splitSize : T.r < 2^W)
    (quota : T.checks = true → T.r ≤ i → T.hist+(i-T.r) < 2^W) :
    rawArguments.Fits W pub mem (values base i col.val) := by
  have column : col.val < 2^W := by have := col.isLt; omega
  have one : 1 < 2^W := by omega
  have zero : 0 < 2^W := by omega
  have ar (j : ℕ) (h : j < 26) : base+j < 2^W := by omega
  have r : mem (base+3)=T.r := stored 3
  have checked : mem (base+13)=T.checks.toNat := stored 13
  have hist : mem (base+18)=T.hist := stored 18
  obtain ⟨hs,hd,hm,hc,hp,hb⟩ := row_fits W pub mem T base i col.val stored room child splitSize
  dsimp only [values] at hs hd hm hc hp hb
  unfold rawArguments
  apply choose_fits (one := one)
  · trivial
  · exact column
  · cases check : T.checks <;> by_cases side : i < T.r <;>
      simp (disch := omega) [left,eqz,lt,num,reg,add,sub,get,Formula.Fits,
        Formula.natural,opFits,natOp,natTest,values,hs,hd,hm,hc,hp,hb,ar,r,checked,hist,
        child,splitSize,check,side,one,zero]; exact quota check (by omega)

theorem run_command (W : ℕ) (data : Fin 1 → ℕ) (mem : ℕ → ℕ) (T : Header)
    (base i : ℕ) (step : Fin 3) (col : Fin 7) (stored : ∀ u : Fin 26,mem (base+u.val)=T.words u)
    (fit : rawCommand.Fits W (fun _ => data 0) mem (values base i (7*step.val+col.val))) :
    (program W true).eval (fun j => (data j : Word W)) (fun j => (mem j : Word W))
      (fun j => (values base i (7*step.val+col.val) j : Word W)) = (command T i step col : Word W) := by
  change (rawCommand.compile _).eval _ _ _ = _
  rw [Formula.eval_compile]
  refine (Formula.value_eq_natural rawCommand (fun _ => data 0) mem _ fit).trans ?_
  rw [command_value W _ mem T base i step col stored]

theorem run_argument (W : ℕ) (data : Fin 1 → ℕ) (mem : ℕ → ℕ) (T : Header)
    (base i : ℕ) (col : Fin 23) (stored : ∀ u : Fin 26,mem (base+u.val)=T.words u)
    (fit : rawArguments.Fits W (fun _ => data 0) mem (values base i col.val)) :
    (program W false).eval (fun j => (data j : Word W)) (fun j => (mem j : Word W))
      (fun j => (values base i col.val j : Word W)) = (arguments T mem i col : Word W) := by
  change (rawArguments.compile _).eval _ _ _ = _
  rw [Formula.eval_compile]
  refine (Formula.value_eq_natural rawArguments (fun _ => data 0) mem _ fit).trans ?_
  rw [argument_value W _ mem T base i col stored]


end ThreeFlat.RAM.HistoryBatchTape

end OAI
