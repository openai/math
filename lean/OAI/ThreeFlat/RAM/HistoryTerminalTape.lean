import OAI.ThreeFlat.RAM.HistoryFinalCopy
import OAI.ThreeFlat.RAM.TickSelectedPins
import OAI.ThreeFlat.RAM.PhysicalPinsNat

namespace OAI
/-! # Generating the selected root's live edge and endpoint pin map -/

namespace ThreeFlat.RAM.HistoryTerminalTape

open Computability.VPVNP.BurstRAM DescriptorExpr PhysicalPinsExpr
open scoped Fin.CommRing

/-- The global wire-prefix table uses the physical source-edge numbering.
Both endpoint records therefore install exactly the same wire bits. -/
structure Root where
  arguments : ℕ
  map : ℕ
  endpoints : ℕ
  ext : ℕ
  halves : ℕ
  halfData : ℕ
  wireStart : ℕ
  wirePrefix : ℕ
  stream : ℕ
  localPins : ℕ
  «meta» : ℕ
  rows : ℕ
  physicalPins : ℕ
  beforeHidden : ℕ

def Root.words (z : Root) : Fin 14 → ℕ :=
  ![z.arguments,z.map,z.endpoints,z.ext,z.halves,z.halfData,z.wireStart,z.wirePrefix,z.stream,
    z.localPins,z.meta,z.rows,z.physicalPins,z.beforeHidden]

structure Half where
  edge : ℕ
  side : ℕ
  width : ℕ
  start : ℕ

def half (T : Root) (mem : ℕ→ℕ) (i : ℕ) : Half :=
  let p := T.halfData+4*i
  ⟨mem p,mem (p+1),mem (p+2),mem (p+3)⟩

def interval (T : Root) (mem : ℕ→ℕ) (i : ℕ) := T.map+T.ext+(half T mem i).start
def source (T : Root) (mem : ℕ→ℕ) (i : ℕ) := T.wireStart+mem (T.wirePrefix+(half T mem i).edge)

def command (T : Root) (mem : ℕ→ℕ) (i : ℕ) : Fin 7→ℕ :=
  let data := T.arguments+7*i
  if i=0 then ![data,T.map,10,0,0,0,T.map+T.ext]
  else if i≤T.halves then ![data,interval T mem (i-1),11,0,0,0,interval T mem (i-1)+(half T mem (i-1)).width]
  else ![data,T.meta,1,0,0,0,T.meta+4*T.rows]

def arguments (T : Root) (mem : ℕ→ℕ) (i : ℕ) : Fin 7→ℕ :=
  if i=0 then ![T.map,T.ext,T.endpoints,0,0,0,0]
  else if i≤T.halves then ![interval T mem (i-1),(half T mem (i-1)).width,source T mem (i-1),0,0,0,0]
  else ![T.stream,T.meta,T.map,T.localPins,T.physicalPins,T.beforeHidden,T.meta+4*T.rows]

private abbrev E := Formula 13
private def h (j : ℕ) : E := .load (add (.reg 0) (.lit j))
private def entry (i : E) (j : ℕ) : E := .load (add (add (h 5) (mul (.lit 4) i)) (.lit j))
private def piece (i bare more last : E) := eqz i (.lit 0) bare (lt (h 4) i last more)
private def switch (j : E) (xs : List E) : E :=
  match xs with
  | [] => .lit 0
  | x::ys => eqz j (.lit 0) x (switch (sub j (.lit 1)) ys)

def formula (commands : Bool) : E :=
  let x : E := .reg 5
  let i := div x (.lit 7)
  let col := rem x (.lit 7)
  let b := sub i (.lit 1)
  let point := add (add (h 1) (h 3)) (entry b 3)
  let dest := piece i (h 1) point (h 10)
  let len := piece i (h 3) (entry b 2) (mul (.lit 4) (h 11))
  if commands then
    switch col [add (h 0) (mul (.lit 7) i),dest,piece i (.lit 10) (.lit 11) (.lit 1),
      .lit 0,.lit 0,.lit 0,add dest len]
  else
    let copy := switch col [h 1,h 3,h 2,.lit 0,.lit 0,.lit 0,.lit 0]
    let wire := switch col [point,entry b 2,add (h 6) (.load (add (h 7) (entry b 0))),
      .lit 0,.lit 0,.lit 0,.lit 0]
    let join := switch col [h 8,h 10,h 1,h 9,h 12,h 13,add (h 10) (mul (.lit 4) (h 11))]
    piece i copy wire join

def program (W : ℕ) (commands : Bool) : Term W 1 13 := (formula commands).compile (fun _ => 0)

theorem program_size (W W' : ℕ) (commands : Bool) :
    (program W commands).binds=(program W' commands).binds := by simp [program,Formula.binds_compile]

theorem formula_value (W : ℕ) (data : Param→ℕ) (mem : ℕ→ℕ) (vs : Fin 13→ℕ)
    (T : Root) (i : ℕ) (j : Fin 7) (cmd : Bool) (word : vs 5=7*i+j.val)
    (mount : ∀ u : Fin 14,mem (vs 0+u.val)=T.words u) :
    (formula cmd).natural W data mem vs=if cmd then command T mem i j else arguments T mem i j := by
  have valid := j.isLt
  have index : (7*i+j.val)/7=i := by
    rw [Nat.add_comm,Nat.add_mul_div_left _ _ (by decide),Nat.div_eq_of_lt valid,Nat.zero_add]
  have col : (7*i+j.val)%7=j.val := by
    rw [Nat.add_comm,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt valid]
  have header (t : ℕ) (ok : t<14 := by decide) : (h t).natural W data mem vs=T.words ⟨t,ok⟩ := by
    simpa only [h,add,Formula.natural,natOp] using mount ⟨t,ok⟩
  let eval (f : E) := f.natural W data mem vs
  have bank (b : E) (t : ℕ) : eval (entry b t)=mem (T.halfData+4*eval b+t) := by
    simp only [eval,entry,add,mul,Formula.natural,natOp,header 5]
    rfl
  cases cmd <;> by_cases first : i=0 <;> by_cases last : i≤T.halves <;> fin_cases j <;>
    simp [formula,command,arguments,piece,switch,eqz,lt,rem,div,add,mul,sub,
      Formula.natural,natTest,natOp,word,index,col,header,Root.words,first,last,lt_iff_not_ge,interval,source,half,entry]

theorem run (W : ℕ) (data : Fin 1→ℕ) (mem : ℕ→ℕ) (vs : Fin 13→ℕ)
    (T : Root) (i : ℕ) (j : Fin 7) (cmd : Bool) (word : vs 5=7*i+j.val)
    (mount : ∀ u : Fin 14,mem (vs 0+u.val)=T.words u)
    (fit : (formula cmd).Fits W (fun _ => data 0) mem vs) :
    (program W cmd).eval (fun k => (data k : Word W)) (fun a => (mem a : Word W)) (fun j => (vs j : Word W)) =
      ((if cmd then command T mem i j else arguments T mem i j : ℕ) : Word W) := by
  rw [program,Formula.eval_compile]
  change (formula cmd).value (fun _ => (data 0 : Word W)) (fun a => (mem a : Word W))
    (fun j => (vs j : Word W)) = _
  rw [Formula.value_eq_natural (formula cmd) (fun _ => data 0) mem vs fit,
      formula_value W _ mem vs T i j cmd word mount]

theorem shared_address {u teams hidden hist live a : ℕ} (q nt ns np capacity : ℕ)
    (room : 1+hist+live≤a) (T : Root) (mem : ℕ→ℕ) (i j : ℕ) (bit : Fin live)
    (origin : T.wireStart=(TickPhysicalABI.mounted u a teams capacity q nt ns np).oldAux+1+hist)
    (coord : bit.val=mem (T.wirePrefix+(half T mem i).edge)+j) :
    source T mem i+j=BitLayout.sourceAddress (n:=hidden) (.pin (TickSelectedPins.wire q nt ns np room bit)) := by
  rw [TickSelectedPins.wire_address (u:=u) (teams:=teams) capacity,source,origin,coord]
  omega

end ThreeFlat.RAM.HistoryTerminalTape

end OAI
