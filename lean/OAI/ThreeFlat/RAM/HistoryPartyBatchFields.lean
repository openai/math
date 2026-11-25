import OAI.ThreeFlat.RAM.HistoryPartyHeader
import OAI.ThreeFlat.RAM.HistoryBoundedJoin
import OAI.ThreeFlat.RAM.HistoryScratch
import OAI.ThreeFlat.RAM.HeaderScanProcedure

namespace OAI
/-! # Source cursors and result words of a selected histogram party -/

namespace ThreeFlat.RAM.HistoryPartyBatch

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure
open HistoryPartyHeader HistoryScratch
open scoped Fin.CommRing

/-- Fixed per-stage grid catalogue, selected chronological node and compact
navigation directory. The high arenas in this record hold only the currently
selected nodes' trivalent records. Temporary tape space is reused across all
motifs and parties. The finite slot and grid bounds do not depend on age. -/
structure Layout where
  cursor : ℕ
  nodes : ℕ
  V : ℕ
  arena : ℕ
  motifs : ℕ
  parties : ℕ
  motif : ℕ
  party : ℕ
  kinds : ℕ
  seed : ℕ
  batch : ℕ
  commands : ℕ
  arguments : ℕ
  maps : ℕ
  lutBase : ℕ
  lutStride : ℕ
  compBase : ℕ
  compStride : ℕ
  countBase : ℕ

private def V3 (A : Layout) (checks : Bool) (bank : ℕ) : HistoryScratch.Local :=
  ⟨A.motif+2,A.party+2,checks.toNat,bank⟩

def dest (A : Layout) (checks : Bool) (id bank : ℕ) :=
  atWord A.arena A.V A.motifs A.parties id (V3 A checks bank) 0

def kernel (A : Layout) (m : ℕ→ℕ) :=
  m (A.nodes+8*(m A.cursor-1)+5)

def incident (A : Layout) (m : ℕ→ℕ) := m (kernel A m+4)+6*A.motif

def occupied (A : Layout) (m : ℕ→ℕ) :=
  A.motif< m (kernel A m+3) ∧ m (incident A m+5)/2^A.party%2=1

instance (A : Layout) (m : ℕ → ℕ) : Decidable (occupied A m) := by
  unfold occupied
  infer_instance

def shape (A : Layout) (m : ℕ→ℕ) :=
  A.kinds+7*(m (incident A m+2)*A.parties+A.party)

def registers (A : Layout) (checks : Bool) (m : ℕ→ℕ) : Registers :=
  let yes := occupied A m
  ⟨A.arguments,dest A checks (m A.cursor-1) 0,A.maps,
    if yes then incident A m else A.seed+15,if yes then shape A m else A.seed+21,
    A.seed+1,A.lutBase,A.lutStride,A.compBase,A.compStride,A.countBase⟩

def copies (A : Layout) (m : ℕ→ℕ) := if occupied A m then m (incident A m+3) else 0
def digit (A : Layout) (m : ℕ→ℕ) := if occupied A m then m (shape A m+4) else 0
def kinds (A : Layout) (checks : Bool) (m : ℕ→ℕ) :=
  if occupied A m then m (shape A m+checks.toNat) else 0
def children (A : Layout) (checks : Bool) (m : ℕ→ℕ) :=
  copies A m+kinds A checks m

/-- Control+extent, eleven selected source cursors, zero-word dummy headers
for unoccupied bounded roles, scan descriptors, seven-word interpreter bounds
and result output. No dummy trivalent factors are emitted. -/
def seedWords (A : Layout) (checks : Bool) (m : ℕ→ℕ) : Fin 37 → ℕ :=
  let rs := registers A checks m
  let r := copies A m
  let n := children A checks m
  ![A.seed+1,max r (r*digit A m),0,0,
    rs.arguments,rs.streams,rs.maps,rs.incident,rs.grid,rs.dyadic,rs.lutBase,
    rs.lutStride,rs.compBase,rs.compStride,rs.countBase,
    0,0,0,0,0,0,
    0,0,0,0,0,0,0,
    A.seed+29,A.commands,21*n,A.arguments,23*n,
    A.commands,A.commands+21*n,dest A checks (m A.cursor-1) 1,4]

private abbrev E := Formula 1
def pick (j : E) : ℕ → List E → E
  | _,[] => .lit 0
  | n,x::xs => eqz j (.lit n) x (pick j (n+1) xs)
def rd (a : E) (i : ℕ) := Formula.load (add a (.lit i))

def seedFormula (A : Layout) (checks : Bool) : E :=
  let l := @Formula.lit 1
  let i := Formula.cut (.load (l A.cursor)) (l 1)
  let n := add (l A.nodes) (mul (l 8) i)
  let k := rd n 5
  let inc := add (rd k 4) (l (6*A.motif))
  let gr := add (l A.kinds) (mul (l 7) (add (mul (rd inc 2) (l A.parties)) (l A.party)))
  let en (x y : E) := lt (l A.motif) (rd k 3)
    (eqz (rem (div (rd inc 5) (l (2^A.party))) (l 2)) (l 1) x y) y
  let reps := en (rd inc 3) (l 0)
  let d := en (rd gr 4) (l 0)
  let long := mul reps d
  let n := add reps (en (rd gr checks.toNat) (l 0))
  let stream (b : ℕ) := add (add (l A.arena) (mul
    (add (mul i (l A.V)) (l (sector A.motifs A.parties (V3 A checks b)))) (l A.V))) (l 0)
  pick (.cut (.reg 0) (l A.seed)) 0
    [l (A.seed+1),lt reps long long reps,l 0,l 0,
     l A.arguments,stream 0,l A.maps,en inc (l (A.seed+15)),en gr (l (A.seed+21)),l (A.seed+1),
     l A.lutBase,l A.lutStride,l A.compBase,l A.compStride,l A.countBase,
     l 0,l 0,l 0,l 0,l 0,l 0,l 0,l 0,l 0,l 0,l 0,l 0,l 0,
     l (A.seed+29),l A.commands,mul (l 21) n,l A.arguments,mul (l 23) n,
     l A.commands,add (l A.commands) (mul (l 21) n),stream 1,l 4]

set_option maxRecDepth 15000 in
set_option maxHeartbeats 5000000 in
theorem seed_value (W : ℕ) (A : Layout) (b : Bool) (pub : Param→ℕ) (m : ℕ→ℕ) (j : Fin 37) :
    (seedFormula A b).natural W pub m (fun _ => A.seed+j.val)=(seedWords A b m) j := by
  by_cases hm : A.motif< m (kernel A m+3)
  · by_cases hp : m (incident A m+5)/2^A.party%2=1
    · have active : occupied A m := ⟨hm,hp⟩
      fin_cases j <;>
        simp [seedFormula,seedWords,pick,registers,children,copies,kinds,digit,occupied,kernel,incident,shape,
          dest,atWord,rd,eqz,lt,rem,div,add,mul,Formula.natural,natOp,natTest] at hm hp ⊢ <;>
        simp [hm,hp,max_def]; (try split_ifs) <;> omega
    · fin_cases j <;>
        simp [seedFormula,seedWords,pick,registers,children,copies,kinds,digit,occupied,kernel,incident,shape,
          dest,atWord,rd,eqz,lt,rem,div,add,mul,Formula.natural,natOp,natTest] at hm hp ⊢ <;>
        simp [hm,hp]
  · have inactive : ¬ A.motif < m (m (A.nodes+8*(m A.cursor-1)+5)+3) := hm
    fin_cases j <;>
      simp [seedFormula,seedWords,pick,registers,children,copies,kinds,digit,occupied,kernel,incident,dest,atWord,rd,eqz,lt,rem,div,add,mul,Formula.natural,natOp,natTest,inactive]

def absAddr {W : ℕ} (base : ℕ) : Term W 0 1 :=
  .binary .sub (.result 0) (.literal (base : Word W))

/-- Reindex the formula-to-native compiler directly at zero for completely
fixed closed arithmetic. Its parameter operands are unused. -/
def actualHeader (W : ℕ) (A : Layout) (checks : Bool) : Term W 0 1 :=
  (HeaderScan.closed (HistoryPartyHeader.formula checks)).instantiate
    (fun i => if i=0 then .literal ((A.seed+4 : ℕ):Word W)
      else if i=5 then absAddr A.batch else .literal 0)

/-- Source expression over the actual array cursor. The 26-word header has
already been emitted in selected scratch. -/
def batchTerm (W : ℕ) (A : Layout) (commands : Bool) : Term W 0 1 :=
  let key := absAddr (W:=W) (if commands then A.commands else A.arguments)
  let stride : Word W := if commands then 21 else 23
  (HeaderScan.closed (if commands then HistoryBatchTape.rawCommand else HistoryBatchTape.rawArguments)).instantiate
    ![.literal (A.batch : Word W),.binary .div key (.literal stride),.binary .mod key (.literal stride)]

def resultWord (A : Layout) : E :=
  let l := @Formula.lit 1
  let b := l A.batch
  let root := rd b 1
  let count (x y : ℕ) := add (mul (rd b 3) (rd b x)) (mul (rd b 4) (rd b y))
  let rows := count 6 9
  let addr := rd (l A.seed) 35
  pick (.cut (.reg 0) addr) 0
    [add root (mul (l 4) rows),rd b 11,rows,add (rd b 12) (count 7 10)]

/-- The four published words of the parent of a regular batch. -/
def info (T : HistoryBatchTape.Header) : HistoryBoundedJoin.Info :=
  let rows := T.r*T.left.rows+T.s*T.right.rows
  ⟨T.stream+4*rows,T.parentPins,rows,T.shared+(T.r*T.left.bits+T.s*T.right.bits)⟩

theorem result_value (A : Layout) (T : HistoryBatchTape.Header) (W target : ℕ)
    (raw : ℕ→ℕ) (j : Fin 4) (header : ∀ k : Fin 26, raw (A.batch+k.val)=T.words k)
    (dst : raw (A.seed+35)=target) :
    (resultWord A).natural W (fun _=>0) raw (fun _=>target+j.val) = (info T).words j := by
  have h (k : ℕ) (hk : k<26) : raw (A.batch+k)=T.words ⟨k,hk⟩ := header ⟨k,hk⟩
  fin_cases j <;>
    simp [resultWord,info,HistoryBoundedJoin.Info.words,pick,rd,eqz,add,mul,natOp,natTest,
      Formula.natural,dst,h 1 (by decide),h 3 (by decide),h 4 (by decide),h 6 (by decide),
      h 7 (by decide),h 9 (by decide),h 10 (by decide),h 11 (by decide),h 12 (by decide),
      HistoryBatchTape.Header.words]

theorem result_fits (A : Layout) (W target : ℕ) (raw : ℕ→ℕ) (j : Fin 4)
    (seedRoom : A.seed+37<2^W) (batchRoom : A.batch+26<2^W)
    (room : target+4<2^W) (dst : raw (A.seed+35)=target) :
    (resultWord A).Fits W (fun _=>0) raw (fun _=>target+j.val) := by
  have cursorRoom : target+j.val < 2^W := by have := j.isLt; omega
  have offset : target+j.val-target = j.val := Nat.add_sub_cancel_left target j.val
  simp only [resultWord,pick,rd,eqz,add,mul,Formula.Fits,Formula.natural,
    opFits,natOp,natTest,dst,offset]
  split_ifs <;> (repeat' apply And.intro) <;> first | trivial | omega


end ThreeFlat.RAM.HistoryPartyBatch

end OAI
