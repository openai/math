import OAI.Computability.VPVNP.CompressorSliceSchedule
import OAI.Computability.VPVNP.CompressorTermRecord
import OAI.Computability.VPVNP.ShrinkLayout

/-!
# Width arrays for shrinking-step kernel slices

The AB bundle and each surviving supply wire are repartitioned by the same
quotient and remainder rule. Each visit reads the total from external memory
and writes one subdivision width. A surviving supply total includes the
selected payload and one selector field per repetition.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSliceArrays

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression
open Compression.PackingData

variable {w : ℕ}

private abbrev div (a b : Word w) := BinaryOp.div.eval a b
private abbrev mod (a b : Word w) := BinaryOp.mod.eval a b

/-- Public data give the total address, number of pieces, and output base. -/
def splitOps : List (Op 7 3) :=
  [.stateWord 0, .publicWord 1 0, .read 2 1, .publicWord 3 1,
   .binary .div 4 2 3, .binary .mod 5 2 3, .constant 6 1,
   .binary .add 0 0 6, .binary .div 5 5 0, .binary .div 5 5 5,
   .binary .add 4 4 5, .publicWord 1 2, .stateWord 5, .binary .add 1 1 5,
   .write 1 4]

/-- Word width assigned to piece `i` when splitting a total `b` among `q` pieces. For `i < q`,
the first `b % q` pieces get one more than `b / q`. -/
def splitValue (b q i : Word w) : Word w :=
  let t := div (mod b q) (i+1)
  div b q + div t t

/-- Trace of one split visit, reading the total, writing the width at the output base plus
piece index `i`, and returning `i + 1`. -/
def splitReport (p : Fin 3 → Word w) (mem : Memory w) (i : Word w) : Report w :=
  let b := mem (p 0).val
  ⟨[.tick,.tick,.read (p 0) b,.tick,.tick,.tick,.tick,.tick,.tick,.tick,
    .tick,.tick,.tick,.tick,.write (p 2+i) (splitValue b (p 1) i)],some (i+1)⟩

theorem split_native (p : Fin 3 → Word w) (mem : Memory w) (i : Word w) :
    let M := (template splitOps 0).instantiate w p
    execute M.program 16 (M.program.start i) mem [] = some (splitReport p mem i) := by
  let M := (template splitOps 0).instantiate w p
  change execute M.program (1+splitOps.length) ⟨M.entry,i,fun _ => 0,fun _ => 0⟩ mem [] = _
  rw [execute_template,run_eq_trace]
  simp (config := {decide := true}) [splitOps,splitReport,splitValue,trace,Op.effect,BinaryOp.eval,
    div,mod,Function.update]
  exact ⟨rfl,rfl⟩

private theorem div_val (a b : Word w) : (div a b).val = a.val / b.val :=
  Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt a.isLt)

private theorem mod_val (a b : Word w) : (mod a b).val = a.val % b.val :=
  Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt a.isLt)

/-- Division of the remainder by the next cursor, followed by its nonzero
indicator, supplies the extra bit exactly to the initial remainder-many fields. -/
theorem splitValue_eq (b q i : Word w) (hi : i.val < q.val) :
    (splitValue b q i).val = splitWidth b.val q.val ⟨i.val,hi⟩ := by
  let t := div (mod b q) (i+1)
  have hone : (1 : Word w).val = 1 := by rw [Fin.val_one', Nat.mod_eq_of_lt (show 1 < 2^w by have := q.isLt; omega)]
  have hnext : (i+1).val = i.val+1 := by
    rw [Fin.val_add, hone, Nat.mod_eq_of_lt (by have := q.isLt; omega)]
  have ht : t.val = (b.val % q.val) / (i.val+1) := by rw [div_val,mod_val,hnext]
  have hq : 0 < q.val := by omega
  have hsum : (∑ j, splitWidth b.val q.val j) < 2^w := (sum_splitWidth _ _ hq) ▸ b.isLt
  have hfit : splitWidth b.val q.val ⟨i.val,hi⟩ < 2^w := (Finset.single_le_sum (fun j _ => Nat.zero_le (splitWidth b.val q.val j))
    (Finset.mem_univ (⟨i.val,hi⟩ : Fin q.val))).trans_lt hsum
  change (div b q + div t t).val = _
  rw [Fin.val_add,div_val,div_val]
  apply (Nat.mod_eq_of_lt _).trans
  · exact (show b.val / q.val + t.val / t.val = splitWidth b.val q.val ⟨i.val,hi⟩ by
      by_cases h : i.val < b.val % q.val
      · rw [Nat.div_self (ht ▸ Nat.div_pos h (Nat.zero_lt_succ _)), splitWidth, ite_eq_left h]
      · rw [ht, Nat.div_eq_of_lt (show b.val % q.val < i.val+1 by omega), Nat.zero_div, Nat.add_zero, splitWidth, ite_eq_right h])
  · by_cases h : i.val < b.val % q.val
    · rw [Nat.div_self (ht ▸ Nat.div_pos h (Nat.zero_lt_succ _))]
      simpa only [splitWidth,ite_eq_left h] using hfit
    · rw [ht,Nat.div_eq_of_lt (show b.val % q.val < i.val+1 by omega),Nat.zero_div,Nat.add_zero]
      exact (Nat.div_le_self ..).trans_lt b.isLt

/-- Initial contents outside the target width row are preserved. -/
structure SplitAt (p : Fin 3 → Word w) (initial mem : Memory w) (k : ℕ) : Prop where
  rows : ∀ i : Fin (p 1).val, i.val < k →
    (mem ((p 2).val+i.val)).val = splitWidth (initial (p 0).val).val (p 1).val i
  frame : ∀ x, x < (p 2).val ∨ (p 2).val+k ≤ x → mem x = initial x

/-- The piece-count word is also the stopping cursor. Every call has two probes
and sixteen instructions, including the return. -/
theorem split_prefix (p : Fin 3 → Word w) (mem : Memory w) (k : ℕ) (hk : k ≤ (p 1).val)
    (fit : (p 2).val + (p 1).val ≤ 2^w)
    (apart : (p 0).val < (p 2).val ∨ (p 2).val+(p 1).val ≤ (p 0).val) :
    let M := (template splitOps 0).instantiate w p
    ∃ rs, runSegment M.program 16 (some 0) mem (List.replicate k []) = some rs ∧
      SplitAt p mem (after mem (eventLog rs)) k ∧
      endState (some 0) rs = some (Fin.ofNat _ k) ∧ rs.length = k ∧
      ∀ r ∈ rs, r.probes = 2 ∧ r.events.length+1 = 16 := by
  let M := (template splitOps 0).instantiate w p
  induction k with
  | zero => exact ⟨[],rfl,⟨fun _ h => by omega,fun _ _ => rfl⟩,rfl,rfl,by simp⟩
  | succ k ih =>
    obtain ⟨rs,hr,cur,he,hl,hw⟩ := ih (by omega)
    let i : Word w := Fin.ofNat _ k
    have hv : i.val = k := Nat.mod_eq_of_lt (by have := (p 1).isLt; omega)
    have hn : i+1 = Fin.ofNat _ (k+1) := by
      apply Fin.ext
      rw [Fin.val_add,Fin.val_one',hv,Nat.add_mod_mod]; rfl
    have ha : (p 2+i).val = (p 2).val + k := by
      rw [Fin.val_add,hv,Nat.mod_eq_of_lt (by omega)]
    let m := after mem (eventLog rs)
    let r := splitReport p m i
    have hmem : after mem (eventLog (rs ++ [r])) =
        writeMemory m (p 2+i) (splitValue (m (p 0).val) (p 1) i) := by
      simp only [eventLog,List.flatMap_append,after,List.foldl_append]
      rfl
    have hs : m (p 0).val = mem (p 0).val := cur.frame _ (by omega)
    refine ⟨rs ++ [r],?_,⟨?_,?_⟩,?_,by simp [hl],?_⟩
    · rw [List.replicate_succ',PrimedSchedule.runSegment_append,hr]
      simp only [Option.bind_some,he,runSegment,split_native,Option.map_some]
      rfl
    · intro j hj
      rw [hmem]
      by_cases h : j.val = k
      · simp only [writeMemory,ha,h,↓reduceIte,hs]
        rw [splitValue_eq (mem (p 0).val) (p 1) i (by omega)]
        exact congrArg _ (Fin.ext (hv.trans h.symm))
      · simpa only [writeMemory,ha,ite_eq_right (show (p 2).val+j.val ≠ (p 2).val+k by omega)] using
          cur.rows j (by omega)
    · intro x hx
      rw [hmem,writeMemory,ha,ite_eq_right (by omega)]
      exact cur.frame _ (by omega)
    · rw [endState_append]; exact congrArg some hn
    · intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hw _ ht
      · obtain rfl := List.mem_singleton.mp ht; exact ⟨rfl,rfl⟩

/-- Materialize the complete target array from the total cell. -/
theorem split_run (p : Fin 3 → Word w) (mem : Memory w)
    (fit : (p 2).val + (p 1).val ≤ 2^w)
    (apart : (p 0).val < (p 2).val ∨ (p 2).val+(p 1).val ≤ (p 0).val) :
    let M := (template splitOps 0).instantiate w p
    ∃ rs, runSegment M.program 16 (some 0) mem (List.replicate (p 1).val []) = some rs ∧
      SplitAt p mem (after mem (eventLog rs)) (p 1).val ∧
      endState (some 0) rs = some (p 1) ∧ rs.length = (p 1).val ∧
      ∀ r ∈ rs, r.probes = 2 ∧ r.events.length+1 = 16 := by
  simpa using split_prefix p mem (p 1).val le_rfl fit apart


open SliceSchedule

/-- The native descriptor pass with its exact local cost. -/
structure Built (o t B : Word w) (old new : List ℕ) (m : Memory w) (rs : Passes w) : Prop where
  runs : NativePasses o t B old.length new.length m rs
  stored : Stored B old new m (rs.result m)
  calls : rs.all.length = 2 + 2*(old.length+new.length) + 2*(old.length*new.length)
  probes : (rs.all.map Report.probes).sum = 2 + 5*(old.length+new.length) +
    6*(old.length*new.length) + 8*(copyRecords old new).length
  instructions : (rs.all.map fun r => r.events.length+1).sum = 16 + 22*(old.length+new.length) +
    46*(old.length*new.length) + 28*(copyRecords old new).length

theorem build_arrays (o t B : Word w) (old new : List ℕ) (m : Memory w)
    (space : Workspace o t B old.length new.length)
    (ho : old.sum < 2^w) (hn : new.sum < 2^w)
    (src : ∀ i (hi : i < old.length), (m (o.val+i)).val = old[i])
    (dst : ∀ i (hi : i < new.length), (m (t.val+i)).val = new[i]) :
    ∃ rs, Built o t B old new m rs := by
  obtain ⟨rs,h₁,h₂,h₃,h₄,h₅⟩ := build old new o t B m space ho hn src dst
  exact ⟨rs,h₁,h₂,h₃,h₄,h₅⟩

/-- Put the source total and piece count in the fixed split-worker slots. -/
def splitData (total q t : Word w) : Fin 3 → Word w := ![total,q,t]

/-- A complete native split scan from cursor zero to `q`, with one two-probe report per piece
and the resulting widths in the output row at `t`. -/
structure SplitPass (total q t : Word w) (mem : Memory w) (rs : List (Report w)) : Prop where
  runs : let M := (template splitOps 0).instantiate w (splitData total q t)
    runSegment M.program 16 (some 0) mem (List.replicate q.val []) = some rs
  widths : SplitAt (splitData total q t) mem (after mem (eventLog rs)) q.val
  result : endState (some 0) rs = some q
  length : rs.length = q.val
  cost : ∀ r ∈ rs, r.probes = 2 ∧ r.events.length+1 = 16

/-- Repartition a physical old row. The native split and descriptor schedules
share external memory, including the computed total and the old widths. -/
theorem split_build (o total q t B : Word w) (old : List ℕ) (mem : Memory w)
    (space : Workspace o t B old.length q.val) (hq : 0 < q.val)
    (apart : total.val < t.val ∨ t.val+q.val ≤ total.val)
    (rowsApart : o.val+old.length ≤ t.val ∨ t.val+q.val ≤ o.val)
    (widths : ∀ i (hi : i < old.length), (mem (o.val+i)).val = old[i])
    (sum : (mem total.val).val = old.sum) :
    ∃ split desc, SplitPass total q t mem split ∧
      Built o t B old (List.ofFn (splitWidth old.sum q.val)) (after mem (eventLog split)) desc := by
  let p := splitData total q t
  obtain ⟨rs,hr,hp,he,hl,hc⟩ := split_run p mem space.newFit apart
  let out := after mem (eventLog rs)
  let new := List.ofFn (splitWidth old.sum q.val)
  have hn : new.length = q.val := List.length_ofFn
  have hsum : new.sum = old.sum := List.sum_ofFn.trans (sum_splitWidth _ _ hq)
  have hfit : old.sum < 2^w := sum ▸ (mem total.val).isLt
  have src (i : ℕ) (hi : i < old.length) : (out (o.val+i)).val = old[i] := by
    rw [show out (o.val+i) = mem (o.val+i) from hp.frame _ (show o.val+i < t.val ∨ t.val+q.val ≤ o.val+i by omega)]
    exact widths i hi
  have dst (i : ℕ) (hi : i < new.length) : (out (t.val+i)).val = new[i] := by
    have hj : i < q.val := hn ▸ hi
    have h := hp.rows (⟨i,hj⟩ : Fin q.val) hj
    change (out (t.val+i)).val = splitWidth (mem total.val).val q.val ⟨i,hj⟩ at h
    simpa only [new,List.getElem_ofFn,sum] using h
  obtain ⟨desc,hd⟩ := build_arrays o t B old new out (hn ▸ space) hfit (hsum ▸ hfit) src dst
  exact ⟨rs,desc,⟨hr,hp,he,hl,hc⟩,hd⟩

/-- Read the selected supply field and repetition word, multiply by the fixed
selector width, and store the complete width for the subsequent split pass. -/
def supplyOps : List (Op 6 3) :=
  [.stateWord 0,.constant 1 1,.binary .add 2 0 1,.read 2 2,.publicWord 3 1,
   .binary .mul 2 2 3,.constant 1 2,.binary .add 3 0 1,.publicWord 4 0,
   .binary .add 3 3 4,.read 4 3,.binary .add 4 4 2,.publicWord 5 2,.write 5 4,
   .constant 0 0]

/-- The supply worker’s three public operands in order are the term-field coordinate, selector
width per repetition, and address for the resulting total. -/
def supplyData (coordinate selectors total : Word w) : Fin 3 → Word w :=
  ![coordinate,selectors,total]

/-- Total width of the selected supply field, equal to its payload word plus the repetition
count times the selector width. -/
def supplyValue (p : Fin 3 → Word w) (base : Word w) (m : Memory w) : Word w :=
  m (base+2+p 0).val + m (base+1).val * p 1

/-- Report of the supply worker, reading the repetition count and selected payload from the
term record, writing their combined width to the total cell, and returning zero. -/
def supplyReport (p : Fin 3 → Word w) (base : Word w) (m : Memory w) : Report w :=
  ⟨[.tick,.tick,.tick,.read (base+1) (m (base+1).val),.tick,.tick,.tick,.tick,.tick,.tick,
    .read (base+2+p 0) (m (base+2+p 0).val),.tick,.tick,.write (p 2) (supplyValue p base m),.tick],some 0⟩

theorem supply_native (p : Fin 3 → Word w) (base : Word w) (m : Memory w) :
    let M := (template supplyOps 0).instantiate w p
    execute M.program 16 (M.program.start base) m [] = some (supplyReport p base m) ∧
      after m (supplyReport p base m).events = writeMemory m (p 2) (supplyValue p base m) ∧
      (supplyReport p base m).probes = 3 ∧ (supplyReport p base m).events.length+1 = 16 := by
  let M := (template supplyOps 0).instantiate w p
  refine ⟨?_,rfl,rfl,rfl⟩
  change execute M.program (1+supplyOps.length) ⟨M.entry,base,fun _ => 0,fun _ => 0⟩ m [] = _
  rw [execute_template,run_eq_trace]
  simp (config := {decide := true}) [supplyOps,supplyReport,supplyValue,trace,Op.effect,BinaryOp.eval,Function.update]
  exact ⟨⟨rfl,rfl⟩,rfl⟩

theorem supplyValue_eq (p : Fin 3 → Word w) (base : Word w) (m : Memory w)
    {width : ℕ} (hfit : base.val+2+(p 0).val < 2^w)
    (read : (m (base.val+2+(p 0).val)).val + (m (base.val+1)).val * (p 1).val = width)
    (hw : width < 2^w) : (supplyValue p base m).val = width := by
  have h1 : (base+1).val = base.val+1 := by
    rw [Fin.val_add,Fin.val_one',Nat.mod_eq_of_lt (show 1 < 2^w by omega),Nat.mod_eq_of_lt (by omega)]
  have h2 : (2 : Word w).val = 2 := Nat.mod_eq_of_lt (show 2 < 2^w by omega)
  have h3 : (base+2+p 0).val = base.val+2+(p 0).val := by
    simp only [Fin.val_add,h2,Nat.mod_add_mod,Nat.mod_eq_of_lt hfit]
  rw [supplyValue,Fin.val_add,Fin.val_mul,h3,h1,Nat.add_mod_mod,read,Nat.mod_eq_of_lt hw]

section Supply

open MotifGrid MotifBlocks MotifConversion MotifSelector

variable {K : Type*} [_root_.Field K] {J D S : Type} [Fintype J] [Fintype D] [Fintype S]
variable {a b : D → J} {P : Supply J S} {p : D → ℚ} {q : S → ℚ} {H H' : ℝ}
variable (F : FixedBlock K a b P (realWidths p) (realWidths q) H H')

/-- Given the two addressed cells of the actual term-record image, the native
source reader, subdivision pass and interval construction produce both endpoint
directories for this supply edge. The rest of memory can hold other motifs. -/
theorem supply_build {n : ℕ} (supply : Fin n ≃ S) (hq : ∀ e, 0 < q e)
    (demand : D → ℕ) (v : ↥(outerIndices F demand)) (i : Fin n)
    (prior m : Memory w) (base row u count total t B : BurstRAM.Word w)
    (recFit : base.val+2+n < 2^w) (cap : outerCap F demand < 2^w)
    (rep : u.val = repetitions F demand)
    (record : ∀ x, base.val ≤ x → x < base.val+2+n →
      m x = TermRecord.recordMemory prior base row u supply v.val x)
    (selectors : F.selectorBits < 2^w)
    (wf : supplyWidths F demand v.val (supply i) < 2^w)
    (space : Workspace total t B 1 count.val) (hc : 0 < count.val)
    (apart : total.val < t.val ∨ t.val+count.val ≤ total.val) :
    let pub := supplyData (Fin.ofNat _ i.val) (Fin.ofNat _ F.selectorBits) total
    let r := supplyReport pub base m
    let M := (template supplyOps 0).instantiate w pub
    let width := supplyWidths F demand v.val (supply i)
    let m₁ := after m r.events
    execute M.program 16 (M.program.start base) m [] = some r ∧
    (m₁ total.val).val = width ∧ r.probes = 3 ∧ r.events.length+1 = 16 ∧
    ∃ split desc, SplitPass total count t m₁ split ∧
      Built total t B [width] (List.ofFn (splitWidth width count.val)) (after m₁ (eventLog split)) desc := by
  intro pub r M width m₁
  have hi : (pub 0).val = i.val := Nat.mod_eq_of_lt (by have := i.isLt; omega)
  have hs : (pub 1).val = F.selectorBits := Nat.mod_eq_of_lt selectors
  have exactWidth := TermRecord.recordMemory_supply F prior base row u supply hq demand v cap recFit rep i
  have read : (m (base.val+2+(pub 0).val)).val + (m (base.val+1)).val * (pub 1).val = width := by
    rw [hi,hs,record _ (by omega) (by have := i.isLt; omega),record _ (by omega) (by have := i.isLt; omega)]
    exact exactWidth
  have hval := supplyValue_eq pub base m (hi ▸ (show base.val+2+i.val < 2^w by have := i.isLt; omega)) read wf
  obtain ⟨hr,hm,probes,cost⟩ := supply_native pub base m
  have ht : (m₁ total.val).val = width := by
    change (after m (supplyReport pub base m).events total.val).val = _
    rw [hm]; simpa only [writeMemory,show pub 2 = total from rfl,↓reduceIte] using hval
  refine ⟨hr,ht,probes,cost,?_⟩
  have src (j : ℕ) (hj : j < [width].length) : (m₁ (total.val+j)).val = [width][j] := by
    obtain rfl : j = 0 := by simpa using hj
    simpa using ht
  simpa using split_build total total count t B [width] m₁ space hc apart (by simp; omega) src (by simpa using ht)

end Supply

end CompressorRecords.ShrinkSliceArrays

end VPVNP
end Computability
end OAI
