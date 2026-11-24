import OAI.Computability.VPVNP.PrimedStackRAMCode
import OAI.Computability.VPVNP.LiveStageLinkPaths
import OAI.Computability.VPVNP.CompressorRecordsBlockPlanner

/-!
# Loading local worker operands in a whole-level scan

For each parameter and for the local cursor, the prologue computes
`base + globalRow * stride`, optionally reads the word there, and adds a
fixed offset. The source-worker registers remain zero until its body starts.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.FlatRows

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

open private update_left update_right from OAI.Computability.VPVNP.CompressorRecordFrame
open private probe_append bits_append from OAI.Computability.VPVNP.LiveStageLinkPaths

variable {w r k : ℕ}

/-- Register count for a flattened row worker, including the original registers, operand cache,
and three temporaries. -/
abbrev Registers (r k : ℕ) := r + ((k+1)+3)
/-- Number of public words needed for three address fields per local operand, including the
local cursor. -/
abbrev Params (k : ℕ) := (k+1)*3
/-- Public operand bank indexed by the address-field positions of a flattened row worker. -/
abbrev Public (k w : ℕ) := Fin (Params k) → Word w

/-- Flatten an operand number and its base, stride, or offset field into one public-word index. -/
def field (j : Fin (k+1)) (d : Fin 3) := finProdFinEquiv (j,d)

/-- Embed an original worker register into the leading register bank of the flattened worker. -/
def ordinary (k : ℕ) (j : Fin r) : Fin (Registers r k) := j.castAdd _
/-- Register holding one cached local operand or the local cursor after the prologue. -/
def slot (r : ℕ) (j : Fin (k+1)) : Fin (Registers r k) := (j.castAdd 3).natAdd r
/-- Select one of the three temporary registers following the operand cache. -/
def scratch (r k : ℕ) (j : Fin 3) : Fin (Registers r k) := (j.natAdd (k+1)).natAdd r

/-- Row-dependent address computed from an operand's public base and stride. -/
def addr (p : Public k w) (s : Word w) (j : Fin (k+1)) := p (field j 0)+s*p (field j 1)
/-- Operand supplied to the body after optionally loading from its row address and adding the
public offset. -/
def value (load : Fin (k+1) → Bool) (p : Public k w) (s : Word w) (m : Memory w) (j : Fin (k+1)) :=
  (if load j then m (addr p s j).val else addr p s j)+p (field j 2)

/-- One affine parameter takes seven lines, with the fifth line a single
read for indirect operands and a register copy for direct operands. -/
def operand (r : ℕ) (load : Fin (k+1) → Bool) (j : Fin (k+1)) : List (Op (Registers r k) (Params k)) :=
  let tmp := scratch r k 1
  let dst := slot r j
  [.publicWord tmp (field j 1), .binary .mul dst (scratch r k 0) tmp,
   .publicWord tmp (field j 0), .binary .add dst tmp dst,
   if load j then .read dst dst else .copy dst dst,
   .publicWord tmp (field j 2), .binary .add dst dst tmp]

/-- Seven prologue events for one operand, including an external read precisely when its load
flag is set. -/
def operandEvents (load : Fin (k+1) → Bool) (p : Public k w) (s : Word w) (m : Memory w) (j : Fin (k+1)) :
    List (Event w) :=
  [.tick,.tick,.tick,.tick,if load j then .read (addr p s j) (m (addr p s j).val) else .tick,.tick,.tick]

/-- Combine the body registers, cached operands, and three temporaries into a single register
bank. -/
def registers (core : Fin r → Word w) (cached : Fin (k+1) → Word w) (temps : Fin 3 → Word w) :
    Fin (Registers r k) → Word w := Fin.append core (Fin.append cached temps)

@[simp] theorem registers_ordinary (core : Fin r → Word w) (cache : Fin (k+1) → Word w) (temps : Fin 3 → Word w)
    (j : Fin r) : registers core cache temps (ordinary k j) = core j := Fin.append_left ..
@[simp] theorem registers_slot (core : Fin r → Word w) (cache : Fin (k+1) → Word w) (temps : Fin 3 → Word w)
    (j : Fin (k+1)) : registers core cache temps (slot r j) = cache j := by
  simp [registers,slot]
@[simp] theorem registers_scratch (core : Fin r → Word w) (cache : Fin (k+1) → Word w) (temps : Fin 3 → Word w)
    (j : Fin 3) : registers core cache temps (scratch r k j) = temps j := by simp [registers,scratch]

theorem update_ordinary (core : Fin r → Word w) (cache : Fin (k+1) → Word w) (temps : Fin 3 → Word w)
    (j : Fin r) (v : Word w) :
    Function.update (registers core cache temps) (ordinary k j) v = registers (Function.update core j v) cache temps := by
  exact update_left ..

theorem update_slot (core : Fin r → Word w) (cache : Fin (k+1) → Word w) (temps : Fin 3 → Word w)
    (j : Fin (k+1)) (v : Word w) :
    Function.update (registers core cache temps) (slot r j) v = registers core (Function.update cache j v) temps := by
  simp only [registers,slot,update_right,update_left]

theorem update_scratch (core : Fin r → Word w) (cache : Fin (k+1) → Word w) (temps : Fin 3 → Word w)
    (j : Fin 3) (v : Word w) :
    Function.update (registers core cache temps) (scratch r k j) v = registers core cache (Function.update temps j v) := by
  simp only [registers,scratch,update_right]

variable (load : Fin (k+1) → Bool) (p : Public k w) (s : Word w) (m : Memory w)

private theorem operand_trace (j : Fin (k+1)) (core : Fin r → Word w) (cache : Fin (k+1) → Word w)
    (temps : Fin 3 → Word w) (hs : temps 0 = s) :
    trace p s (operand r load j) (registers core cache temps) m =
      some (operandEvents load p s m j,
        registers core (Function.update cache j (value load p s m j))
          (Function.update temps 1 (p (field j 2))),m) := by
  cases hl : load j <;>
    simp (config := {decide := true}) [operand,operandEvents,value,hl,trace,Op.effect,BinaryOp.eval,addr,
      update_slot,update_scratch,Function.update_idem,hs]

private def loadList (is : List (Fin (k+1))) (cache : Fin (k+1) → Word w) :=
  fun j => if j ∈ is then value load p s m j else cache j

private theorem trace_list (is : List (Fin (k+1))) (core : Fin r → Word w) (cache : Fin (k+1) → Word w)
    (temps : Fin 3 → Word w) (hs : temps 0 = s) :
    ∃ tmp, trace p s (is.flatMap (operand r load)) (registers core cache temps) m =
      some (is.flatMap (operandEvents load p s m),
        registers core (loadList load p s m is cache) (Function.update temps 1 tmp),m) := by
  induction is generalizing cache temps with
  | nil =>
    have h : loadList load p s m [] cache = cache := by funext j; simp [loadList]
    exact ⟨temps 1,by simp [trace,h]⟩
  | cons j is ih =>
    let v := value load p s m
    let temps' := Function.update temps 1 (p (field j 2))
    obtain ⟨tmp,hr⟩ := ih (Function.update cache j (v j)) temps' (by simpa [temps'] using hs)
    have h : loadList load p s m is (Function.update cache j (v j)) =
        loadList load p s m (j::is) cache := by
      funext t
      by_cases ht : t ∈ is <;> by_cases he : t = j <;> simp [loadList,Function.update,ht,he,v]
    refine ⟨tmp,?_⟩
    simp only [List.flatMap_cons,trace_append,operand_trace load p s m j core cache temps hs,Option.bind_some]
    change (trace p s (is.flatMap (operand r load)) (registers core (Function.update cache j (v j)) temps') m).map _ = _
    rw [hr]; simp [h,temps',Function.update_idem]

/-- Instructions that cache all operands for the current global row and calculate the successor
row cursor. -/
def prologue (r : ℕ) (load : Fin (k+1) → Bool) : List (Op (Registers r k) (Params k)) :=
  [.stateWord (scratch r k 0)] ++ (List.finRange (k+1)).flatMap (operand r load) ++
    [.constant (scratch r k 1) 1,.binary .add (scratch r k 2) (scratch r k 0) (scratch r k 1)]

/-- Complete prologue event list for a global row, including the operand reads and cursor
arithmetic. -/
def events := [.tick] ++ (List.finRange (k+1)).flatMap (operandEvents load p s m) ++ [.tick,.tick]

theorem prologue_trace :
    trace p s (prologue r load) (fun _ => 0) m =
      some (events load p s m,registers (fun _ : Fin r => 0) (value load p s m) ![s,1,s+1],m) := by
  let zero : Fin 3 → Word w := fun _ => 0
  let z : Fin (k+1) → Word w := fun _ => 0
  let core : Fin r → Word w := fun _ => 0
  let tmp := Function.update zero 0 s
  have hz : (fun _ => (0 : Word w)) = registers core z zero := by
    funext i; cases i using Fin.addCases with
    | left j => simp [registers,core]
    | right j => cases j using Fin.addCases <;> simp [registers,z,zero]
  obtain ⟨v,hr⟩ := trace_list load p s m (List.finRange _) core z tmp (by simp [tmp])
  have full : loadList load p s m (List.finRange (k+1)) z = value load p s m := by funext j; simp [loadList]
  rw [full] at hr
  have hlast : Function.update (Function.update tmp 1 (1 : Word w)) 2 (s+1) = ![s,1,s+1] := by
    funext j; fin_cases j <;> simp [tmp,Function.update]
  rw [hz]
  simp only [prologue,trace_append,trace,Op.effect,update_scratch,Option.bind_some,pure,bind]
  change ((trace p s ((List.finRange (k+1)).flatMap (operand r load)) (registers core z tmp) m).map _).bind _ = _
  rw [hr]
  simp only [Option.map_some,Option.bind_some,update_scratch,registers_scratch,BinaryOp.eval,Function.update_idem]
  simp [events,core,tmp,Function.update]
  exact congrArg (registers core (value load p s m)) hlast

theorem prologue_length : (prologue r load).length = 3+7*(k+1) := by
  have h (is : List (Fin (k+1))) : (is.flatMap (operand r load)).length = 7*is.length := by
    induction is with
    | nil => simp
    | cons j is ih => simp [operand,ih,Nat.mul_succ]
  simp [prologue,h]; omega

theorem events_cost :
    (events load p s m).length = 3+7*(k+1) ∧
      countProbes (events load p s m) ≤ k+1 ∧ after m (events load p s m) = m ∧
      choiceBits (events load p s m) = [] := by
  have h (is : List (Fin (k+1))) :
      (is.flatMap (operandEvents load p s m)).length = 7*is.length ∧
      countProbes (is.flatMap (operandEvents load p s m)) ≤ is.length ∧
      after m (is.flatMap (operandEvents load p s m)) = m ∧
      choiceBits (is.flatMap (operandEvents load p s m)) = [] := by
    induction is with
    | nil => exact ⟨rfl,le_rfl,rfl,rfl⟩
    | cons j js ih =>
      obtain ⟨hlen,hprobe,hmem,hbits⟩ := ih
      change (List.flatMap (operandEvents load p s m) js).foldl BurstRAM.update m = m at hmem
      cases hj : load j <;>
        simp [operandEvents,hj,countProbes,choiceBits,after,BurstRAM.update,Nat.mul_succ,hlen,hbits,hmem] <;> omega
  obtain ⟨hl,hp,hm,hb⟩ := h (List.finRange (k+1))
  simp only [List.length_finRange] at hl hp
  simp only [events,List.length_append,List.length_cons,List.length_nil,probe_append,bits_append,
    countProbes,choiceBits,after,List.foldl_append,List.foldl_cons,List.foldl_nil,BurstRAM.update,hl,hb] at *
  exact ⟨by omega,by omega,hm,rfl⟩

end CompressorRecords.FlatRows

end VPVNP
end Computability
end OAI
