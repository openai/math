import OAI.Computability.VPVNP.PairSimulationDFS
import OAI.Computability.VPVNP.CompressorRecordPreimageScan
import OAI.Computability.VPVNP.PrimedInputRAMFlowEval

/-!
# Converting preimage identifiers to child descriptor addresses

A native pass reads a site's stored count and child identifiers. It writes
a header and a separate row of addresses in the older level's descriptor
table. The input order, including the empty preimage list, is preserved.
The child scan reads and writes one word per old position independently
of the widths of all tensor fields.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.DescriptorRows

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM CompressorRecords
open scoped Fin.CommRing

variable {w : ℕ}

private abbrev word (w n : ℕ) : Word w := (n : Word w)

private theorem val_word {n : ℕ} (h : n < 2^w) : (word w n).val = n := Nat.mod_eq_of_lt h

/-- Register 0 scans identifiers up to register 1. Register 2 is the
destination cursor. Registers 3–5 contain the older table base, its
descriptor stride and the unit. Register 6 holds the current address. -/
def body : Flow 7 0 :=
  .seq (.line (.read 6 0)) <|
  .seq (.line (.binary .mul 6 6 4)) <|
  .seq (.line (.binary .add 6 6 3)) <|
  .seq (.line (.write 2 6)) <|
  .seq (.line (.binary .add 0 0 5)) (.line (.binary .add 2 2 5))

/-- While the input cursor is below its end, read each child identifier, convert it to an
address in the older descriptor table, and write that address at the advancing destination
cursor. -/
def scan : Flow 7 0 := .whileLt 0 1 body

/-- Compute a child descriptor's address in word arithmetic by adding its identifier times the
older table's row stride to the table base. -/
def address (base stride id : Word w) : Word w := id*stride+base

private def advance (rs : Regs w 7) (value : Word w) : Regs w 7 :=
  Function.update (Function.update (Function.update rs 6 value) 0 (rs 0 + rs 5)) 2 (rs 2 + rs 5)

private def events (src dst value addr : Word w) : List (Event w) :=
  [.read src value,.tick,.tick,.write dst addr,.tick,.tick]

private theorem body_exec (pub : Fin 0 → Word w) (state : Word w) (rs : Regs w 7) (m : Memory w) :
    let id := m (rs 0).val
    let addr := address (rs 3) (rs 4) id
    Flow.Exec pub state body rs m (events (rs 0) (rs 2) id addr)
      (advance rs addr) (writeMemory m (rs 2) addr) := by
  dsimp only
  unfold body events advance address
  apply Flow.Exec.seq (.line rfl)
  apply Flow.Exec.seq (.line rfl)
  apply Flow.Exec.seq (.line rfl)
  apply Flow.Exec.seq (.line rfl)
  apply Flow.Exec.seq (.line rfl)
  apply Flow.Exec.line
  simp (config := {decide := true}) [Op.effect,BinaryOp.eval,Function.update]

/-- Exact state of the output row, with all other memory cells retained. -/
def rowMemory (src dst count : ℕ) (base stride : Word w) (m : Memory w) : Memory w := fun i =>
  if dst ≤ i ∧ i < dst+count then address base stride (m (src+(i-dst))) else m i

private theorem rowMemory_succ (src dst count : ℕ) (base stride : Word w) (m : Memory w)
    (h : dst < 2^w) (before : src+(count+1) ≤ dst) :
    rowMemory (src+1) (dst+1) count base stride (writeMemory m (word w dst) (address base stride (m src))) =
      rowMemory src dst (count+1) base stride m := by
  funext i
  by_cases hd : i = dst
  · subst i; simp [rowMemory,writeMemory,val_word h]
  · simp only [rowMemory,writeMemory,val_word h]
    split_ifs <;> first | rfl | (congr 2; omega)

/-- The finite loop scans exactly the indicated interval, returning its
external probe count and instruction count even for an empty child row. -/
theorem scan_exec (pub : Fin 0 → Word w) (state : Word w) (rs : Regs w 7) (m : Memory w)
    (src dst count : ℕ) (base stride : Word w) (hs : rs 0 = word w src)
    (he : rs 1 = word w (src+count)) (hd : rs 2 = word w dst) (hb : rs 3 = base)
    (hst : rs 4 = stride) (hone : rs 5 = 1) (fit : dst+count < 2^w) (before : src+count ≤ dst) :
    ∃ es out, Flow.Exec pub state scan rs m es out (rowMemory src dst count base stride m) ∧
      countProbes es = 2*count ∧ es.length = 7*count+1 ∧ choiceBits es = [] := by
  induction count generalizing rs m src dst with
  | zero =>
    have hn : ¬ rs 0 < rs 1 := by rw [hs, he]; simp
    have hm : rowMemory src dst 0 base stride m = m := by funext i; simp [rowMemory]
    rw [hm]
    exact ⟨[.tick],rs,.whileDone hn,rfl,rfl,rfl⟩
  | succ n ih =>
    have hfit : src+(n+1) < 2^w := by omega
    have lt : rs 0 < rs 1 := by
      change (rs 0).val < (rs 1).val
      rw [hs,he,val_word (by omega : src < 2^w),val_word hfit]; omega
    let addr := address base stride (m src)
    let out := advance rs addr
    let m' := writeMemory m (word w dst) addr
    have ex := body_exec pub state rs m
    rw [hs,hd,hb,hst,val_word (by omega : src < 2^w)] at ex
    change Flow.Exec pub state body rs m (events (word w src) (word w dst) (m src) addr) out m' at ex
    obtain ⟨es,last,loop,hcost,hlen,hchoice⟩ := ih out m' (src+1) (dst+1)
      (by simp [out,advance,Function.update,hs,hone,word])
      (by simp [out,advance,Function.update,he,word]; ring)
      (by simp [out,advance,hd,hone,word])
      (by simp [out,advance,Function.update,hb]) (by simp [out,advance,Function.update,hst])
      (by simp [out,advance,Function.update,hone]) (by omega) (by omega)
    have hm := rowMemory_succ src dst n base stride m (by omega) before
    change rowMemory (src+1) (dst+1) n base stride m' = _ at hm
    refine ⟨_,last,hm ▸ Flow.Exec.whileStep lt ex loop,?_,?_,?_⟩
    · simp [events,countProbes,hcost]; omega
    · simp [events,hlen]; omega
    · simpa [events,choiceBits] using hchoice

/-- Link the identifier scan to arbitrary native successor code. -/
theorem linked_scan {p : ℕ} {M : Machine w p 7 0} {pc : scan.Label → Fin p} {stop bad : Fin p}
    (hl : Flow.Linked M scan pc stop bad) (hbad : M.code bad = .reject)
    (state : Word w) (priv : Word w → Word w) (rs : Regs w 7) (m : Memory w)
    (src dst count : ℕ) (base stride : Word w) (hs : rs 0 = word w src)
    (he : rs 1 = word w (src+count)) (hd : rs 2 = word w dst) (hb : rs 3 = base)
    (hst : rs 4 = stride) (hone : rs 5 = 1) (fit : dst+count < 2^w) (before : src+count ≤ dst) :
    ∃ es out, countProbes es = 2*count ∧ choiceBits es = [] ∧ ∀ fuel bs,
      execute M.program (7*count+1+fuel) ⟨pc scan.entry,state,rs,priv⟩ m bs =
        (execute M.program fuel ⟨stop,state,out,priv⟩ (rowMemory src dst count base stride m) bs).map
          (Flow.prependEvents es) := by
  obtain ⟨es,out,run,probes,steps,bits⟩ := scan_exec M.publicData state rs m src dst count base stride
    hs he hd hb hst hone fit before
  refine ⟨es,out,probes,bits,?_⟩
  intro fuel bs
  simpa only [steps,bits,List.nil_append] using run.execute hl hbad priv fuel bs

/-- A separate fixed three-probe block loads the preimage count from
register 0 and writes the row pointer and count at the node's first two
descriptor cells. Register 1 holds the row pointer, register 2 the node
address, and register 3 the unit. -/
def header : List (Op 5 0) :=
  [.read 4 0,.write 2 1,.binary .add 2 2 3,.write 2 4]

theorem header_native (pub : Fin 0 → Word w) (state : Word w) (regs : Regs w 5)
    (mem : Memory w) (priv : Word w → Word w) :
    let M := (template header 4).instantiate w pub
    let n := mem (regs 0).val
    execute M.program 5 ⟨M.entry,state,regs,priv⟩ mem [] =
      some ⟨[.read (regs 0) n,.write (regs 2) (regs 1),.tick,.write (regs 2+regs 3) n],some n⟩ := by
  change execute _ (1 + header.length) _ _ _ = _
  rw [execute_template, run_eq_trace]
  simp (config := {decide := true}) [header,trace,Op.effect,BinaryOp.eval,Function.update]

/-- A scanned preimage row and the written header have precisely the
representation read by the native stack traversal. -/
theorem represents_DFS_row (mem : Memory w) (node src dst : ℕ) (countCell base stride : Word w)
    (ids : List (Word w)) (hrow : rowRepresents mem countCell (word w src) ids)
    (hsrc : src < 2^w) (fit : dst+ids.length < 2^w) (before : node+1 < dst)
    :
    let final := rowMemory src dst ids.length base stride mem
    let headers := writeMemory (writeMemory final (word w node) (word w dst))
      (word w (node+1)) (mem countCell.val)
    DFS.Row headers node dst (ids.map (address base stride)) := by
  dsimp only
  refine ⟨by omega,by simpa using fit,?_,?_,?_⟩
  · simp only [writeMemory,val_word (by omega : node+1 < 2^w),val_word (by omega : node < 2^w),
      ite_eq_right (by omega : node ≠ node+1),↓reduceIte]
  · simp only [writeMemory,val_word (by omega : node+1 < 2^w),↓reduceIte,List.length_map]
    exact Fin.ext (hrow.1.trans (val_word (by omega : ids.length < 2^w)).symm)
  · intro i
    have hi : i.val < ids.length := by simpa using i.isLt
    have hh := hrow.2 ⟨i.val,hi⟩
    rw [val_word hsrc] at hh
    simp only [writeMemory,val_word (by omega : node+1 < 2^w),val_word (by omega : node < 2^w),
      ite_eq_right (by omega : dst+i.val ≠ node), ite_eq_right (by omega : dst+i.val ≠ node+1)]
    simp [rowMemory,show dst+i.val < dst+ids.length by omega,hh]

end PairSimulation.DescriptorRows

end VPVNP
end Computability
end OAI
