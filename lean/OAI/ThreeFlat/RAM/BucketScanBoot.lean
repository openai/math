import OAI.ThreeFlat.RAM.BucketScanROM

namespace OAI
/-! # Initializing the bucket scanner from the five runtime header words -/

namespace ThreeFlat.RAM.BucketScanROM

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM HistoryRowLoop

variable {w p r k n : ℕ}

/-- Load the source, group array, counter array, destination, and source limit.
Each public parameter holds the external address of its corresponding header. -/
def bootOps (R : Fin 12 ↪ Fin r) (ptr : Fin 5 → Fin k) : List (Op r k) :=
  [.publicWord (R 0) (ptr 0), .read (R 0) (R 0),
   .publicWord (R 1) (ptr 1), .read (R 1) (R 1),
   .publicWord (R 2) (ptr 2), .read (R 2) (R 2),
   .publicWord (R 3) (ptr 3), .read (R 3) (R 3),
   .publicWord (R 5) (ptr 4), .read (R 5) (R 5)]

def headers (ptr : Fin 5 → Fin k) (data : Fin k → Word w) (m : Memory w) : BucketRegisters w :=
  let atHeader (i : Fin 5) := m (data (ptr i)).val
  ⟨atHeader 0, atHeader 1, atHeader 2, atHeader 3, atHeader 4⟩

def bootEmit (R : Fin 12 ↪ Fin r) (ptr : Fin 5 → Fin k) (rows : Fin 10 → Fin p)
    (guard bad : Fin p) : Fin 10 → Instr w p r k :=
  opRows w (bootOps R ptr) (Fin.lastCases guard rows) bad

theorem advance_boot (M : Machine w p r k) (R : Fin 12 ↪ Fin r) (ptr : Fin 5 → Fin k)
    (rows : Fin 10 → Fin p) (guard bad : Fin p)
    (code : ∀ i, M.code (rows i) = bootEmit R ptr rows guard bad i)
    (state : Word w) (rs : Regs w r) (priv : Word w → Word w) (m : Memory w) :
    ∃ out, advance M.program 10 ⟨rows 0,state,rs,priv⟩ m = some (⟨guard,state,out,priv⟩,m) ∧
      BucketRegisters.view R out = headers ptr M.publicData m := by
  let loc : Fin 11 → Fin p := Fin.lastCases guard rows
  have before (i : Fin 10) : loc i.castSucc = rows i := by
    simp only [loc, Fin.lastCases_castSucc]
  have head : loc (0 : Fin 11) = rows 0 := before 0
  have tail : loc (Fin.last 10) = guard := Fin.lastCases_last
  have linked : Contains M bad (loc (0 : Fin 11)) (bootOps R ptr) (loc (Fin.last 10)) := by
    apply contains_opRows M bad (bootOps R ptr) loc
    intro i
    change M.code (loc (show Fin 11 from (show Fin 10 from i).castSucc)) = bootEmit R ptr rows guard bad i
    rw [before]
    exact code i
  have image : Contains M bad (rows 0) (bootOps R ptr) guard := by
    rw [←head, ←tail]
    exact linked
  have exec : ∃ es out, trace M.publicData state (bootOps R ptr) rs m = some (es,out,m) ∧
      BucketRegisters.view R out = headers ptr M.publicData m := by
    refine ⟨_,_,rfl,?_⟩
    simp [BucketRegisters.view,headers,Function.update,R.injective.eq_iff]
  obtain ⟨es,out,tr,hdr⟩ := exec
  exact ⟨out,HistoryBucketEmitter.advance_trace image state rs out priv m m es tr,hdr⟩

theorem advance_from_headers (M : Machine w p r k) (R : Fin 12 ↪ Fin r) (ptr : Fin 5 → Fin k)
    (boot : Fin 10 → Fin p) (loc : Fin 23 → Fin p) (exit bad : Fin p)
    (startup : ∀ i, M.code (boot i) = bootEmit R ptr boot (loc (Fin.last 22)) bad i)
    (loop : ∀ i, M.code (loc i) = emit R loc exit bad i)
    (count : ℕ) (state : Word w) (rs : Regs w r) (priv : Word w → Word w) (m : Memory w)
    (size : (headers ptr M.publicData m).source.val + count*3 = (headers ptr M.publicData m).stop.val) :
    ∃ out, advance M.program (11+count*23) ⟨boot 0,state,rs,priv⟩ m =
      some (⟨exit,state,out,priv⟩,walk BucketRegisters.next BucketRegisters.update count
        (headers ptr M.publicData m) m) := by
  obtain ⟨live,load,hdr⟩ := advance_boot M R ptr boot _ bad startup state rs priv m
  have liveSize : (live (R 0)).val+count*3=(live (R 5)).val := by
    change (BucketRegisters.view R live).source.val+count*3=(BucketRegisters.view R live).stop.val
    rw [hdr]
    exact size
  obtain ⟨out,run⟩ := advance_scan M R loc exit bad loop count state live priv m liveSize
  rw [hdr] at run
  exact ⟨out,by simpa only [← Nat.add_assoc] using advance_trans load run⟩

def bootPc (n : ℕ) (i : Fin 10) : Fin (10+(23+n)) := i.castAdd _
def scanPc (n : ℕ) (i : Fin 23) : Fin (10+(23+n)) := Fin.natAdd 10 (i.castAdd n)
def callerPc (n : ℕ) (i : Fin n) : Fin (10+(23+n)) := Fin.natAdd 10 (Fin.natAdd 23 i)

/-- All 33 rows installed in a single machine before arbitrary caller code. -/
def bootMachine (R : Fin 12 ↪ Fin r) (ptr : Fin 5 → Fin k) (exit bad : Fin n)
    (tail : Fin n → Instr w (10+(23+n)) r k) (data : Fin k → Word w) :
    Machine w (10+(23+n)) r k where
  entry := bootPc n 0
  code := Fin.addCases
    (bootEmit R ptr (bootPc n) (scanPc n (Fin.last 22)) (callerPc n bad))
    (Fin.addCases (emit R (scanPc n) (callerPc n exit) (callerPc n bad)) tail)
  publicData := data

theorem advance_bootMachine (R : Fin 12 ↪ Fin r) (ptr : Fin 5 → Fin k) (exit bad : Fin n)
    (tail : Fin n → Instr w (10+(23+n)) r k) (data : Fin k → Word w)
    (count : ℕ) (state : Word w) (rs : Regs w r) (priv : Word w → Word w) (m : Memory w)
    (size : (headers ptr data m).source.val + count*3 = (headers ptr data m).stop.val) :
    let M := bootMachine R ptr exit bad tail data
    ∃ out, advance M.program (11+count*23) ⟨M.entry,state,rs,priv⟩ m =
      some (⟨callerPc n exit,state,out,priv⟩,walk BucketRegisters.next BucketRegisters.update count
        (headers ptr data m) m) := by
  apply advance_from_headers (bootMachine R ptr exit bad tail data) R ptr (bootPc n) (scanPc n)
    (callerPc n exit) (callerPc n bad) _ _ count state rs priv m size
  · intro i; simp [bootMachine,bootPc]
  · intro i; simp [bootMachine,scanPc]

end ThreeFlat.RAM.BucketScanROM

end OAI
