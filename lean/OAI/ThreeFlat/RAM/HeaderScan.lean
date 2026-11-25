import OAI.ThreeFlat.RAM.PhysicalScanLink

namespace OAI
/-! # A callable scan whose interval is loaded from the current stage header -/

namespace ThreeFlat.RAM.HeaderScan

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorScan DescriptorExpr ContinuationLink
open scoped Fin.CommRing

variable {w k p r P R K : ℕ}

structure Frame (e : Term w k 1) (p r : ℕ) where
  pc : Fin (13+e.labels) → Fin p
  reg : Fin 4 ↪ Fin r
  temp : Fin e.binds ↪ Fin r
  fresh : ∀ i j, reg i ≠ temp j
  exit : Fin p

namespace Frame

variable {e : Term w k 1} (A : Frame e p r)

def drv (i : Fin 13) : Fin p := A.pc (i.castAdd e.labels)
def loc (i : Fin e.labels) : Fin p := A.pc (Fin.natAdd 13 i)
def labels : Labels p := ⟨A.drv 10,A.loc e.first,A.drv 11,A.drv 12,A.exit⟩

def driver (current : Word w) (lowOff lenOff : ℕ) : Fin 13 → Instr w p r k
  | 0 => .constant (A.reg 2) current (A.drv 1)
  | 1 => .readExternal (A.reg 2) (A.reg 2) (A.drv 2)
  | 2 => .constant (A.reg 0) (lowOff : Word w) (A.drv 3)
  | 3 => .binary .add (A.reg 0) (A.reg 2) (A.reg 0) (A.drv 4)
  | 4 => .readExternal (A.reg 0) (A.reg 0) (A.drv 5)
  | 5 => .constant (A.reg 1) (lenOff : Word w) (A.drv 6)
  | 6 => .binary .add (A.reg 1) (A.reg 2) (A.reg 1) (A.drv 7)
  | 7 => .readExternal (A.reg 1) (A.reg 1) (A.drv 8)
  | 8 => .binary .add (A.reg 1) (A.reg 0) (A.reg 1) (A.drv 9)
  | 9 => .constant (A.reg 3) 1 (A.drv 10)
  | 10 => .jumpLt (A.reg 0) (A.reg 1) (A.loc e.first) A.exit
  | 11 => .writeExternal (A.reg 0) (A.reg 2) (A.drv 12)
  | 12 => .binary .add (A.reg 0) (A.reg 0) (A.reg 3) (A.drv 10)

def emit (current : Word w) (lowOff lenOff : ℕ) : Fin (13+e.labels) → Instr w p r k :=
  Fin.addCases (A.driver current lowOff lenOff) (e.emit A.loc (fun _ => A.reg 0) A.temp (A.reg 2) (A.drv 11))

theorem advance (M : Machine w p r k) (current : Word w) (lowOff lenOff lo n : ℕ) (stop : lo+n<2^w)
    (rom : ∀ i, M.code (A.pc i) = A.emit current lowOff lenOff i)
    (c : Config w p r) (m₀ : Memory w) (start : c.pc = A.drv 0) (word : ℕ → Word w)
    (lowWord : m₀ (m₀ current.val + (lowOff:Word w)).val = (lo:Word w))
    (lenWord : m₀ (m₀ current.val + (lenOff:Word w)).val = (n:Word w))
    (correct : ∀ (a : Word w) (m : Memory w), lo ≤ a.val → a.val < lo+n →
      agreesOutside lo (lo+n) m m₀ → e.eval M.publicData m (fun _ => a) = word a.val) :
    ∃ steps ≤ 13+n*(2*e.binds+4), ∃ out : Config w p r, out.pc=A.exit ∧
      RAM.advance M.program steps c m₀ = some (out,fillSegment lo n word m₀) := by
  have driverRom (i : Fin 13) : M.code (A.drv i) = A.driver current lowOff lenOff i := by
    simpa only [drv,emit,Fin.addCases_left] using rom (i.castAdd e.labels)
  have exprRom (i : Fin e.labels) : M.code (A.loc i) =
      e.emit A.loc (fun _ => A.reg 0) A.temp (A.reg 2) (A.drv 11) i := by
    simpa only [loc,emit,Fin.addCases_right] using rom (Fin.natAdd 13 i)
  have installed : Installed M A.reg A.labels :=
    ⟨driverRom 10,driverRom 11,driverRom 12⟩
  let info := m₀ current.val
  let boot := c.put (A.drv 1) (A.reg 2) current
    |>.put (A.drv 2) (A.reg 2) info
    |>.put (A.drv 3) (A.reg 0) (lowOff:Word w)
    |>.put (A.drv 4) (A.reg 0) (info+(lowOff:Word w))
    |>.put (A.drv 5) (A.reg 0) (lo:Word w)
    |>.put (A.drv 6) (A.reg 1) (lenOff:Word w)
    |>.put (A.drv 7) (A.reg 1) (info+(lenOff:Word w))
    |>.put (A.drv 8) (A.reg 1) (n:Word w)
    |>.put (A.drv 9) (A.reg 1) ((lo+n:ℕ):Word w)
    |>.put (A.drv 10) (A.reg 3) 1
  have run : RAM.advance M.program 10 c m₀ = some (boot,m₀) := by
    simp (config := {decide:=true}) [RAM.advance,Machine.program,start,driverRom,driver,
      Instr.run,BinaryOp.eval,boot,Config.put,info,lowWord,lenWord,Nat.cast_add]
  have low : (boot.reg (A.reg 0)).val = lo := by
    simp (config := {decide:=true}) [boot,Config.put,Fin.val_cast_of_lt (show lo<2^w by omega)]
  have high : (boot.reg (A.reg 1)).val = lo+n := by
    have upper : boot.reg (A.reg 1)=((lo+n : ℕ) : Word w) := by
      simp (config := {decide:=true}) [boot,Config.put]
    rw [upper,Fin.val_cast_of_lt stop]
  have valid : scanInvariant A.reg lo (lo+n) m₀ boot m₀ :=
    ⟨by simp [boot,Config.put],low.ge,high,fun _ _ => rfl⟩
  have desc := describes_expression M A.reg A.labels e A.loc A.temp A.fresh rfl exprRom
    lo (lo+n) m₀ word correct
  obtain ⟨steps,hsteps,out,exit,finish⟩ :=
    generate M A.reg A.labels installed e.steps word _ desc n boot m₀ rfl valid (by rw [low,high])
  refine ⟨10+steps,?_,out,exit,?_⟩
  · rw [e.steps_eq,show 2*e.binds+1+3=2*e.binds+4 by omega] at hsteps
    omega
  · simpa only [low] using advance_trans run finish

end Frame



def linkedFrame (e : Term w k 1) (pc : Fin (13+e.labels) ↪ Fin P)
    (reg : Fin (4+e.binds) ↪ Fin R) (φ : Fin k → Fin K) (exit : Fin P) :
    Frame (e.mapPublic φ) P R where
  pc i := pc (i.cast (by simp))
  reg := (Fin.castAddEmb e.binds).trans reg
  temp := ((Fin.castLEEmb (by simp) : Fin (e.mapPublic φ).binds ↪ Fin e.binds).trans
    (Fin.natAddEmb 4)).trans reg
  fresh := by
    intro i j equal
    have he := congrArg Fin.val (reg.injective equal)
    change i.val=4+j.val at he
    have := i.isLt
    omega
  exit := exit

def block (e : Term w k 1) (current : Word w) (lowOff lenOff : ℕ) : Block w (13+e.labels) (4+e.binds) k where
  first := (0 : Fin 13).castAdd e.labels
  emit pc reg φ exit j := (linkedFrame e pc reg φ exit).emit current lowOff lenOff (j.cast (by simp))

theorem advance_block (e : Term w k 1) (current : Word w) (lowOff lenOff lo n : ℕ) (stop : lo+n<2^w)
    (pc : Fin (13+e.labels) ↪ Fin P) (reg : Fin (4+e.binds) ↪ Fin R)
    (φ : Fin k → Fin K) (exit : Fin P) (M : Machine w P R K)
    (installed : (block e current lowOff lenOff).Installed M pc reg φ exit)
    (c : Config w P R) (m₀ : Memory w) (start : c.pc=pc (block e current lowOff lenOff).first) (word : ℕ → Word w)
    (lowWord : m₀ (m₀ current.val + (lowOff:Word w)).val = (lo:Word w))
    (lenWord : m₀ (m₀ current.val + (lenOff:Word w)).val = (n:Word w))
    (correct : ∀ (a : Word w) (m : Memory w), lo ≤ a.val → a.val < lo+n →
      agreesOutside lo (lo+n) m m₀ → e.eval (M.publicData ∘ φ) m (fun _ => a) = word a.val) :
    ∃ steps ≤ 13+n*(2*e.binds+4), ∃ out : Config w P R, out.pc=exit ∧
      advance M.program steps c m₀ = some (out,fillSegment lo n word m₀) := by
  let A := linkedFrame e pc reg φ exit
  have rom (i : Fin (13+(e.mapPublic φ).labels)) : M.code (A.pc i)=A.emit current lowOff lenOff i := by
    let j : Fin (13+e.labels) := i.cast (by simp)
    have same : j.cast (by simp : 13+e.labels=13+(e.mapPublic φ).labels) = i := Fin.ext rfl
    have hi := installed j
    change M.code (A.pc i)=A.emit current lowOff lenOff (j.cast (by simp)) at hi
    rwa [same] at hi
  have begins : c.pc=A.drv 0 := start
  have done : A.exit=exit := rfl
  simpa only [Term.binds_mapPublic,done] using A.advance M current lowOff lenOff lo n stop rom c m₀ begins word lowWord lenWord
    (fun a m h u untouched => by simpa using correct a m h u untouched)

end ThreeFlat.RAM.HeaderScan

end OAI
