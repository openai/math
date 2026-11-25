import OAI.ThreeFlat.RAM.CheckRowsLoop
import OAI.ThreeFlat.RAM.PhysicalScanLink

namespace OAI
/-! # Linking a read-only row check with an external success continuation -/

namespace ThreeFlat.RAM.CheckRowsBlock

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr ContinuationLink
open scoped Classical Fin.CommRing
variable {w k p r P R K : ℕ}

structure Frame (e : Term w k 1) (p r : ℕ) where
  pc : Fin (9+e.labels) → Fin p
  reg : Fin 4 ↪ Fin r
  temp : Fin e.binds ↪ Fin r
  fresh : ∀ i j, reg i ≠ temp j
  exit : Fin p

namespace Frame
variable {e : Term w k 1} (A : Frame e p r)

def drv (i : Fin 9) : Fin p := A.pc (i.castAdd e.labels)
def loc (i : Fin e.labels) : Fin p := A.pc (Fin.natAdd 9 i)
def labels : CheckRowsLoop.Labels p :=
  ⟨A.drv 5,A.loc e.first,A.drv 6,A.drv 7,A.drv 8,A.exit⟩

def driver (ctrl : ℕ) : Fin 9 → Instr w p r k
  | 0 => .constant (A.reg 2) (ctrl:Word w) (A.drv 1)
  | 1 => .readExternal (A.reg 2) (A.reg 2) (A.drv 2)
  | 2 => .readExternal (A.reg 1) (A.reg 2) (A.drv 3)
  | 3 => .constant (A.reg 0) 0 (A.drv 4)
  | 4 => .constant (A.reg 3) 1 (A.drv 5)
  | 5 => .jumpLt (A.reg 0) (A.reg 1) (A.loc e.first) A.exit
  | 6 => .jumpEq (A.reg 2) (A.reg 3) (A.drv 7) (A.drv 8)
  | 7 => .binary .add (A.reg 0) (A.reg 0) (A.reg 3) (A.drv 5)
  | 8 => .reject

def emit (ctrl : ℕ) : Fin (9+e.labels) → Instr w p r k :=
  Fin.addCases (A.driver ctrl) (e.emit A.loc (fun _ => A.reg 0) A.temp (A.reg 2) (A.drv 6))

theorem advance (M : Machine w p r k) (ctrl : ℕ)
    (rom : ∀ i, M.code (A.pc i)=A.emit ctrl i)
    (c : Config w p r) (m : Memory w) (start : c.pc=A.drv 0) :
    let n := (m (m (ctrl:Word w).val).val).val
    ∃ t ≤ 6+n*(2*e.binds+4), ∃ d : Config w p r, RAM.advance M.program t c m=some (d,m) ∧
      d.pc=(if ∀ i, i<n → e.eval M.publicData m (fun _ => (i:Word w))=1 then A.exit else A.drv 8) := by
  dsimp only
  have driverRom (i : Fin 9) : M.code (A.drv i)=A.driver ctrl i := by
    simpa only [drv,emit,Fin.addCases_left] using rom (i.castAdd e.labels)
  have exprRom (i : Fin e.labels) : M.code (A.loc i)=
      e.emit A.loc (fun _ => A.reg 0) A.temp (A.reg 2) (A.drv 6) i := by
    simpa only [loc,emit,Fin.addCases_right] using rom (Fin.natAdd 9 i)
  have driverOk : CheckRowsLoop.Installed M A.reg A.labels :=
    ⟨driverRom 5,driverRom 6,driverRom 7,driverRom 8⟩
  let f := fun i : ℕ => e.eval M.publicData m (fun _ => (i:Word w))
  have desc : CheckRowsLoop.Describes M A.reg A.labels m e.steps f := by
    intro d entry _
    let z := e.run M.publicData m (fun _ => A.reg 0) A.temp (A.reg 2) (A.drv 6) d
    have frame := (e.run_frame M.publicData m (fun _ => A.reg 0) A.temp (A.reg 2) (A.drv 6) d).2.2
    have result := e.run_result M.publicData m (fun _ => A.reg 0) A.temp (A.reg 2) (A.drv 6) d
      (fun _ j => A.fresh 0 j) A.temp.injective
    refine ⟨z,e.advance_emit M A.loc _ A.temp _ _ exprRom d m entry,e.run_pc ..,
      frame _ (A.reg.injective.ne (by decide : (0:Fin 4)≠2)) (A.fresh 0),
      frame _ (A.reg.injective.ne (by decide : (1:Fin 4)≠2)) (A.fresh 1),
      frame _ (A.reg.injective.ne (by decide : (3:Fin 4)≠2)) (A.fresh 3),?_⟩
    simpa only [f,Fin.cast_val_eq_self,Function.comp_def] using result
  let info := m (ctrl:Word w).val
  let count := m info.val
  let boot := c.put (A.drv 1) (A.reg 2) (ctrl:Word w)
    |>.put (A.drv 2) (A.reg 2) info
    |>.put (A.drv 3) (A.reg 1) count
    |>.put (A.drv 4) (A.reg 0) 0
    |>.put (A.drv 5) (A.reg 3) 1
  have init : RAM.advance M.program 5 c m = some (boot,m) := by
    simp (config:={decide:=true}) [RAM.advance,Machine.program,start,driverRom,driver,Instr.run,boot,
      Config.put,info,count]
  have low : (boot.reg (A.reg 0)).val=0 := by simp (config:={decide:=true}) [boot,Config.put]
  have high : boot.reg (A.reg 1)=count := by simp (config:={decide:=true}) [boot,Config.put]
  have unit : boot.reg (A.reg 3)=1 := by simp [boot,Config.put]
  obtain ⟨t,ht,d,finish,pc⟩ := CheckRowsLoop.walk M A.reg A.labels driverOk m e.steps f desc
    count.val boot rfl unit (by rw [low,high,zero_add])
  refine ⟨5+t,?_,d,advance_trans init finish,?_⟩
  · rw [e.steps_eq,show 2*e.binds+1+3=2*e.binds+4 by omega] at ht
    dsimp only [count,info] at ht
    omega
  · simpa only [low,CheckRowsLoop.passes,zero_add,f,count,info,labels] using pc

end Frame

def linkedFrame (e : Term w k 1) (pc : Fin (9+e.labels) ↪ Fin P)
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

def block (e : Term w k 1) (ctrl : ℕ) : Block w (9+e.labels) (4+e.binds) k where
  first := (0 : Fin 9).castAdd e.labels
  emit pc reg φ exit j := (linkedFrame e pc reg φ exit).emit ctrl (j.cast (by simp))

theorem advance_block (e : Term w k 1) (ctrl : ℕ)
    (pc : Fin (9+e.labels) ↪ Fin P) (reg : Fin (4+e.binds) ↪ Fin R)
    (φ : Fin k → Fin K) (exit : Fin P) (M : Machine w P R K)
    (installed : (block e ctrl).Installed M pc reg φ exit)
    (c : Config w P R) (m : Memory w) (start : c.pc=pc (block e ctrl).first) :
    let n := (m (m (ctrl:Word w).val).val).val
    ∃ t ≤ 6+n*(2*e.binds+4), ∃ d : Config w P R, advance M.program t c m=some (d,m) ∧
      d.pc=(if ∀ i, i<n → e.eval (M.publicData ∘ φ) m (fun _ => (i:Word w))=1 then exit
        else pc ((8:Fin 9).castAdd e.labels)) ∧ M.code (pc ((8:Fin 9).castAdd e.labels))=.reject := by
  dsimp only
  let A := linkedFrame e pc reg φ exit
  have rom (i : Fin (9+(e.mapPublic φ).labels)) : M.code (A.pc i)=A.emit ctrl i := by
    let j : Fin (9+e.labels) := i.cast (by simp)
    have same : j.cast (by simp : 9+e.labels=9+(e.mapPublic φ).labels)=i := Fin.ext rfl
    have hi := installed j
    change M.code (A.pc i)=A.emit ctrl (j.cast (by simp)) at hi
    rwa [same] at hi
  have begins : c.pc=A.drv 0 := start
  obtain ⟨t,ht,d,run,dpc⟩ := A.advance M ctrl rom c m begins
  refine ⟨t,by simpa using ht,d,run,?_,?_⟩
  · simpa only [Term.eval_mapPublic,show A.exit=exit from rfl,
      show A.drv 8=pc ((8:Fin 9).castAdd e.labels) from rfl] using dpc
  · have h := rom ((8:Fin 9).castAdd (e.mapPublic φ).labels)
    have hit : M.code (A.drv 8)=A.driver ctrl 8 := by
      simpa only [Frame.drv,Frame.emit,Fin.addCases_left] using h
    calc
      M.code (pc ((8:Fin 9).castAdd e.labels)) = M.code (A.drv 8) := rfl
      _ = A.driver ctrl 8 := hit
      _ = .reject := by simp [Frame.driver]

end ThreeFlat.RAM.CheckRowsBlock

end OAI
