import OAI.Hierarchy.ProbeStageWordStore
import OAI.Hierarchy.ProbeStageMaskUpdate

namespace OAI
/-! # Store the occurrence rank, advance its counter, and scatter on first saturation -/

namespace Hierarchy.ProbeStage.RankUpdate
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ContinuationLink PhysicalPinsExpr DescriptorExpr
open scoped Fin.CommRing

/-- The two public slots point at the address and value scratch cells. -/
def storeBlock (w : ℕ) : Block w 5 2 2 where
  first := 0
  emit pc r pub out := ![.publicWord (r 0) (pub 0) (pc 1), .readExternal (r 0) (r 0) (pc 2),
    .publicWord (r 1) (pub 1) (pc 3), .readExternal (r 1) (r 1) (pc 4), .writeExternal (r 0) (r 1) out]

def store (w ptr val : ℕ) : Procedure w := ⟨5,2,2,storeBlock w,![(ptr:Word w),(val:Word w)]⟩

def stored {w : ℕ} (ptr val : ℕ) (m : Memory w) :=
  writeMemory m (m (ptr:Word w).val) (m (val:Word w).val)

theorem store_exec {w : ℕ} (ptr val : ℕ) (m : Memory w) : (store w ptr val).Exec m (stored ptr val m) 5 := by
  intro P R K M pc reg pub exit installed data c input start eqn
  subst input
  change Fin 2 ↪ Fin R at reg
  change Fin 2 → Fin K at pub
  change Fin 5 ↪ Fin P at pc
  have h0 := installed (0 : Fin 5)
  have h1 := installed (1 : Fin 5)
  have h2 := installed (2 : Fin 5)
  have h3 := installed (3 : Fin 5)
  have h4 := installed (4 : Fin 5)
  change M.code (pc 0)=.publicWord (reg 0) (pub 0) (pc 1) at h0
  change M.code (pc 1)=.readExternal (reg 0) (reg 0) (pc 2) at h1
  change M.code (pc 2)=.publicWord (reg 1) (pub 1) (pc 3) at h2
  change M.code (pc 3)=.readExternal (reg 1) (reg 1) (pc 4) at h3
  change M.code (pc 4)=.writeExternal (reg 0) (reg 1) exit at h4
  change c.pc=pc 0 at start
  have d0 : M.publicData (pub 0) = (ptr:Word w) := data (0 : Fin 2)
  have d1 : M.publicData (pub 1) = (val:Word w) := data (1 : Fin 2)
  have ne : reg 0 ≠ reg 1 := reg.injective.ne (by decide)
  let a := c.put (pc 1) (reg 0) (ptr:Word w)
  let b := a.put (pc 2) (reg 0) (m (ptr:Word w).val)
  let d := b.put (pc 3) (reg 1) (val:Word w)
  let e := d.put (pc 4) (reg 1) (m (val:Word w).val)
  refine ⟨5,le_rfl,{e with pc := exit},stored ptr val m,?_,rfl,rfl⟩
  simp [a,b,d,e,advance,Machine.program,start,h0,h1,h2,h3,h4,Instr.run,Config.put,d0,d1,stored]

/-- Common scratch and public word arrays. `rank` is the row's own source or target rank
field, and `counterBase` and `maskBase` already hold the bases for that endpoint block. -/
structure Layout where
  rank : ℕ
  counterBase : ℕ
  maskBase : ℕ
  chosen : ℕ
  ptr : ℕ
  value : ℕ
  head : ℕ
  length : ℕ
  heads : ℕ
  lengths : ℕ
  offsets : ℕ
  clear : ℕ
  quota : ℕ

def cell (a : ℕ) : Formula 1 := .load (.lit a)

def pointer (s : Layout) : Formula 1 := .op .add (cell s.counterBase) (cell s.chosen)

def getRank (s : Layout) : Formula 1 := .load (cell s.ptr)

def increment (s : Layout) : Formula 1 := .op .add (cell s.rank) (.lit 1)

def directory (base chosen : ℕ) : Formula 1 := .load (.op .add (.lit base) (cell chosen))

def activation (s : Layout) : Formula 1 := .select .eq (cell s.value) (.lit s.quota)
  (directory s.lengths s.chosen) (.lit 0)

def page (w : ℕ) (s : Layout) := MaskUpdate.parameters w s.length s.head s.maskBase s.offsets s.clear

/-- Every word assignment is a genuine fixed-size RAM procedure, and the only data-dependent
iteration is the earlier checked advice-list scatter. -/
def procedure (w : ℕ) (s : Layout) : Procedure w :=
  (WordStore.put w s.ptr (pointer s)).seq <| (WordStore.put w s.rank (getRank s)).seq <|
  (WordStore.put w s.value (increment s)).seq <| (store w s.ptr s.value).seq <|
  (WordStore.put w s.head (directory s.heads s.chosen)).seq <| (WordStore.put w s.length (activation s)).seq <|
  MaskUpdate.procedure (page w s)

def assign {w : ℕ} (a : ℕ) (f : Formula 1) (m : Memory w) := Function.update m a (WordStore.value a f m)

def prepared {w : ℕ} (s : Layout) (m : Memory w) :=
  let a := assign s.ptr (pointer s) m
  let b := assign s.rank (getRank s) a
  let c := assign s.value (increment s) b
  let d := stored s.ptr s.value c
  let e := assign s.head (directory s.heads s.chosen) d
  assign s.length (activation s) e

def occurrenceCount {w : ℕ} (s : Layout) (m : Memory w) := ((prepared s m) ((s.length:Word w).val)).val

def image {w : ℕ} (s : Layout) (m : Memory w) := MaskUpdate.image (page w s) (prepared s m) (occurrenceCount s m)

def setupTicks (s : Layout) := (2*(pointer s).work+8)+((2*(getRank s).work+8)+((2*(increment s).work+8)+
  (5+((2*(directory s.heads s.chosen).work+8)+(2*(activation s).work+8)))))

structure Fits (w : ℕ) (s : Layout) : Prop where
  ptr : s.ptr+1 < 2^w
  rank : s.rank+1 < 2^w
  value : s.value+1 < 2^w
  head : s.head+1 < 2^w
  length : s.length+1 < 2^w

theorem execute {w : ℕ} (s : Layout) (m : Memory w) (fit : Fits w s) :
    (procedure w s).Exec m (image s m) (setupTicks s+4+18*occurrenceCount s m) := by
  let a := assign s.ptr (pointer s) m
  let b := assign s.rank (getRank s) a
  let c := assign s.value (increment s) b
  let d := stored s.ptr s.value c
  let e := assign s.head (directory s.heads s.chosen) d
  unfold setupTicks
  rw [show (2*(pointer s).work+8)+((2*(getRank s).work+8)+((2*(increment s).work+8)+
    (5+((2*(directory s.heads s.chosen).work+8)+(2*(activation s).work+8)))))+4+18*occurrenceCount s m =
    (2*(pointer s).work+8)+((2*(getRank s).work+8)+((2*(increment s).work+8)+
    (5+((2*(directory s.heads s.chosen).work+8)+((2*(activation s).work+8)+(4+18*occurrenceCount s m)))))) by omega]
  apply Procedure.Exec.then (WordStore.execute s.ptr (pointer s) m fit.ptr)
  apply Procedure.Exec.then (WordStore.execute s.rank (getRank s) a fit.rank)
  apply Procedure.Exec.then (WordStore.execute s.value (increment s) b fit.value)
  apply Procedure.Exec.then (store_exec s.ptr s.value c)
  apply Procedure.Exec.then (WordStore.execute s.head (directory s.heads s.chosen) d fit.head)
  apply Procedure.Exec.then (WordStore.execute s.length (activation s) e fit.length)
  exact MaskUpdate.execute (page w s) (prepared s m)

end Hierarchy.ProbeStage.RankUpdate

end OAI
