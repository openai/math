import OAI.ThreeFlat.RAM.PhysicalProcedure

namespace OAI
/-! # Mounted rows of a finite bank of native procedures -/

namespace ThreeFlat.RAM.ProcedureBank

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink PhysicalProcedure

variable {w p r k : ℕ}

/-- The last row jumps directly to the caller's exit. -/
def program : (h : ℕ) → (Fin (h+1) → Procedure w) → Procedure w
  | 0, f => f 0
  | h+1, f => (f 0).seq (program h (fun i => f i.succ))

/-- A particular row as it occurs in the physical machine. -/
structure Site (M : Machine w p r k) (A : Procedure w) where
  pc : Fin A.labels ↪ Fin p
  reg : Fin A.registers ↪ Fin r
  pub : Fin A.slots → Fin k
  next : Fin p
  installed : A.block.Installed M pc reg pub next
  data : ∀ i,M.publicData (pub i)=A.publicData i

abbrev Site.first {M : Machine w p r k} {A : Procedure w} (s : Site M A) := s.pc A.block.first

structure Mounted (h : ℕ) (f : Fin (h+1) → Procedure w) (M : Machine w p r k)
    (entry exit : Fin p) where
  site : ∀ i,Site M (f i)
  start : (site 0).first=entry
  step : ∀ i : Fin h,(site i.castSucc).next=(site i.succ).first
  finish : (site (Fin.last h)).next=exit

/-- Extract each indexed code bank, operand frame and continuation from the installed sequence. -/
def sitesFin : (h : ℕ) → (f : Fin (h+1) → Procedure w) → (M : Machine w p r k) →
    (pc : Fin (program h f).labels ↪ Fin p) → (reg : Fin (program h f).registers ↪ Fin r) →
    (pub : Fin (program h f).slots → Fin k) → (exit : Fin p) →
    (program h f).block.Installed M pc reg pub exit →
    (∀ i,M.publicData (pub i)=(program h f).publicData i) → Mounted h f M (pc (program h f).block.first) exit
  | 0, f, M, pc, reg, pub, exit, table, words =>
    let one : Site M (f 0) := ⟨pc,reg,pub,exit,table,words⟩
    { site := Fin.cases one (fun i => Fin.elim0 i)
      start := rfl
      step := fun i => Fin.elim0 i
      finish := rfl }
  | h+1, f, M, pc, reg, pub, exit, table, words => by
    let A := f 0
    let B := program h (fun i => f i.succ)
    have split := (Block.seq_installed _ _ M pc reg pub exit).mp table
    have leftWords (i : Fin A.slots) : M.publicData (pub (i.castAdd B.slots))=A.publicData i := by
      have found := words (i.castAdd B.slots)
      change M.publicData (pub (i.castAdd B.slots))=(A.seq B).publicData (i.castAdd B.slots) at found
      simpa only [Procedure.seq,Fin.addCases_left] using found
    have rightWords (i : Fin B.slots) : M.publicData (pub (Fin.natAdd A.slots i))=B.publicData i := by
      have found := words (Fin.natAdd A.slots i)
      change M.publicData (pub (Fin.natAdd A.slots i))=(A.seq B).publicData (Fin.natAdd A.slots i) at found
      simpa only [Procedure.seq,Fin.addCases_right] using found
    let later := sitesFin h (fun i => f i.succ) M ((Fin.natAddEmb A.labels).trans pc)
      ((Fin.natAddEmb A.registers).trans reg) (pub ∘ Fin.natAdd A.slots) exit split.2 rightWords
    let head : Site M A := ⟨(Fin.castAddEmb B.labels).trans pc,(Fin.castAddEmb B.registers).trans reg,
      pub ∘ Fin.castAdd B.slots,pc (Fin.natAdd A.labels B.block.first),split.1,leftWords⟩
    refine ⟨Fin.cases head (fun i => later.site i),rfl,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact later.start.symm
      · exact later.step j
    · exact later.finish


end ThreeFlat.RAM.ProcedureBank

end OAI
