import OAI.ThreeFlat.RAM.ContinuationLink
import OAI.ThreeFlat.RAM.DeterministicBlock

namespace OAI
/-! # Bounded preparatory procedures in arbitrary native callers -/

namespace ThreeFlat.RAM.PhysicalProcedure

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink

structure Procedure (w : ℕ) where
  labels : ℕ
  registers : ℕ
  slots : ℕ
  block : Block w labels registers slots
  publicData : Fin slots → Word w

variable {w : ℕ}

/-- Scratch and private state can start arbitrarily. The externally observable postcondition
relates the input memory to the memory when the caller regains control. -/
def Procedure.Spec (A : Procedure w) (pre : Memory w → Prop)
    (post : Memory w → Memory w → Prop) (budget : ℕ) : Prop :=
  ∀ {P R K : ℕ} (M : Machine w P R K) (pc : Fin A.labels ↪ Fin P)
    (reg : Fin A.registers ↪ Fin R) (pub : Fin A.slots → Fin K) (exit : Fin P),
    A.block.Installed M pc reg pub exit →
    (∀ i, M.publicData (pub i) = A.publicData i) →
    ∀ (c : Config w P R) (m : Memory w), c.pc = pc A.block.first → pre m →
      ∃ t, t ≤ budget ∧ ∃ c' m', advance M.program t c m = some (c',m') ∧
        c'.pc = exit ∧ post m m'

def Procedure.seq (A B : Procedure w) : Procedure w where
  labels := A.labels+B.labels
  registers := A.registers+B.registers
  slots := A.slots+B.slots
  block :=
    (A.block.reindex (Fin.castAddEmb B.registers) (Fin.castAdd B.slots)).seq
      (B.block.reindex (Fin.natAddEmb A.registers) (Fin.natAdd A.slots))
  publicData := Fin.addCases A.publicData B.publicData

theorem Procedure.Spec.mono {A : Procedure w} {pre pre' : Memory w → Prop}
    {post post' : Memory w → Memory w → Prop} {budget budget' : ℕ}
    (h : A.Spec pre post budget) (p : ∀ m, pre' m → pre m)
    (q : ∀ m o, post m o → post' m o) (b : budget ≤ budget') : A.Spec pre' post' budget' := by
  intro P R K M pc reg pub exit hi hd c m start pm
  obtain ⟨t,ht,c',m',adv,hpc,hq⟩ := h M pc reg pub exit hi hd c m start (p m pm)
  exact ⟨t,ht.trans b,c',m',adv,hpc,q m m' hq⟩

theorem Procedure.Spec.seq {A B : Procedure w} {pre mid : Memory w → Prop}
    {left right : Memory w → Memory w → Prop} {ka kb : ℕ}
    (a : A.Spec pre left ka) (b : B.Spec mid right kb) (composable : ∀ m o, left m o → mid o) :
    (A.seq B).Spec pre (fun m o => ∃ tmp, left m tmp ∧ right tmp o) (ka+kb) := by
  intro P R K M pc reg pub exit installed data c m start hp
  obtain ⟨ia,ib⟩ := (Block.seq_installed _ _ M pc reg pub exit).mp installed
  have da (i : Fin A.slots) : M.publicData (pub (i.castAdd B.slots)) = A.publicData i := by
    simpa [Procedure.seq] using data (i.castAdd B.slots)
  have db (i : Fin B.slots) : M.publicData (pub (Fin.natAdd A.slots i)) = B.publicData i := by
    simpa [Procedure.seq] using data (Fin.natAdd A.slots i)
  obtain ⟨t,ht,c₁,m₁,h₁,hpc,hl⟩ := a M ((Fin.castAddEmb B.labels).trans pc)
    ((Fin.castAddEmb B.registers).trans reg) (pub ∘ Fin.castAdd B.slots)
    (pc (Fin.natAdd A.labels B.block.first)) ia da c m start hp
  obtain ⟨u,hu,c₂,m₂,h₂,hpc',hr⟩ := b M ((Fin.natAddEmb A.labels).trans pc)
    ((Fin.natAddEmb A.registers).trans reg) (pub ∘ Fin.natAdd A.slots)
    exit ib db c₁ m₁ hpc (composable m m₁ hl)
  exact ⟨t+u,Nat.add_le_add ht hu,c₂,m₂,advance_trans h₁ h₂,hpc',m₁,hl,hr⟩

end ThreeFlat.RAM.PhysicalProcedure

end OAI
