import OAI.ThreeFlat.RAM.CompressorIteration
import OAI.ThreeFlat.RAM.PhysicalProcedure

namespace OAI
/-! # A fixed procedure loop driven by a word in the mutable memory -/

namespace ThreeFlat.RAM.PhysicalProcedure.Procedure
open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink
variable {w : ℕ}

def counted (body : Procedure w) (cell : Word w) : Procedure w :=
  let inner := body.block.reindex (Fin.natAddEmb 3) id
  ⟨7+body.labels,3+body.registers,body.slots,CompressorIteration.block cell
    (Fin.castAddEmb body.registers) inner,body.publicData⟩

theorem Spec.atMemory {A : Procedure w} {pre : Memory w → Prop} {post : Memory w → Memory w → Prop}
    {cost : ℕ} (h : A.Spec pre post cost) (m : Memory w) (hm : pre m) :
    A.Spec (fun x => x=m) (fun _ out => post m out) cost := by
  intro P R K M pc reg pub exit rom data c x entry eq
  subst x
  exact h M pc reg pub exit rom data c m entry hm

/-- The counter decrement is the only write by the loop outside its body. -/
theorem counted_spec (body : Procedure w) (cell : Word w) (n cost : ℕ)
    (inv : ℕ → Memory w → Prop)
    (step : ∀ z m, inv (z+1) m → (m cell.val).val=z+1 →
      body.Spec (fun m' => m'=writeMemory m cell (m cell.val-1))
        (fun _ m' => (m' cell.val).val=z ∧ inv z m') cost) :
    (body.counted cell).Spec (fun m => inv n m ∧ (m cell.val).val=n)
      (fun _ m' => inv 0 m') (n*(7+cost)+4) := by
  intro P R K M pc reg pub exit installed data c m entry initial
  let : NeZero (body.counted cell).labels := ⟨by change 7+body.labels≠0; omega⟩
  have root : (Fin.castAddEmb body.labels) (0 : Fin 7) = (0 : Fin (body.counted cell).labels) := by
    apply Fin.ext
    change (0 : Fin 7).val = (0 : Fin (body.counted cell).labels).val
    simp
  let inner := body.block.reindex (Fin.natAddEmb 3) id
  let ip := (Fin.natAddEmb 7).trans pc
  have rom : inner.Installed M ip reg pub (pc 0) := by
    intro i
    rw [show ip i = pc (Fin.natAdd 7 i) by rfl]
    have row := installed (Fin.natAdd 7 i)
    simp only [counted,CompressorIteration.block,Fin.addCases_right] at row
    exact row.trans (congrArg (fun stop => inner.emit ip reg pub stop i) (congrArg pc root))
  have nested := (body.block.reindex_installed (Fin.natAddEmb 3) id M ip reg pub (pc 0)).mp rom
  apply CompressorIteration.run cell inner (Fin.castAddEmb body.registers) M pc reg pub exit installed
    inv cost _ n c m initial.1 initial.2 entry
  intro z m' d h hc hp
  exact step z m' h hc M ip ((Fin.natAddEmb 3).trans reg) (pub ∘ id) (pc 0)
    nested data d _ hp rfl

end ThreeFlat.RAM.PhysicalProcedure.Procedure

end OAI
