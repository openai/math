import OAI.ThreeFlat.RAM.TickProcedureContracts
import OAI.ThreeFlat.RAM.NextStage

namespace OAI
/-! # Native admission postconditions and exact stage-pointer advancement -/

namespace ThreeFlat.RAM
open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink PhysicalProcedure TickFuel
variable {W : ℕ}

namespace TickStageSpec

theorem Admission.mono {F : Type*} [Semiring F] {field : FieldCode F W} {n r k : ℕ}
    {b : Block W n r k} {data : Fin k→Word W} {pre good pre' good' : Memory W→Prop}
    {post post' : Memory W→Memory W→Prop} {t t' : ℕ}
    (proof : Admission field b data pre good post t)
    (input : ∀ m,pre' m → pre m) (accept : ∀ m,pre' m → (good' m ↔ good m))
    (result : ∀ m out,pre' m → good' m → post m out → post' m out) (cost : t≤t') :
    Admission field b data pre' good' post' t' := by
  intro p regs slots M pc reg pub exit inst values c m begin h
  obtain ⟨yes,no⟩ := proof M pc reg pub exit inst values c m begin (input m h)
  constructor
  · intro ok
    obtain ⟨ticks,bound,c',out,done,valid,run⟩ := yes ((accept m h).mp ok)
    exact ⟨ticks,bound.trans cost,c',out,done,result m out h ok valid,run⟩
  · intro bad
    have no' : ¬good m := fun ok=>bad ((accept m h).mpr ok)
    have halted : Returns field M.program t c m 0 := no no'
    exact halted.later cost

end TickStageSpec

namespace NextStage

def memory (cell : Word W) (m : Memory W) : Memory W :=
  writeMemory m cell (m (m cell.val+4).val)

theorem spec (cell : Word W) (input : Memory W) :
    (procedure cell).Spec (fun m=>m=input) (fun _ out=>out=memory cell input) 6 := by
  intro p r k M pc reg pub exit installed _ c m first same
  subst m
  obtain ⟨d,adv,ret⟩ := run cell M pc reg pub exit installed c input first
  exact ⟨6,le_rfl,d,_,adv,ret,rfl⟩

end NextStage
end ThreeFlat.RAM

end OAI
