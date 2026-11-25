import OAI.ThreeFlat.RAM.CachedBlockRun
import OAI.ThreeFlat.RAM.PhysicalProcedure

namespace OAI
/-! # Executing a procedure with its public data supplied by the live cache -/

namespace ThreeFlat.RAM.CachedBlock
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure

theorem advance_procedure {w labels regs slots budget : ℕ} (A : Procedure w)
    {pre : Memory w → Prop} {post : Memory w → Memory w → Prop} (spec : A.Spec pre post budget)
    (nat : Natural A.block) (loc : Fin A.slots → Word w)
    (M : Machine w labels regs slots) (pc reg) (pub : Fin 0 → Fin slots) (exit : Fin labels)
    (rom : (lower loc A.block).Installed M pc reg pub exit)
    (c : Config w labels regs) (m : Memory w) (entry : c.pc = pc (lower loc A.block).first)
    (params : ∀ j, m (loc j).val = A.publicData j) (ready : pre m) :
    ∃ time ≤ 2 * A.slots + budget, ∃ z : Config w labels regs, ∃ out : Memory w,
      z.pc = exit ∧ post m out ∧ advance M.program time c m = some (z, out) := by
  let reads := fun j : Fin A.slots => m (loc j).val
  let b := A.block
  obtain ⟨s, boot, atBody, cached, _, _, _⟩ := CachedBlockLoader.advance loc
    (Fin.natAddEmb A.registers) (body b) M pc reg pub exit rom c m entry
  have bodyRom := CachedBlockLoader.body_installed loc (Fin.natAddEmb A.registers) (body b)
    M pc reg pub exit rom
  obtain ⟨t, ht, z, out, step, done, good⟩ := spec (shadow b M reg exit reads)
    (Fin.castAddEmb labels) ((Fin.castAddEmb A.slots).trans reg) (Fin.castAdd slots)
    (Fin.natAdd A.labels exit) (shadow_installed b M reg exit reads)
    (fun i => (shadow_param b M reg exit reads i).trans (params i))
    (atPC (b.first.castAdd labels) s) m rfl ready
  refine ⟨2 * A.slots + t, Nat.add_le_add_left ht _, atPC exit z, out, rfl, good, ?_⟩
  exact advance_trans boot (advance_body b nat M _ reg pub exit bodyRom reads t b.first s m
    atBody cached step done)

end ThreeFlat.RAM.CachedBlock

end OAI
