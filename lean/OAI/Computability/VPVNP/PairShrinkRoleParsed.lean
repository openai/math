import OAI.Computability.VPVNP.PairShrinkRoleBind

/-! # Retaining the actual argument of a successful native parse -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM BurstRAM.PrivateRAM DFS

variable {w n p r k : ℕ} {α : Type*}

/-- A concrete result of the reader on some finite input stream and entry scratch. -/
def Parsed (reader : Reader w n α) (node : Word w) (x : α) : Prop :=
  ∃ s bits out tail, reader node s bits = some (out, tail) ∧ out.value = x

/-- In addition to the native postcondition, the continuation can use the fact
that the data came from the very reader it is linked to. -/
theorem Realizes.withParsed {reader : Reader w n α} {M : Machine w p r k} {m : Memory w}
    {dfs : Fin 9 ↪ Fin r} {pre : Word w → Config w p r → Prop}
    {post : α → Word w → Config w p r → Prop} (h : Realizes reader M m dfs pre post) :
    Realizes reader M m dfs pre (fun x node c => post x node c ∧ Parsed reader node x) := by
  refine ⟨?_, h.reject⟩
  intro node c bs out tail hc read
  obtain ⟨parts, d, done, frame, store, run⟩ := h.success node c bs out tail hc read
  exact ⟨parts, d, ⟨done, _, bs, out, tail, read, rfl⟩, frame, store, run⟩

theorem Parsed.afterSetup {reader : Reader w n α} {setup : Setup w n}
    {node : Word w} {x : α} (h : Parsed (bind setup.reader (fun _ => reader)) node x) :
    Parsed reader node x := by
  obtain ⟨s, bs, out, tail, hit, value⟩ := h
  change (reader node (setup.updated node s) bs).map _ = some (out, tail) at hit
  obtain ⟨⟨v, rest⟩, done, eqn⟩ := Option.map_eq_some_iff.mp hit
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj eqn
  exact ⟨_, bs, v, rest, done, value⟩

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
