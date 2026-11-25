import OAI.ThreeFlat.RAM.ChunkRequestExpr

namespace OAI
/-! # Execution and frame of a native chunk request check -/

namespace ThreeFlat.RAM.ChunkRequests

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr

variable {w p r k : ℕ}

/-- The fixed register layout is cursor, tag, old base, new base, flag, stride, and stop. -/
structure RegisterFrame (t r : ℕ) where
  slot : Fin 7 ↪ Fin r
  tmp : Fin t ↪ Fin r
  fresh : ∀ i j, slot i ≠ tmp j

abbrev Registers (w k r : ℕ) := RegisterFrame (rowTerm w k).binds r

def RegisterFrame.input {t : ℕ} (R : RegisterFrame t r) (i : Fin 5) : Fin r :=
  R.slot (i.castAdd 2)

structure Counters (n p : ℕ) where
  guard : Fin p
  exit : Fin p
  next : Fin p
  expr : Fin n → Fin p

abbrev Labels (w k p : ℕ) := Counters (rowTerm w k).labels p

structure Installed (M : Machine w p r k) (R : Registers w k r) (L : Labels w k p) : Prop where
  guard : M.code L.guard = .jumpLt (R.slot 0) (R.slot 6) (L.expr (rowTerm w k).first) L.exit
  expr : ∀ i, M.code (L.expr i) = (rowTerm w k).emit L.expr R.input R.tmp (R.slot 4) L.next i
  next : M.code L.next = .binary .add (R.slot 0) (R.slot 0) (R.slot 5) L.guard

private def evaluated (D : Fin k → Word w) (R : Registers w k r) (L : Labels w k p)
    (c : Config w p r) (m : Memory w) :=
  (rowTerm w k).run D m R.input R.tmp (R.slot 4) L.next c

def body (D : Fin k → Word w) (R : Registers w k r) (L : Labels w k p)
    (c : Config w p r) (m : Memory w) : Config w p r × Memory w :=
  let d := evaluated D R L c m
  (d.put L.guard (R.slot 0) (d.reg (R.slot 0) + d.reg (R.slot 5)), m)

theorem advance_body (M : Machine w p r k) (R : Registers w k r) (L : Labels w k p)
    (rom : Installed M R L) (c : Config w p r) (m : Memory w)
    (hc : c.pc = L.expr (rowTerm w k).first) :
    advance M.program 60 c m = some (body M.publicData R L c m) := by
  let d := evaluated M.publicData R L c m
  have expr : advance M.program (rowTerm w k).steps c m = some (d,m) :=
    (rowTerm w k).advance_emit M _ _ _ _ _ rom.expr c m hc
  have pc : d.pc = L.next := (rowTerm w k).run_pc _ _ _ _ _ _ _
  have next : advance M.program 1 d m = some (body M.publicData R L c m) := by
    simp [advance, Machine.program, pc, rom.next, Instr.run, BinaryOp.eval, body, d]
  rw [show 60 = (rowTerm w k).steps + 1 by rw [rowTerm_steps]]
  exact advance_trans expr next

private theorem evaluated_reg (D : Fin k → Word w) (R : Registers w k r) (L : Labels w k p)
    (c : Config w p r) (m : Memory w) (j : Fin 7) (hj : j ≠ 4) :
    (evaluated D R L c m).reg (R.slot j) = c.reg (R.slot j) :=
  ((rowTerm w k).run_frame D m R.input R.tmp (R.slot 4) L.next c).2.2
    _ (R.slot.injective.ne hj) (R.fresh j)

theorem body_reg (D : Fin k → Word w) (R : Registers w k r) (L : Labels w k p)
    (c : Config w p r) (m : Memory w) (j : Fin 7) (h₀ : j ≠ 0) (h₄ : j ≠ 4) :
    (body D R L c m).1.reg (R.slot j) = c.reg (R.slot j) := by
  simpa only [body, Config.put, Function.update_of_ne (R.slot.injective.ne h₀)] using
    evaluated_reg D R L c m j h₄

theorem body_cursor (D : Fin k → Word w) (R : Registers w k r) (L : Labels w k p)
    (c : Config w p r) (m : Memory w) :
    (body D R L c m).1.reg (R.slot 0) = c.reg (R.slot 0) + c.reg (R.slot 5) := by
  simp only [body, Config.put, Function.update_self, evaluated_reg D R L c m 0 (by decide),
    evaluated_reg D R L c m 5 (by decide)]

theorem body_flag (D : Fin k → Word w) (R : Registers w k r) (L : Labels w k p)
    (c : Config w p r) (m : Memory w) :
    (body D R L c m).1.reg (R.slot 4) =
      if rowMatches m (readRow m (c.reg (R.slot 0))) (c.reg (R.slot 1))
        (c.reg (R.slot 2)) (c.reg (R.slot 3)) then c.reg (R.slot 4) else 0 := by
  have run := (rowTerm w k).run_result D m R.input R.tmp (R.slot 4) L.next c
    (fun i => R.fresh (i.castAdd 2)) R.tmp.injective
  rw [rowTerm_eval] at run
  have h₀ : (c.reg ∘ R.input) 0 = c.reg (R.slot 0) := rfl
  have h₁ : (c.reg ∘ R.input) 1 = c.reg (R.slot 1) := rfl
  have h₂ : (c.reg ∘ R.input) 2 = c.reg (R.slot 2) := rfl
  have h₃ : (c.reg ∘ R.input) 3 = c.reg (R.slot 3) := rfl
  have h₄ : (c.reg ∘ R.input) 4 = c.reg (R.slot 4) := rfl
  simp only [h₀,h₁,h₂,h₃,h₄] at run
  by_cases ok : rowMatches m (readRow m (c.reg (R.slot 0))) (c.reg (R.slot 1))
    (c.reg (R.slot 2)) (c.reg (R.slot 3)) <;>
    simpa only [body,evaluated,Config.put,Function.update_of_ne (R.slot.injective.ne
      (by decide : (4:Fin 7) ≠ 0)),ok,ite_true,ite_false] using run

theorem body_frame (D : Fin k → Word w) (R : Registers w k r) (L : Labels w k p)
    (c : Config w p r) (m : Memory w) :
    (body D R L c m).1.persistent = c.persistent ∧
      (body D R L c m).1.privateMem = c.privateMem :=
  ⟨((rowTerm w k).run_frame D m R.input R.tmp _ _ c).1,
    ((rowTerm w k).run_frame D m R.input R.tmp _ _ c).2.1⟩

end ThreeFlat.RAM.ChunkRequests

end OAI
