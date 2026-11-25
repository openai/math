import OAI.ThreeFlat.RAM.PhysicalProcedure
import OAI.ThreeFlat.RAM.TickFuel
import OAI.ThreeFlat.RAM.NativeRelocate

namespace OAI
/-! # Sharing the native register file across the base-zero header shift -/

namespace ThreeFlat.RAM.SharedTickPrelude

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink PhysicalProcedure TickFuel
variable {F : Type*} [Semiring F] {w p r k P K : ℕ}

/-- Renaming program counters keeps both memories, every register and the persistent word. -/
def liftPC (pc : Fin p ↪ Fin P) (c : Config w p r) : Config w P r :=
  ⟨pc c.pc,c.persistent,c.reg,c.privateMem⟩

private theorem lift_entry (pc : Fin p ↪ Fin P) (i : Fin p) (d : Config w P r) (atEntry : d.pc=pc i) :
    liftPC pc (⟨i,d.persistent,d.reg,d.privateMem⟩ : Config w p r)=d := by
  cases d with
  | mk j persistent reg memory =>
    change j=pc i at atEntry
    subst j
    rfl

private def liftAction {C D : Type*} (f : C→D) : CallAction w C→CallAction w D
  | .localStep s => .localStep (f s)
  | .branch q => .branch (fun b=>f (q b))
  | .read a q => .read a (fun x=>f (q x))
  | .write a v s => .write a v (f s)
  | .finish v => .finish v
  | .reject => .reject

private theorem step (pc : Fin p ↪ Fin P) (pub : Fin k→Fin K) (m : Machine w p r k) (M : Machine w P r K)
    (code : ∀ i,M.code (pc i)=NativeRelocate.relocate pc (Function.Embedding.refl _) pub (m.code i))
    (data : ∀ i,M.publicData (pub i)=m.publicData i) (c : Config w p r) :
    M.program.step (liftPC pc c) = liftAction (liftPC pc) (m.program.step c) := by
  change (M.code (pc c.pc)).run M.publicData (liftPC pc c)=liftAction _ ((m.code c.pc).run m.publicData c)
  rw [code]
  cases m.code c.pc <;> simp only [NativeRelocate.relocate,Instr.run,liftAction,liftPC,data,
    Function.Embedding.refl_apply] <;> first | rfl |
    (rename_i lhs rhs yes no; by_cases test : c.reg lhs = c.reg rhs <;> simp only [test, ite_true, ite_false]) |
    (rename_i lhs rhs yes no; by_cases test : c.reg lhs < c.reg rhs <;> simp only [test, ite_true, ite_false]) |
    (congr 1; funext t; cases t <;> rfl)

private theorem mass_lift (pc : Fin p ↪ Fin P) (pub : Fin k→Fin K) (m : Machine w p r k) (M : Machine w P r K)
    (code : ∀ i,M.code (pc i)=NativeRelocate.relocate pc (Function.Embedding.refl _) pub (m.code i))
    (data : ∀ i,M.publicData (pub i)=m.publicData i) (field : FieldCode F w)
    (f : ℕ) (c : Config w p r) (mem : Memory w) :
    mass field M.program f (liftPC pc c) mem = mass field m.program f c mem := by
  induction f generalizing c mem with
  | zero => rfl
  | succ f ih =>
    simp only [mass,step pc pub m M code data]
    cases m.program.step c <;> simp [liftAction,ih]

/-- The caller prelude and tick share registers. Each installs public operands in its own
bank; the native tick requires only its original number of labels beyond the prelude. -/
def attach (A : Procedure w) (fit : A.registers≤r) (m : Machine w p r k) :
    Machine w (A.labels+p) r (A.slots+k) :=
  close (A.block.reindex (Fin.castLEEmb fit) (Fin.castAdd k)) m.entry
    (fun pc i => NativeRelocate.relocate pc (Function.Embedding.refl _) (Fin.natAdd A.slots) (m.code i))
    (Fin.addCases A.publicData m.publicData)

/-- A tick proven for arbitrary entry registers can immediately follow the physical shift.
The statement applies to all native instructions, including access to private memory. -/
theorem attach_returns (A : Procedure w) (fit : A.registers≤r) (m : Machine w p r k)
    (field : FieldCode F w) (pre : Memory w→Prop) (post : Memory w→Memory w→Prop)
    (shift tick : ℕ) (spec : A.Spec pre post shift) (input : Memory w) (allowed : pre input) (v : F)
    (run : ∀ out,post input out → ∀ c : Config w p r,c.pc=m.entry → Returns field m.program tick c out v)
    (cfg : Config w (A.labels+p) r) (entry : cfg.pc=(attach A fit m).entry) :
    Returns field (attach A fit m).program (shift+tick) cfg input v := by
  let M := attach A fit m
  let pc : Fin A.labels ↪ Fin (A.labels+p) := Fin.castAddEmb p
  let callee : Fin p ↪ Fin (A.labels+p) := Fin.natAddEmb A.labels
  let native := fun (p' : Fin p ↪ Fin (A.labels+p)) i =>
    NativeRelocate.relocate p' (Function.Embedding.refl (Fin r)) (Fin.natAdd A.slots) (m.code i)
  let b := A.block.reindex (Fin.castLEEmb fit) (Fin.castAdd k)
  have install := close_installed b m.entry native (Fin.addCases A.publicData m.publicData)
  have sub := (A.block.reindex_installed (Fin.castLEEmb fit) (Fin.castAdd k) M pc
    (Function.Embedding.refl _) id (callee m.entry)).mp install
  have operands (i : Fin A.slots) : M.publicData (i.castAdd k)=A.publicData i := by
    simp [M,attach,close]
  obtain ⟨t,ht,d,out,go,reached,valid⟩ := spec M pc _ _ (callee m.entry) sub operands cfg input entry allowed
  let initial : Config w p r := ⟨m.entry,d.persistent,d.reg,d.privateMem⟩
  have eq : liftPC callee initial=d := lift_entry callee m.entry d reached
  have tail : Returns field M.program tick d out v := by
    intro extra
    rw [←eq,mass_lift callee (Fin.natAdd A.slots) m M (fun i=>close_tail b m.entry native _ i)
      (fun i=>by simp [M,attach,close]) field]
    exact run out valid initial rfl extra
  exact (tail.prefix go).later (by omega)


end ThreeFlat.RAM.SharedTickPrelude

end OAI
