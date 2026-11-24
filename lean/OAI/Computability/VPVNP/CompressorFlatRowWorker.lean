import OAI.Computability.VPVNP.CompressorFlatRowOperands

/-!
# A fixed whole-level worker for repeated local descriptor calls

The original worker runs with the computed public operands and local cursor.
A successful return advances the global row cursor, while choice streams,
external effects and rejection agree with the original body.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.FlatRows

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open private contains_indexed from OAI.Computability.VPVNP.PrimedStackRAMCode

variable {w p r k : ℕ} (T : Template p r k) (load : Fin (k+1) → Bool)

/-- Number of program counters for the prologue, original body, and final return instruction. -/
abbrev PCs (p r : ℕ) (load : Fin (k+1) → Bool) := (prologue r load).length+p+1

/-- Relocate an original body program counter past the operand-loading prologue. -/
def bodyPC (i : Fin p) : Fin (PCs p r load) :=
  ⟨(prologue r load).length+i.val,by unfold PCs; have := i.isLt; omega⟩

/-- Map a prologue counter into the flattened program, transferring to the original entry when
the prologue finishes. -/
def prePC (j : Fin ((prologue r load).length+1)) : Fin (PCs p r load) :=
  if h : j.val < (prologue r load).length then ⟨j.val,by unfold PCs; omega⟩ else bodyPC (r := r) load T.entry

private def badPC : Fin (PCs p r load) := Fin.last ((prologue r load).length+p)

private def liftOp : Instr w p r k → Instr w (PCs p r load) (Registers r k) (Params k)
  | .constant a x t => .constant (ordinary k a) x (bodyPC load t)
  | .publicWord a j t => .copy (ordinary k a) (slot r j.castSucc) (bodyPC load t)
  | .stateWord a t => .copy (ordinary k a) (slot r (Fin.last k)) (bodyPC load t)
  | .copy a b t => .copy (ordinary k a) (ordinary k b) (bodyPC load t)
  | .binary op a b c t => .binary op (ordinary k a) (ordinary k b) (ordinary k c) (bodyPC load t)
  | .loadPrivate a b t => .loadPrivate (ordinary k a) (ordinary k b) (bodyPC load t)
  | .storePrivate a b t => .storePrivate (ordinary k a) (ordinary k b) (bodyPC load t)
  | .jumpEq a b y n => .jumpEq (ordinary k a) (ordinary k b) (bodyPC load y) (bodyPC load n)
  | .jumpLt a b y n => .jumpLt (ordinary k a) (ordinary k b) (bodyPC load y) (bodyPC load n)
  | .choose y n => .choose (bodyPC load y) (bodyPC load n)
  | .readExternal a b t => .readExternal (ordinary k a) (ordinary k b) (bodyPC load t)
  | .writeExternal a b t => .writeExternal (ordinary k a) (ordinary k b) (bodyPC load t)
  | .returnState _ => .returnState (scratch r k 2)
  | .accept => .accept
  | .reject => .reject

/-- The whole-level template. The operand array is indexed by (local public
parameter or local cursor, base/stride/bias). -/
def compile : Template (PCs p r load) (Registers r k) (Params k) where
  literalWidth := max 2 T.literalWidth
  entry := prePC T load 0
  code i :=
    let ops := prologue r load
    if hp : i.val < ops.length then
      ((ops[i.val]).emit (prePC T load ⟨i.val+1,by change i.val < (prologue r load).length at hp; omega⟩) (badPC load)).resize _
    else if hb : i.val-ops.length < p then
      liftOp load ((T.code ⟨i.val-ops.length,hb⟩).resize _)
    else .reject

private theorem resize_twice {b f : ℕ} (op : Instr b p r k) (h : b ≤ f) :
    (op.resize f).resize w = op.resize w := by
  cases op with
  | constant reg v t =>
    have hlt : v.val < 2^f := v.isLt.trans_le (Nat.pow_le_pow_right (by decide) h)
    simp [Instr.resize,Nat.mod_eq_of_lt hlt]
  | _ => rfl

private theorem body_code (pub : Public k w) (i : Fin p) :
    ((compile T load).instantiate w pub).code (bodyPC (r := r) load i) = liftOp load ((T.code i).resize w) := by
  let n := (prologue r load).length
  have hlt : ¬ n+i.val < n := by omega
  have hb : n+i.val-n < p := by rw [Nat.add_sub_cancel_left]; exact i.isLt
  change ((compile T load).code (bodyPC load i)).resize w = _
  simp only [compile,bodyPC]
  change ((if hp : n+i.val < n then _ else if h : n+i.val-n < p then _ else _ : Instr (max 2 T.literalWidth) (PCs p r load) (Registers r k) (Params k))).resize w = _
  rw [dite_eq_right hlt,dite_eq_left hb]
  have he : (⟨n+i.val-n,hb⟩ : Fin p) = i := Fin.ext (Nat.add_sub_cancel_left ..)
  rw [he]
  have h (op : Instr T.literalWidth p r k) :
      (liftOp load (op.resize (max 2 T.literalWidth))).resize w = liftOp load (op.resize w) := by
    have hw := resize_twice (w := w) op (le_max_right 2 T.literalWidth)
    rw [← hw]
    generalize op.resize (max 2 T.literalWidth) = op'
    cases op' <;> rfl
  exact h _

private theorem pre_contains (pub : Public k w) :
    Contains ((compile T load).instantiate w pub) (badPC load)
      (prePC T load 0) (prologue r load) (bodyPC load T.entry) := by
  have last : prePC T load (Fin.last (prologue r load).length) = bodyPC load T.entry := by simp [prePC]
  rw [← last]
  apply contains_indexed _ _ _ (prePC T load)
  intro i
  have hpre : (prePC T load i.castSucc).val = i.val := by simp [prePC,i.isLt]
  change ((compile T load).code (prePC T load i.castSucc)).resize w = _
  simp only [compile,hpre,dite_eq_left i.isLt]
  exact resize_twice _ (le_max_left 2 T.literalWidth)

private theorem bad_code (pub : Public k w) :
    ((compile T load).instantiate w pub).code (badPC load) = .reject := by
  let n := (prologue r load).length
  change ((compile T load).code (badPC load)).resize w = _
  simp only [compile,badPC,Fin.val_last]
  change ((if hp : n+p < n then _ else if h : n+p-n < p then _ else _ : Instr (max 2 T.literalWidth) (PCs p r load) (Registers r k) (Params k))).resize w = _
  rw [dite_eq_right (by omega),dite_eq_right (by omega)]; rfl

private def liftConfig (global : Word w) (operands : Fin k → Word w) (c : Config w p r) :
    Config w (PCs p r load) (Registers r k) :=
  ⟨bodyPC load c.pc,global,registers c.reg (Fin.snoc operands c.persistent) ![global,1,global+1],c.privateMem⟩

/-- Preserve the body's events and rejection, and replace a successful return by the next
global row cursor. -/
def result (s : Word w) (rep : Report w) : Report w := ⟨rep.events,rep.result.map (fun _ => s+1)⟩

private def mapAction {C D : Type*} (s : Word w) (f : C → D) : CallAction w C → CallAction w D
  | .localStep c => .localStep (f c)
  | .branch g => .branch (f ∘ g)
  | .read a g => .read a (f ∘ g)
  | .write a v c => .write a v (f c)
  | .finish v => .finish (v.map (fun _ => s+1))
  | .reject => .reject

private theorem body_step (pub : Public k w) (s : Word w) (v : Fin k → Word w) (c : Config w p r) :
    ((compile T load).instantiate w pub).program.step (liftConfig load s v c) =
      mapAction s (liftConfig load s v) ((T.instantiate w v).program.step c) := by
  change (((compile T load).instantiate w pub).code (bodyPC load c.pc)).run _ _ = mapAction _ _ (((T.code c.pc).resize w).run v c)
  rw [body_code]
  generalize (T.code c.pc).resize w = op
  cases op <;> simp only [liftOp,Instr.run,liftConfig,mapAction,Config.put,Config.store,
    registers_ordinary,registers_slot,registers_scratch,Fin.snoc_castSucc,Fin.snoc_last,update_ordinary,Function.comp_def]
  all_goals first | rfl | (split <;> rfl) | (congr 1; funext b; cases b <;> rfl)

private theorem body_run (pub : Public k w) (s : Word w) (v : Fin k → Word w) (f : ℕ)
    (c : Config w p r) (m : Memory w) (bs : List Bool) :
    execute ((compile T load).instantiate w pub).program f (liftConfig load s v c) m bs =
      (execute (T.instantiate w v).program f c m bs).map (result s) := by
  induction f generalizing c m bs with
  | zero => rfl
  | succ f ih =>
    rw [execute,body_step,execute]
    cases h : (T.instantiate w v).program.step c <;> simp only [mapAction,Function.comp_apply]
    all_goals first
      | rfl
      | (split <;> rfl)
      | (rw [ih]; simp [Option.map_map,result,Report.prepend,Function.comp_def])
      | (cases bs <;> simp [ih,Option.map_map,result,Report.prepend,Function.comp_def])

/-- A successful local call contributes exactly its original events after the
operand prologue. Rejection and its accepted branch stream are preserved. -/
theorem execute_flat (pub : Public k w) (s : Word w) (m : Memory w) (bs : List Bool) (f : ℕ) :
    let vals := value load pub s m
    let src := (T.instantiate w (fun j => vals j.castSucc)).program
    let flat := ((compile T load).instantiate w pub).program
    execute flat (f+(3+7*(k+1))) (flat.start s) m bs =
      (execute src f (src.start (vals (Fin.last k))) m bs).map (fun rep =>
        ⟨events load pub s m ++ rep.events,rep.result.map (fun _ => s+1)⟩) := by
  intro vals src flat
  have init : flat.start s = ⟨prePC T load 0,s,fun _ => 0,fun _ => 0⟩ := rfl
  rw [init,← prologue_length (r := r) load,
    (pre_contains T load pub).execute (bad_code T load pub),run_eq_trace,prologue_trace]
  simp only [Option.bind_some]
  have full : Fin.snoc (fun j : Fin k => vals j.castSucc) (vals (Fin.last k)) = vals := by
    funext j; cases j using Fin.lastCases <;> simp
  have exactConfig : (⟨bodyPC load T.entry,s,registers (fun _ => 0) vals ![s,1,s+1],fun _ => 0⟩ :
      Config w (PCs p r load) (Registers r k)) =
      liftConfig load s (fun j => vals j.castSucc) (src.start (vals (Fin.last k))) := by
    simp only [liftConfig,src,Machine.program,Template.instantiate,full]
  change ((execute _ f (⟨bodyPC load T.entry,s,registers (fun _ => 0) vals ![s,1,s+1],fun _ => 0⟩ : Config w (PCs p r load) (Registers r k)) m bs).map _) = _
  rw [exactConfig,body_run]
  simp [Option.map_map,result,Function.comp_def]
  rfl

end CompressorRecords.FlatRows

end VPVNP
end Computability
end OAI
