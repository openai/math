import OAI.Computability.VPVNP.LiveStageLinkPaths
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.FinCases

/-!
# The nested stage tag of the compressed pair routine

During the first half the evaluator's old-state bank is unused. Its first
word immediately follows the live counter array, so its address is the sum
of the counter base and the two label counts. Five private instructions
compute this address at call entry. The linked pair table sees the original
eleven public operands and the computed tag address in its twelfth slot.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairTag
open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

variable {p r w : ℕ}

/-- The nested pair tag cell immediately following the counter base and both label-count
intervals. -/
def address (pub : Fin 11 → Word w) := pub 4 + pub 5 + pub 9

/-- Append the computed tag-cell address as the twelfth public operand of the nested pair
table. -/
def data (pub : Fin 11 → Word w) : Fin 12 → Word w := Fin.snoc pub (address pub)

private def reg (a : Fin r) : Fin (r+2) := a.castAdd 2
private def cache (r : ℕ) : Fin (r+2) := (0 : Fin 2).natAdd r
private def tmp (r : ℕ) : Fin (r+2) := (1 : Fin 2).natAdd r
private def pre (p : ℕ) (i : Fin 5) : Fin (5+p) := i.castAdd p
private def body (i : Fin p) : Fin (5+p) := i.natAdd 5

private def operand (dst : Fin r) (j : Fin p) : Fin 12 → Instr w (5+p) (r+2) 11 :=
  Fin.lastCases (.copy (reg dst) (cache r) (body j)) (fun i => .publicWord (reg dst) i (body j))

private def lower : Instr w p r 12 → Instr w (5+p) (r+2) 11
  | .constant a v j => .constant (reg a) v (body j)
  | .publicWord a i j => operand a j i
  | .stateWord a j => .stateWord (reg a) (body j)
  | .copy a b j => .copy (reg a) (reg b) (body j)
  | .binary op a b c j => .binary op (reg a) (reg b) (reg c) (body j)
  | .loadPrivate a b j => .loadPrivate (reg a) (reg b) (body j)
  | .storePrivate a b j => .storePrivate (reg a) (reg b) (body j)
  | .jumpEq a b y n => .jumpEq (reg a) (reg b) (body y) (body n)
  | .jumpLt a b y n => .jumpLt (reg a) (reg b) (body y) (body n)
  | .choose y n => .choose (body y) (body n)
  | .readExternal a b j => .readExternal (reg a) (reg b) (body j)
  | .writeExternal a b j => .writeExternal (reg a) (reg b) (body j)
  | .returnState a => .returnState (reg a)
  | .accept => .accept
  | .reject => .reject

private def bootCode (entry : Fin p) : Fin 5 → Instr w (5+p) (r+2) 11
  | 0 => .publicWord (cache r) 4 (pre p 1)
  | 1 => .publicWord (tmp r) 5 (pre p 2)
  | 2 => .binary .add (cache r) (cache r) (tmp r) (pre p 3)
  | 3 => .publicWord (tmp r) 9 (pre p 4)
  | _ => .binary .add (cache r) (cache r) (tmp r) (body entry)

/-- Compile a twelve-operand linked table to the eleven-operand pair interface by computing its
tag address in five entry instructions. -/
def compile (T : Template p r 12) : Template (5+p) (r+2) 11 where
  literalWidth := T.literalWidth
  entry := pre p 0
  code := Fin.addCases (bootCode T.entry) (fun j => lower (T.code j))

private def registers (rs : Fin r → Word w) (a t : Word w) : Fin (r+2) → Word w := Fin.append rs ![a,t]

private def embed (pub : Fin 11 → Word w) (c : Config w p r) : Config w (5+p) (r+2) :=
  ⟨body c.pc,c.persistent,registers c.reg (address pub) (pub 9),c.privateMem⟩

private theorem registers_reg (rs : Fin r → Word w) (a t : Word w) (i : Fin r) :
    registers rs a t (reg i) = rs i := by simp [registers,reg]

private theorem update_reg (rs : Fin r → Word w) (a t v : Word w) (i : Fin r) :
    Function.update (registers rs a t) (reg i) v = registers (Function.update rs i v) a t := by
  funext j
  cases j using Fin.addCases with
  | left j =>
    by_cases h : j = i
    · subst j; simp [registers,reg]
    · simp [registers,reg,Function.update,h]
  | right j =>
    have h : j.natAdd r ≠ i.castAdd 2 := by intro he; have hv := congrArg Fin.val he; simp at hv; omega
    simp [registers,reg,Function.update_of_ne h]

private theorem lower_resize {v : ℕ} (op : Instr v p r 12) : (lower op).resize w = lower (op.resize w) := by
  cases op with
  | publicWord a i j => cases i using Fin.lastCases <;> simp only [lower,operand,Fin.lastCases_last,Fin.lastCases_castSucc,Instr.resize]
  | _ => rfl

private theorem code_body (T : Template p r 12) (pub : Fin 11 → Word w) (j : Fin p) :
    ((compile T).instantiate w pub).code (body j) = lower ((T.instantiate w (data pub)).code j) := by
  simp [compile,Template.instantiate,body,Fin.addCases_right,lower_resize]

private def mapAction {A B : Type*} (f : A → B) : CallAction w A → CallAction w B
  | .localStep c => .localStep (f c)
  | .branch g => .branch (f ∘ g)
  | .read a g => .read a (f ∘ g)
  | .write a v c => .write a v (f c)
  | .finish s => .finish s
  | .reject => .reject

private theorem body_step (T : Template p r 12) (pub : Fin 11 → Word w) (c : Config w p r) :
    ((compile T).instantiate w pub).program.step (embed pub c) =
      mapAction (embed pub) ((T.instantiate w (data pub)).program.step c) := by
  change (((compile T).instantiate w pub).code (body c.pc)).run pub _ = _
  rw [code_body]
  change (lower _).run pub _ = mapAction _ (((T.instantiate w (data pub)).code c.pc).run (data pub) c)
  generalize (T.instantiate w (data pub)).code c.pc = op
  cases op with
  | publicWord a i j =>
    cases i using Fin.lastCases <;>
      simp only [lower,operand,Fin.lastCases_last,Fin.lastCases_castSucc,Instr.run,mapAction,embed,Config.put,
        data,Fin.snoc_last,Fin.snoc_castSucc,update_reg]
    · congr 2; simp [cache,registers]
  | _ =>
    simp only [lower,Instr.run,mapAction,embed,Config.put,Config.store,registers_reg,update_reg,Function.comp_def]
    all_goals first | rfl | (congr 1; simp [registers,apply_ite body])

private theorem body_execute (T : Template p r 12) (pub : Fin 11 → Word w) (fuel : ℕ)
    (c : Config w p r) (m : Memory w) (bs : List Bool) :
    execute ((compile T).instantiate w pub).program fuel (embed pub c) m bs =
      execute (T.instantiate w (data pub)).program fuel c m bs := by
  induction fuel generalizing c m bs with
  | zero => rfl
  | succ f ih =>
    rw [execute,body_step,execute]
    cases hs : (T.instantiate w (data pub)).program.step c <;> simp only [mapAction,Function.comp_apply]
    all_goals first | rfl | rw [ih] | (cases bs <;> simp [ih])

private theorem code_pre (T : Template p r 12) (pub : Fin 11 → Word w) (i : Fin 5) :
    ((compile T).instantiate w pub).code (pre p i) = bootCode T.entry i := by
  simp only [compile,Template.instantiate,pre,Fin.addCases_left]
  fin_cases i <;> rfl

private theorem cache_ne_tmp : cache r ≠ tmp r := by
  intro e; have h := congrArg Fin.val e; simp [cache,tmp] at h

private theorem boot_regs (a b c : Word w) :
    Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => 0) (cache r) a) (tmp r) b)
      (cache r) (a+b)) (tmp r) c) (cache r) (a+b+c) = registers (fun _ : Fin r => 0) (a+b+c) c := by
  funext j
  cases j using Fin.addCases with
  | left j =>
    have ne (i : Fin 2) : j.castAdd 2 ≠ i.natAdd r := by intro h; have hv := congrArg Fin.val h; simp at hv; omega
    simp [Function.update_of_ne (ne _),cache,tmp,registers]
  | right j =>
    fin_cases j <;> simp [cache,tmp,registers,Function.update,Fin.natAdd_inj]

/-- Five deterministic ticks recover the extra operand. The original report,
including every continuing word, external access and binary choice, is then
returned exactly, at every runtime width and remaining fuel. -/
theorem execute_start (T : Template p r 12) (pub : Fin 11 → Word w) (fuel : ℕ)
    (st : Word w) (m : Memory w) (bs : List Bool) :
    let P := ((compile T).instantiate w pub).program
    let S := (T.instantiate w (data pub)).program
    execute P (fuel+5) (P.start st) m bs =
      (execute S fuel (S.start st) m bs).map (LiveStageLink.prependLog (List.replicate 5 .tick)) := by
  dsimp only
  change execute ((compile T).instantiate w pub).program (fuel+5) ⟨pre p 0,st,fun _ => 0,fun _ => 0⟩ m bs = _
  simp only [execute, Machine.program,code_pre,bootCode,Instr.run,Config.put,Function.update_self,
    Function.update_of_ne cache_ne_tmp,BinaryOp.eval,boot_regs]
  let P := ((compile T).instantiate w pub).program
  let S := (T.instantiate w (data pub)).program
  let tick := Report.prepend (Event.tick : Event w)
  change (((((execute P fuel (embed pub (S.start st)) m bs).map tick).map tick).map tick).map tick).map tick =
    (execute S fuel (S.start st) m bs).map (LiveStageLink.prependLog (List.replicate 5 .tick))
  rw [body_execute T pub fuel (S.start st) m bs]
  cases execute S fuel (S.start st) m bs <;> rfl

end LiveProgram.PairTag

end VPVNP
end Computability
end OAI
