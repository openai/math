import OAI.Computability.VPVNP.RankQueryStackAlias
import OAI.Computability.VPVNP.RankQueryStackCodec

/-!
# Installed Schur descriptor and child routines

The two child routines put a complete typed query in six auxiliary output
registers. They read the loop index from the live continuation frame. The
descriptor routine leaves a zero dummy index in the auxiliary bank.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.EngineAlias

open BurstRAM RAMTape Dispatch Engine

variable {n U Z w p : ℕ} {K : Type}

theorem field_query (tag count acc left : List Bool) (q : SchurKey n U Z) (j : Fin 6) :
    fields w tag q count acc left ⟨j.val+1,by omega⟩ = UniversalCountStack.digits w (q.words j) := by
  fin_cases j <;> rfl

theorem inputs_query (q : SchurKey n U Z) (k : ℕ) (j : Fin 6) :
    inputs q k ⟨j.val,by omega⟩ = q.words j := by fin_cases j <;> rfl

theorem live_fields (q : SchurKey n U Z) (k : ℕ) (tag count acc left : List Bool) (flag : Bool)
    (hcount : flag = true → count = UniversalCountStack.digits w k) :
    LiveInput w flag (fields w tag q count acc left) (inputs q k) := by
  intro i j hi ix he
  have hx : i.val < 6 ∨ flag = true ∧ i.val = 6 := by
    by_contra hh
    simp [liveSlot, hh] at hi
  have hj : j.val = i.val+1 := by
    simp only [liveSlot, dite_eq_left hx] at hi
    exact (congrArg (fun a : Option (Fin 10) => (a.map Fin.val).getD 0) hi).symm
  rcases hx with hl | ⟨hf,hi⟩
  · let s : Fin 6 := ⟨i.val,hl⟩
    have ej : j = ⟨s.val+1,by have := s.isLt; omega⟩ := Fin.ext hj
    have eix : ix = ⟨s.val,by have := s.isLt; omega⟩ := Fin.ext he
    rw [ej,field_query tag count acc left q s,eix,inputs_query]
  · have ej : j = 7 := Fin.ext (by omega)
    have eix : ix = 6 := Fin.ext (by omega)
    rw [ej,eix]
    exact hcount hf

/-- The dispatch bank is ready and its six output registers encode the child query `q`. -/
def Pending (bank : Small ↪ K) (w : ℕ) (q : SchurKey n U Z) (aux : Stacks K) : Prop :=
  Ready bank w n aux ∧ ∀ i, aux (bank (.reg (Code.outReg capacity i))) = UniversalCountStack.digits w (q.words i)

/-- Compute the selected left or right child query using the loop index in the live frame. -/
def stageChild (bank : Small ↪ K) (right : Bool) : FiniteRoutine (Engine.Port K) :=
  routine bank true (if right then .right else .left)

theorem stageChild_runs [DecidableEq K] {F : Type*} [CommRing F] (bank : Small ↪ K) (right : Bool)
    (entry : Entry n F) (q : SchurKey n U Z) (k : ℕ)
    (hvalid : ∃ t, (SchurKey.program entry).describe q = .inr t ∧ k < t)
    (tag acc left : List Bool) (saved : Data) (signal result : List Bool) (aux : Stacks K)
    (hready : Ready bank w n aux) (he : ∀ i, inputs q k i < 2^p)
    (hp : p ≤ w) (hw : (p+1)*widthFactor ≤ w) :
    let live := fields w tag q (UniversalCountStack.digits w k) acc left
    let prog := SchurKey.program entry
    let a := if right then Operation.right else Operation.left
    ∃ s ≤ a.clock w, ∃ out, Pending bank w (if right then prog.right q k else prog.left q k) out ∧
      (stageChild bank right).Runs s (store live saved signal result aux) (store live saved signal result out) ∧
      ∀ j, (∀ i, bank i ≠ j) → out j = aux j := by
  let a := if right then Operation.right else Operation.left
  have ha : a.tree = child right := by cases right <;> rfl
  obtain ⟨s,hs,out,hr,hrun,hout,hother⟩ := run bank true a (inputs q k) _ saved signal result aux hready
    (live_fields q k tag _ acc left true (fun _ => rfl)) (by intro h; contradiction) rfl he hp hw
  refine ⟨s,hs,out,⟨hr,?_⟩,hrun,hother⟩
  obtain ⟨t,ht,hk⟩ := hvalid
  change (q.node entry).describe = .inr t at ht
  cases h : q.node entry with
  | leaf => simp [h,Node.describe] at ht
  | branch T f =>
    have hT : T = t := by simpa [h,Node.describe] using ht
    subst t
    have eq := child_eq entry q h (⟨k,hk⟩ : Fin T) right
    rw [ha] at hout
    intro i
    rw [hout,eq]
    cases right <;> simp only [Bool.false_eq_true, ite_false, ite_true, SchurKey.program, Node.program,
      h, Node.children, dite_eq_left hk]

/-- Compute the current query's descriptor with a zero dummy loop index. -/
def stageDescribe (bank : Small ↪ K) : FiniteRoutine (Engine.Port K) := routine bank false .describe

theorem stageDescribe_runs [DecidableEq K] (bank : Small ↪ K) (q : SchurKey n U Z)
    (saved : Data) (signal result : List Bool) (aux : Stacks K) (hready : Ready bank w n aux)
    (he : ∀ i, inputs q 0 i < 2^p) (hp : p ≤ w) (hw : (p+1)*widthFactor ≤ w) :
    let live := fields w [] q [] [] []
    ∃ s ≤ Operation.describe.clock w, ∃ out, Ready bank w n out ∧
      (stageDescribe bank).Runs s (store live saved signal result aux) (store live saved signal result out) ∧
      (∀ i, out (bank (.reg (Code.outReg capacity i))) =
        UniversalCountStack.digits w (Dispatch.describe.eval (inputs q 0) i)) ∧
      ∀ j, (∀ i, bank i ≠ j) → out j = aux j :=
  run bank false .describe _ _ saved signal result aux hready
    (live_fields q 0 [] [] [] [] false (by intro h; contradiction)) (fun _ => rfl) rfl he hp hw

/-- A single linear bit bound covers every query register and every loop
counter used by either child program. -/
theorem inputs_bounded (s : ℕ) (hn : n ≤ 2^s) (hu : U ≤ 2^s) (hz : Z ≤ 2^s)
    (q : SchurKey n U Z) (k : ℕ) (hk : k ≤ SchurKey.arityBound n U Z) :
    ∀ i, inputs q k i < 2^(2*s+6) := by
  have hc := SchurKey.arityBound_le_exp n U Z s hn hu hz
  have hA : 1 ≤ 2^s := Nat.one_le_pow _ _ (by decide)
  have hs : 2^s ≤ 2^(2*s+4) := Nat.pow_le_pow_right (by decide) (by omega)
  have hbig : 2^(2*s+6) = 2^(2*s+4)*4 := by
    rw [show 2*s+6 = (2*s+4)+2 by omega, pow_add]; rfl
  have hfield (j : Fin 6) : q.words j < 2^(2*s+6) := by
    have hq := q.words_le j
    rw [hbig]
    have hbase : 2^s*16 ≤ 2^(2*s+4) := by
      rw [pow_add]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))
    omega
  intro i
  fin_cases i <;> first | exact hfield _ | change k < _; rw [hbig]; omega | change n < _; rw [hbig]; omega

end RankQuery.Stack.EngineAlias

end VPVNP
end Computability
end OAI
