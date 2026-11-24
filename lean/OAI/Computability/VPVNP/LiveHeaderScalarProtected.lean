import OAI.Computability.VPVNP.LiveHeaderScalarStages

/-!
# Protected addresses in arbitrary scalar-stage calls

The structured program text tracks which registers contain addresses read
from designated public slots. Every external write of a scalar header stage
uses such a register. This remains true on malformed memory, regardless of
branch choices or fuel, so the outer dispatch tag below the scratch base is
preserved at every continuing call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM LiveHeaderSchedule
open LiveHeaderDescriptors

namespace WriteAnalysis

variable {w r k : ℕ}

/-- A Boolean mark per register identifying those tracked by the analysis of external write
addresses. -/
abbrev Marks (r : ℕ) := Fin r → Bool

/-- A set register bit certifies that it holds an address different from the
protected cell. Arithmetic and external reads discard this information. -/
def line (slots : Fin k → Bool) (marked : Marks r) : Op r k → Bool × Marks r
  | .publicWord dst slot => (true,Function.update marked dst (slots slot))
  | .copy dst src => (true,Function.update marked dst (marked src))
  | .constant dst _ | .stateWord dst | .binary _ dst _ _ | .read dst _ =>
    (true,Function.update marked dst false)
  | .write addr _ => (marked addr,marked)
  | .guardEq .. | .guardLt .. => (true,marked)

private def merge (a b : Bool × Marks r) : Bool × Marks r :=
  (a.1 && b.1,fun i => a.2 i && b.2 i)

/-- Sequential code passes its output marks to the next instruction. A
branch retains exactly the marks common to its two exits. -/
def analyze (slots : Fin k → Bool) : Flow r k → Marks r → Bool × Marks r
  | .line op, marked => line slots marked op
  | .seq x y, marked =>
    let a := analyze slots x marked
    let b := analyze slots y a.2
    (a.1 && b.1,b.2)
  | .ifEq _ _ x y, marked | .ifLt _ _ x y, marked | .branch x y, marked =>
    merge (analyze slots x marked) (analyze slots y marked)
  | .whileLt .., _ => (false,fun _ => false)

/-- Every marked register's word address differs from the designated protected address. -/
def Valid (addr : ℕ) (marked : Marks r) (rs : Regs w r) :=
  ∀ i, marked i = true → (rs i).val ≠ addr

private theorem valid_put {addr : ℕ} {marked : Marks r} {rs : Regs w r}
    (h : Valid addr marked rs) (dst : Fin r) (bit : Bool) (v : Word w) (hv : bit = true → v.val ≠ addr) :
    Valid addr (Function.update marked dst bit) (Function.update rs dst v) := by
  intro j hj
  by_cases hdst : j = dst
  · subst j; simpa using hv (by simpa using hj)
  · simpa [hdst] using h j (by simpa [hdst] using hj)

private theorem line_sound {pub : Fin k → Word w} {st : Word w} (slots : Fin k → Bool) (addr : ℕ)
    (hslots : ∀ i, slots i = true → (pub i).val ≠ addr) (op : Op r k) {rs rs' : Regs w r}
    {m m' : Memory w} {e : Event w} (hr : op.effect pub st rs m = some (e,rs',m'))
    (mark : Marks r) (valid : Valid addr mark rs) (safe : (line slots mark op).1 = true) :
    Valid addr (line slots mark op).2 rs' ∧ m' addr = m addr := by
  cases op <;> simp only [Op.effect] at hr
  all_goals first | split at hr | skip
  all_goals simp at hr
  all_goals obtain ⟨rfl,rfl,rfl⟩ := hr
  all_goals first
    | exact ⟨valid_put valid _ _ _ (hslots _),rfl⟩
    | exact ⟨valid_put valid _ _ _ (valid _),rfl⟩
    | exact ⟨valid_put valid _ _ _ (by simp),rfl⟩
    | exact ⟨valid,rfl⟩
    | exact ⟨valid,ite_eq_right (Ne.symm (valid _ safe))⟩

private theorem common_left (A B : Bool × Marks r) {addr : ℕ} {rs : Regs w r} (h : Valid addr A.2 rs) :
    Valid addr (merge A B).2 rs := fun j hj => h j (Bool.and_eq_true_iff.mp hj).1

private theorem common_right (A B : Bool × Marks r) {addr : ℕ} {rs : Regs w r} (h : Valid addr B.2 rs) :
    Valid addr (merge A B).2 rs := fun j hj => h j (Bool.and_eq_true_iff.mp hj).2

theorem sound {pub : Fin k → Word w} {st : Word w} {body : Flow r k} {rs rs' : Regs w r} {m m' : Memory w}
    {es : List (Event w)} (exec : Flow.Exec pub st body rs m es rs' m') (slots : Fin k → Bool)
    (addr : ℕ) (hslots : ∀ i, slots i = true → (pub i).val ≠ addr) (marked : Marks r)
    (hvalid : Valid addr marked rs) (safe : (analyze slots body marked).1 = true) :
    Valid addr (analyze slots body marked).2 rs' ∧ m' addr = m addr := by
  induction exec generalizing marked with
  | line hr => exact line_sound slots addr hslots _ hr marked hvalid safe
  | seq _ _ ih₁ ih₂ =>
    have hs := Bool.and_eq_true_iff.mp safe
    obtain ⟨v₁,h₁⟩ := ih₁ marked hvalid hs.1
    obtain ⟨v₂,h₂⟩ := ih₂ _ v₁ hs.2
    exact ⟨v₂,h₂.trans h₁⟩
  | ifEqYes _ _ ih | ifLtYes _ _ ih | branchYes _ ih =>
    have hs := Bool.and_eq_true_iff.mp safe
    obtain ⟨v,h⟩ := ih marked hvalid hs.1
    exact ⟨common_left _ _ v,h⟩
  | ifEqNo _ _ ih | ifLtNo _ _ ih | branchNo _ ih =>
    have hs := Bool.and_eq_true_iff.mp safe
    obtain ⟨v,h⟩ := ih marked hvalid hs.2
    exact ⟨common_right _ _ v,h⟩
  | whileDone | whileStep => exact Bool.noConfusion safe

end WriteAnalysis

/-- The widths, four boundary flags, first-tail flag, mode and eight
descriptors each write into statically designated scalar scratch cells. -/
def scalarStage : Stage → Prop
  | .width _ | .flag _ | .firstTail | .mode | .descriptor .. => True
  | _ => False

private theorem checked_call {w : ℕ} (s : Sizes) (base : ℕ) (stg : Stage) (body : Flow 48 16)
    (hbody : stageTemplate stg = entry (body.template none)) (slots : Fin 16 → Bool)
    (hs : (WriteAnalysis.analyze slots body (fun _ => false)).1 = true)
    (hpub : ∀ i, slots i = true → base ≤ (scalarPub w s base stg i).val)
    (fuel : ℕ) (state : Word w) (m : Memory w) (bits : List Bool) (rep : Report w)
    (hr : let P := ((stageTemplate stg).2.instantiate w (rowData w s base stg)).program
      execute P fuel (P.start state) m bits = some rep) (a : ℕ) (ha : a < base) : after m rep.events a = m a := by
  dsimp only at hr
  rw [hbody,entry_start] at hr
  obtain ⟨out,final,exec,_,_,_⟩ := (Flow.template_execute_iff body none (scalarPub w s base stg)
    state (fun _ => 0) (fun _ => 0) m fuel bits rep).mp hr
  rw [PrimedCounter.Call.exec_memory exec]
  exact (WriteAnalysis.sound exec slots a (fun i hi => (ha.trans_le (hpub i hi)).ne.symm)
    (fun _ => false) (fun _ h => by contradiction) hs).2

private def output4 (i : Fin 16) := decide (i = 4)
private def output3 (i : Fin 16) := decide (i = 3)
private def output78 (i : Fin 16) := decide (i = 7 ∨ i = 8)

theorem scalar_call_frame {w : ℕ} (s : Sizes) (base : ℕ) (stg : Stage) (scalar : scalarStage stg)
    (fit : limit s base ≤ 2^w) (fuel : ℕ) (state : Word w) (m : Memory w) (bits : List Bool) (rep : Report w)
    (run : let P := ((stageTemplate stg).2.instantiate w (rowData w s base stg)).program
      execute P fuel (P.start state) m bits = some rep) (a : ℕ) (ha : a < base) : after m rep.events a = m a := by
  have small {n : ℕ} (h : n ≤ 14) : base ≤ (Fin.ofNat (2^w) (base+n)).val := by
    rw [limit_eq] at fit
    rw [Fin.val_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega
  cases stg with
  | width slot =>
    apply checked_call s base (.width slot) (LiveHeaderWidths.WidthCode.block widthSlots slot) rfl
      output4 (by cases slot <;> rfl) ?_ fuel state m bits rep run a ha
    intro i hi
    obtain rfl : i = 4 := of_decide_eq_true hi
    cases slot <;> apply small <;> decide
  | flag flag =>
    apply checked_call s base (.flag flag) (LiveHeaderWidths.PhaseCode.block widthSlots flag) rfl
      output4 (by cases flag <;> rfl) ?_ fuel state m bits rep run a ha
    intro i hi
    obtain rfl : i = 4 := of_decide_eq_true hi
    cases flag <;> apply small <;> decide
  | firstTail =>
    apply checked_call s base .firstTail (LiveHeaderWidths.PhaseCode.firstTailBlock widthSlots 5) rfl
      output4 rfl ?_ fuel state m bits rep run a ha
    intro i hi
    obtain rfl : i = 4 := of_decide_eq_true hi
    exact small (n := 10) (by decide)
  | mode =>
    apply checked_call s base .mode LiveHeader.Mode.program rfl output3 rfl ?_ fuel state m bits rep run a ha
    intro i hi
    obtain rfl : i = 3 := of_decide_eq_true hi
    exact small (n := 11) (by decide)
  | descriptor side f =>
    apply checked_call s base (.descriptor side f) (Native.block descriptorSlots side f) rfl
      output78 (by cases side <;> cases f <;> rfl) ?_ fuel state m bits rep run a ha
    intro i hi
    rcases (of_decide_eq_true hi : i=7 ∨ i=8) with rfl | rfl
    · exact small (n := 12) (by decide)
    · exact small (n := 13) (by decide)
  | index | advice | primedInit | primedDigits | scan _ _ => exact False.elim scalar

end LiveHeaderProgram

end VPVNP
end Computability
end OAI
