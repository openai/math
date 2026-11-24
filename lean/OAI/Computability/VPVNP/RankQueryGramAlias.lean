import OAI.Computability.VPVNP.RankQueryGramScalar
import OAI.Computability.VPVNP.RankQueryStackStages
import OAI.Computability.VPVNP.RankQueryDescribeArms

/-! # Installing Gram reads at the Schur engine's actual ports

Three input registers read the Schur output descriptor directly. The Gram
multiplier's accumulator is the engine's return-value port. Both banks keep
their input widths, advice and private-register invariants across calls.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.DescribeAdapter

open BurstRAM RAMTape Dispatch Engine

/-- Auxiliary ports of the descriptor adapter, combining the Schur dispatch word bank with the
signed Gram coefficient and entry-reader ports. -/
abbrev Aux (K : Type) := EngineAlias.Small ⊕ GramScalar.Port K

variable {K : Type}

/-- Embed the Schur dispatch word bank in the left summand of the adapter's auxiliary ports. -/
def leftBank : EngineAlias.Small ↪ Aux K := ⟨Sum.inl,Sum.inl_injective⟩

/-- The Schur dispatch register that holds output word `i` of the six-word descriptor. -/
def outputSlot (i : Fin 6) : EngineAlias.Small := .reg (Code.outReg capacity i)

/-- Place the six descriptor wires in dispatch output registers and take the coefficient,
scratch and extra wires from the Gram bank. -/
def wires : Describe.Wire ↪ Aux K where
  toFun
    | .desc i => .inl (outputSlot i)
    | .coeff => .inr (.mul (.inr .coeff))
    | .scratch => .inr .tmp
    | .extra => .inr .extra
  inj' := by
    intro a b h; cases a <;> cases b <;> simp_all [outputSlot,Code.outReg,Fin.ext_iff]

/-- Identify the aliased Gram inputs by mapping word registers zero through two to descriptor
outputs one through three. Other ports yield `none`. -/
def slot : GramScalar.Port K → Option (Fin 6)
  | .words (.reg i) => if hi : i.val < 3 then some ⟨i.val+1,by omega⟩ else none
  | _ => none

/-- Connect the first three Gram input registers to the Schur descriptor, the product
accumulator to the engine result, and the remaining ports to Gram auxiliary storage. -/
def gramPorts (x : GramScalar.Port K) : Engine.Port (Aux K) :=
  match slot x with
  | some j => .aux (.inl (outputSlot j))
  | none => match x with
    | .mul (.inr .acc) => .result
    | z => .aux (.inr z)

private theorem slot_some {z : GramScalar.Port K} {j : Fin 6} (h : slot z = some j) :
    ∃ i : EngineAlias.Reg, z = .words (.reg i) ∧ i.val < 3 ∧ j.val = i.val+1 := by
  cases z with
  | words z =>
    cases z with
    | reg i => simp only [slot] at h; split_ifs at h with hs; cases h; exact ⟨i,rfl,hs,rfl⟩
    | _ => contradiction
  | _ => contradiction

private theorem plain {x : GramScalar.Port K} (hx : slot x = none) (ha : x ≠ .mul (.inr .acc)) :
    gramPorts x = .aux (.inr x) := by
  unfold gramPorts; rw [hx]
  cases x with
  | mul x => rcases x with x|x
             · rfl
             · cases x <;> first | rfl | exact (ha rfl).elim
  | _ => rfl

private theorem aliased {x : GramScalar.Port K} {j : Fin 6} (h : slot x = some j) :
    gramPorts x = .aux (.inl (outputSlot j)) := by unfold gramPorts; rw [h]

theorem gramPorts_injective : Function.Injective (gramPorts (K := K)) := by
  intro a b he
  cases ha : slot a <;> cases hb : slot b
  · by_cases h₁ : a = .mul (.inr .acc) <;> by_cases h₂ : b = .mul (.inr .acc)
    · exact h₁.trans h₂.symm
    · subst a; rw [plain hb h₂] at he; contradiction
    · subst b; rw [plain ha h₁] at he; contradiction
    · rw [plain ha h₁,plain hb h₂] at he; exact Sum.inr.inj (Engine.Port.aux.inj he)
  · rw [aliased hb] at he
    by_cases hh : a = .mul (.inr .acc)
    · subst a; contradiction
    · rw [plain ha hh] at he; simp at he
  · rw [aliased ha] at he
    by_cases hh : b = .mul (.inr .acc)
    · subst b; contradiction
    · rw [plain hb hh] at he; simp at he
  · rename_i x y
    obtain ⟨i,rfl,_,hi⟩ := slot_some ha
    obtain ⟨j,rfl,_,hj⟩ := slot_some hb
    rw [aliased ha,aliased hb] at he
    have eq := congrArg Fin.val (ISA.Port.reg.inj (Sum.inl.inj (Engine.Port.aux.inj he)))
    simp only [Code.outReg] at eq
    exact congrArg (fun r => GramScalar.Port.words (.reg r)) (Fin.ext (by omega))

variable {w v p e n m : ℕ} {c : SliceArithmetic.Vector p e}

/-- Gram input register three holds the column count `m`, and input registers four through
seven hold zero. -/
def FixedParams (rs : GramScalar.Registers w) (m : ℕ) : Prop :=
  ∀ a : Fin 8, 3 ≤ a.val → (rs (Code.inReg capacity a)).val = gramInput 0 0 0 m a

/-- The Gram bank has the fixed inputs for `m`, a clean multiplier with packed field advice and
empty operands, and an entry-reader bank satisfying `ready`. -/
def RightReady (w v m : ℕ) (c : SliceArithmetic.Vector p e) (ready : Stacks K → Prop)
    (aux : Stacks (Aux K)) : Prop :=
  ∃ (rs : GramScalar.Registers w) (persist : Word w) (localBank : Stacks K),
    FixedParams rs m ∧ ready localBank ∧ ∀ z, aux (.inr z) =
      GramScalar.bank (GramScalar.wordBank persist rs) (GramRead.arithmeticBank v c [] []) localBank z

/-- The Schur dispatch bank is prepared for row count `n` and the Gram bank for column count
`m`, field advice `c` and a ready entry reader. -/
def Ready (w v n m : ℕ) (c : SliceArithmetic.Vector p e) (ready : Stacks K → Prop)
    (aux : Stacks (Aux K)) : Prop := EngineAlias.Ready leftBank w n aux ∧ RightReady w v m c ready aux

theorem clean {ready : Stacks K → Prop} {aux : Stacks (Aux K)} (h : RightReady w v m c ready aux) :
    Describe.Clean wires v c aux := by
  obtain ⟨rs,persist,localBank,_,_,hp⟩ := h
  exact ⟨hp _,hp _,hp _⟩

variable [DecidableEq K] [Fact p.Prime] [NeZero e]

/-- Install the coefficient callback selected by `neg` on the engine's Gram ports so it reads
the descriptor and writes to the result stack. -/
def valueRoutine (call : Bool → FiniteRoutine (GramScalar.Port K)) (neg : Bool) : FiniteRoutine (Engine.Port (Aux K)) :=
  (call neg).onPorts gramPorts

/-- Use the supplied matrix-entry reader to evaluate a weighted Gram coefficient directly into
the engine result, negating it when `neg` is true. -/
def gram (read : FiniteRoutine (MacaulayRead.Port K)) (neg : Bool) : FiniteRoutine (Engine.Port (Aux K)) :=
  valueRoutine (GramScalar.machine read) neg

private theorem digits_val (x : Word w) : UniversalCountStack.digits w x.val = wordBits x := by
  unfold UniversalCountStack.digits
  rw [show Fin.ofNat (2^w) x.val = x by apply Fin.ext; exact Nat.mod_eq_of_lt x.isLt]

/-- Reuse the three Schur output words as the row, column and degree of a
Gram input. The inactive Gram copies of these words stay in the caller. -/
def prepareRegs (base : GramScalar.Registers w) (env : Fin 8 → ℕ) : GramScalar.Registers w :=
  fun a => if h : a.val < 3 then Fin.ofNat _ (env ⟨a.val,by omega⟩) else base a

omit [DecidableEq K] [Fact p.Prime] [NeZero e] in
theorem prepare {d : ℕ} (i j : Fin n) (z : ℕ) (live saved : Data) (aux : Stacks (Aux K))
    (base : GramScalar.Registers w) (persist : Word w) (localBank : Stacks K) (hparams : FixedParams base m)
    (hs : ∀ a, aux (.inr a) = GramScalar.bank (GramScalar.wordBank persist base) (GramRead.arithmeticBank v c [] []) localBank a)
    (hd : d ≤ w) (he : ∀ a, gramInput i j z m a < 2^d)
    (hdesc : ∀ a : Fin 3, aux (.inl (outputSlot ⟨a.val+1,by omega⟩)) =
      UniversalCountStack.digits w (gramInput i j z m ⟨a.val,by omega⟩)) :
    let rs := prepareRegs base (gramInput i j z m)
    (∀ a, (rs (Code.inReg capacity a)).val = gramInput i j z m a) ∧
    ∀ a, store live saved [] [] aux (gramPorts a) =
      GramScalar.bank (GramScalar.wordBank persist rs) (GramRead.arithmeticBank v c [] []) localBank a := by
  let env := gramInput i j z m
  let rs := prepareRegs base env
  have hreg (a : Fin 8) : (rs (Code.inReg capacity a)).val = env a := by
    by_cases ha : a.val < 3
    · change Fin.val (if h : a.val < 3 then Fin.ofNat (2^w) (env ⟨a.val,by omega⟩) else base (Code.inReg capacity a)) = _
      rw [dite_eq_left ha]; exact Nat.mod_eq_of_lt ((he a).trans_le (Nat.pow_le_pow_right (by decide) hd))
    · have hp' := hparams a (by omega)
      change Fin.val (if h : a.val < 3 then Fin.ofNat (2^w) (env ⟨a.val,by omega⟩) else base (Code.inReg capacity a)) = _
      rw [dite_eq_right ha,hp']; fin_cases a <;> first | rfl | contradiction
  refine ⟨hreg,?_⟩
  intro a
  cases hh : slot a with
  | some b =>
    obtain ⟨r,rfl,hlt,hval⟩ := slot_some hh
    let ai : Fin 3 := ⟨r.val,hlt⟩
    let ix : Fin 8 := ⟨r.val,by omega⟩
    rw [aliased hh]
    change aux (.inl (outputSlot b)) = wordBits (rs r)
    rw [show b = ⟨ai.val+1,by omega⟩ from Fin.ext hval,hdesc ai, ← digits_val]
    exact congrArg (UniversalCountStack.digits w) (hreg ix).symm
  | none =>
    by_cases ha : a = .mul (.inr .acc)
    · subst a; rfl
    · rw [plain hh ha]; change aux (.inr a) = _; rw [hs]
      cases a with
      | words a =>
        cases a with
        | reg a =>
          have hn : ¬ a.val < 3 := by intro ha; simp [slot,ha] at hh
          change wordBits (base a) = wordBits (rs a); simp [rs,prepareRegs,hn]
        | _ => rfl
      | _ => rfl

/-- A signed scalar-entry call uses two row indices and a coefficient degree.
Its fixed program and mathematical entry map may come from the weighted
Gram matrix or a constant-polynomial Cramer matrix. -/
def CallRuns (call : Bool → FiniteRoutine (GramScalar.Port K)) (entry : Entry n (Scalar c))
    (w v m d T : ℕ) (ready : Stacks K → Prop) : Prop :=
  ∀ (i j : Fin n) (z : ℕ) (neg : Bool) (persist : Word w) (rs : GramScalar.Registers w),
    (∀ a, gramInput i j z m a < 2^d) → (∀ a, (rs (Code.inReg capacity a)).val = gramInput i j z m a) →
    ∀ s : Stacks K, ready s → ∃ t ≤ T, ∃ rs' out, ready out ∧
      (∀ a, rs' (Code.inReg capacity a) = rs (Code.inReg capacity a)) ∧ (call neg).Runs t
        (GramScalar.bank (GramScalar.wordBank persist rs) (GramRead.arithmeticBank v c [] []) s)
        (GramScalar.bank (GramScalar.wordBank persist rs')
          (GramRead.arithmeticBank v c [] (scalar v (if neg then -entry i j z else entry i j z))) out)

omit [NeZero e] in
theorem value_runs {d T : ℕ} (call : Bool → FiniteRoutine (GramScalar.Port K)) (entry : Entry n (Scalar c))
    {ready : Stacks K → Prop} (hc : CallRuns call entry w v m d T ready)
    (hd : d ≤ w)
    (i j : Fin n) (z : ℕ) (neg : Bool) (live saved : Data) (aux : Stacks (Aux K)) (haux : RightReady w v m c ready aux)
    (he : ∀ a, gramInput i j z m a < 2^d)
    (hdesc : ∀ a : Fin 3, aux (.inl (outputSlot ⟨a.val+1,by omega⟩)) =
      UniversalCountStack.digits w (gramInput i j z m ⟨a.val,by omega⟩)) :
    ∃ t ≤ T, ∃ out, RightReady w v m c ready out ∧
      (∀ x, out (.inl x) = aux (.inl x)) ∧ (valueRoutine call neg).Runs t
      (store live saved [] [] aux) (store live saved []
        (scalar v (if neg then -entry i j z else entry i j z)) out) := by
  obtain ⟨base,persist,localBank,hparams,hlocal,hs⟩ := haux
  let env := gramInput i j z m
  let rs := prepareRegs base env
  obtain ⟨hreg,hin⟩ := prepare i j z live saved aux base persist localBank hparams hs hd he hdesc
  obtain ⟨t,ht,regs,localOut,hlout,hkeep,hcall⟩ :=
    hc i j z neg persist rs he hreg localBank hlocal
  let cleaned : GramScalar.Registers w := fun a => if a.val < 3 then base a else regs a
  let final := Sum.elim (fun x => aux (.inl x)) (GramScalar.bank (GramScalar.wordBank persist cleaned)
    (GramRead.arithmeticBank v c [] []) localOut)
  let result := scalar v (if neg then -entry i j z else entry i j z)
  have hcparams : FixedParams cleaned m := by
    intro a ha
    change Fin.val (if a.val < 3 then base (Code.inReg capacity a) else regs (Code.inReg capacity a)) = _
    rw [ite_eq_right (by omega),hkeep]
    change Fin.val (if h : a.val < 3 then Fin.ofNat (2^w) (env ⟨a.val,by omega⟩) else base (Code.inReg capacity a)) = _
    rw [dite_eq_right (by omega), hparams a ha]
  refine ⟨t,ht,final,⟨cleaned,persist,localOut,hcparams,hlout,fun _ => rfl⟩,fun _ => rfl,?_⟩
  apply (call neg).runs_onPorts_framed gramPorts_injective hcall
  · exact hin
  · intro a
    cases hh : slot a with
    | some b =>
      obtain ⟨r,rfl,hlt,hval⟩ := slot_some hh
      let ai : Fin 3 := ⟨r.val,hlt⟩
      let ix : Fin 8 := ⟨r.val,by omega⟩
      rw [aliased hh]
      change aux (.inl (outputSlot b)) = wordBits (regs r)
      rw [show b = ⟨ai.val+1,by omega⟩ from Fin.ext hval,hdesc ai, ← digits_val]
      exact congrArg (UniversalCountStack.digits w) ((congrArg Fin.val (hkeep ix)).trans (hreg ix)).symm
    | none =>
      by_cases ha : a = .mul (.inr .acc)
      · subst a; rfl
      · rw [plain hh ha]
        cases a with
        | words a =>
          cases a with
          | reg a =>
            have hn : ¬ a.val < 3 := by intro ha; simp [slot,ha] at hh
            change wordBits (cleaned a) = wordBits (regs a); simp [cleaned,hn]
          | _ => rfl
        | mul a => rcases a with a|a
                   · rfl
                   · cases a <;> first | rfl | exact (ha rfl).elim
        | _ => rfl
  · intro a ha
    cases a with
    | frame j => cases j <;> rfl
    | condition => rfl
    | result => exact (ha (.mul (.inr .acc)) rfl).elim
    | aux a =>
      rcases a with a|a
      · rfl
      · cases hh : slot a with
        | some b =>
          obtain ⟨r,rfl,hlt,_⟩ := slot_some hh
          rw [show store live saved [] [] aux (.aux (.inr (.words (.reg r)))) = _ from hs _]
          change wordBits (cleaned r) = wordBits (base r); simp [cleaned,hlt]
        | none =>
          by_cases hh' : a = .mul (.inr .acc)
          · subst a; exact (hs (.mul (.inr .acc))).symm
          · exact (ha a (plain hh hh')).elim

theorem gram_runs {d B : ℕ} (read : FiniteRoutine (MacaulayRead.Port K)) (M : Matrix (Fin n) (Fin m) (Scalar c))
    {ready : Stacks K → Prop} (hc : MacaulayRead.Correct read M w v B ready)
    (hw : SliceArithmetic.Word.workingWidth p ≤ v) (hw₁ : 1 ≤ w) (hp : (d+1)*widthFactor ≤ w) (hd : d ≤ w)
    (i j : Fin n) (z : ℕ) (neg : Bool) (live saved : Data) (aux : Stacks (Aux K)) (haux : RightReady w v m c ready aux)
    (he : ∀ a, gramInput i j z m a < 2^d)
    (hdesc : ∀ a : Fin 3, aux (.inl (outputSlot ⟨a.val+1,by omega⟩)) =
      UniversalCountStack.digits w (gramInput i j z m ⟨a.val,by omega⟩)) :
    ∃ t ≤ GramScalar.clock w v e B, ∃ out, RightReady w v m c ready out ∧
      (∀ x, out (.inl x) = aux (.inl x)) ∧ (gram read neg).Runs t
      (store live saved [] [] aux) (store live saved []
        (scalar v (if neg then -weightedGramEntryCoeff M i j z else weightedGramEntryCoeff M i j z)) out) :=
  value_runs (GramScalar.machine read) (weightedGramEntryCoeff M)
    (GramScalar.machine_runs read M hc hw hw₁ hp) hd i j z neg live saved aux haux he hdesc

end RankQuery.Stack.DescribeAdapter

end VPVNP
end Computability
end OAI
