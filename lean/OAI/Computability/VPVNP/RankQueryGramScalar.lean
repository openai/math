import OAI.Computability.VPVNP.RankQueryGramRead
import OAI.Computability.VPVNP.RankQueryStackPhysical
import OAI.Computability.VPVNP.RankQueryTagRouter
import OAI.Computability.VPVNP.SliceArithmeticConstant
import OAI.Computability.VPVNP.SliceArithmeticNeg

/-! # The signed Gram-entry call of the physical Schur interpreter

The binary program first computes the Gram column from the degree. It tests
the emitted tag, writes zero or invokes the two Macaulay reads, and applies
packed-field negation when the enclosing Schur factor supplies a minus sign.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.GramScalar

open RAMTape BurstRAM Dispatch Engine
open SliceArithmetic (Vector)
open SliceArithmeticRound (packed)

/-- Word-machine ports for Gram dispatch, with `14 + Dispatch.capacity` registers and zero
public input words. -/
abbrev Small := ISA.Port (14+Dispatch.capacity) 0
/-- The width-`w` register file for Gram dispatch, holding the eight inputs, six descriptor
outputs and compiler scratch registers. -/
abbrev Registers (w : ℕ) := Regs (14+Dispatch.capacity) w

/-- Stack addresses for Gram descriptor words, multiplication, negation, literal-writing
scratch and the supplied matrix-entry reader. -/
inductive Port (K : Type) where
  | words (i : Small) | mul (i : SliceArithmetic.MultiplyCall.Port)
  | neg (i : SliceArithmeticStreamRow.Port Unit) | tmp | extra | aux (k : K)
  deriving DecidableEq, Fintype

variable {K : Type}

/-- Word-stack address of the `i`th Gram descriptor output register. -/
def outWord (i : Fin 6) : Port K := .words (.reg (Code.outReg capacity i))

/-- Wire the two row inputs and common column of a Gram read to output words one, two and
three, and route its multiplier and reader ports to their banks. -/
def reads : GramRead.Port K → Port K
  | .first => outWord 1 | .second => outWord 2 | .column => outWord 3
  | .arithmetic x => .mul x | .aux k => .aux k

theorem reads_injective : Function.Injective (reads (K := K)) := by
  intro a b h; cases a <;> cases b <;> simp_all [reads,outWord,Code.outReg,Fin.ext_iff]

/-- Wire field negation to its own row-arithmetic workspace and the multiplier's shared
external field stacks, including the accumulator. -/
def negPorts : SliceArithmetic.AddCall.Port → Port K
  | .inl x => .neg x | .inr x => .mul (.inr x)

theorem negPorts_injective : Function.Injective (negPorts (K := K)) := by
  rintro (x|x) (y|y) h <;> simp_all [negPorts]

/-- Wire the literal writer to the packed coefficient advice and product accumulator, using
`extra` and `tmp` for its work stacks. -/
def literalPorts : TapeWord.ScanPort → Port K
  | .left => .mul (.inr .coeff) | .out => .mul (.inr .acc) | .right => .extra | .tmp => .tmp

theorem literalPorts_injective : Function.Injective (literalPorts (K := K)) := by
  intro a b h; cases a <;> cases b <;> simp_all [literalPorts]

/-- For descriptor tag one, read and multiply the two entries in the designated column. For
every other tag, write the packed zero scalar. -/
def branch (read : FiniteRoutine (MacaulayRead.Port K)) (tag : ℕ) : FiniteRoutine (Port K) :=
  if tag = 1 then (GramRead.machine read).onPorts reads
  else (SliceArithmeticConstant.machine false).onPorts literalPorts

/-- Negate the field accumulator when the Schur descriptor requests a minus sign and return it
as supplied otherwise. -/
def sign (neg : Bool) : FiniteRoutine (Port K) :=
  if neg then SliceArithmetic.NegCall.machine.onPorts negPorts else .ret

/-- Decode the column for a weighted Gram coefficient, compute its two-entry product or zero
according to the tag, and apply the requested sign. -/
def machine (read : FiniteRoutine (MacaulayRead.Port K)) (neg : Bool) : FiniteRoutine (Port K) :=
  ((Operation.gram.machine.onPorts Port.words).followedBy
    (TagRouter.select (outWord 0) 1 (branch read))).followedBy (sign neg)

/-- Assemble the signed coefficient call's word, multiplication and reader banks with empty
negation and literal-writing work stacks. -/
def bank (words : Stacks Small) (arith : Stacks SliceArithmetic.MultiplyCall.Port) (aux : Stacks K) :
    Stacks (Port K)
  | .words z => words z | .mul z => arith z | .aux z => aux z | _ => []

/-- Initialize the Gram dispatch word stacks from the persistent word and registers, with an
empty write log and zero public inputs. -/
abbrev wordBank {w : ℕ} (persist : Word w) (rs : Registers w) : Stacks Small := ISA.bank Fin.elim0 persist rs []

variable [DecidableEq K] {p e n m w v B d : ℕ} [Fact p.Prime] [NeZero e] {c : Vector p e}

theorem raw_word (x : Word w) : wordBits x = UniversalCountStack.digits w x.val := by
  unfold UniversalCountStack.digits
  rw [show (Fin.ofNat (2^w) x.val) = x by apply Fin.ext; exact Nat.mod_eq_of_lt x.isLt]

theorem zero_runs (hw : SliceArithmetic.Word.workingWidth p ≤ v) (words : Stacks Small) (aux : Stacks K) :
    ((SliceArithmeticConstant.machine false).onPorts literalPorts).Runs (7*(e*v)+3)
      (bank words (GramRead.arithmeticBank v c [] []) aux)
      (bank words (GramRead.arithmeticBank v c [] (scalar v (0 : Scalar c))) aux) := by
  have h := SliceArithmeticConstant.machine_runs (NeZero.pos e) hw false c []
  apply (SliceArithmeticConstant.machine false).runs_onPorts_framed literalPorts_injective (by simpa using h)
  · intro k; cases k <;> rfl
  · intro k; cases k <;> first | rfl | (change packed v (List.ofFn (Scalar.pack c (SliceArithmetic.zero p e)).digits) = _; rw [Scalar.digits_pack]; rfl)
  · intro z hz; cases z with
    | mul x => rcases x with x|x
               · rfl
               · cases x <;> first | rfl | exact (hz .out rfl).elim
    | _ => rfl

omit [NeZero e] in
private theorem negative_digits (x : Scalar c) : (-x).digits = fun i => -x.digits i := by
  change (Scalar.pack c (SliceArithmetic.scale (-1) x.digits)).digits = _
  rw [Scalar.digits_pack]
  funext i; simp [SliceArithmetic.scale]

omit [NeZero e] in
theorem sign_runs (hw : SliceArithmetic.Word.workingWidth p ≤ v) (neg : Bool) (a : Scalar c)
    (words : Stacks Small) (aux : Stacks K) :
    ∃ t ≤ 5*(e*v)+2+SliceArithmetic.AddCall.callCap e v+1,
      (sign neg).Runs t (bank words (GramRead.arithmeticBank v c [] (scalar v a)) aux)
        (bank words (GramRead.arithmeticBank v c [] (scalar v (if neg then -a else a))) aux) := by
  cases neg with
  | false => exact ⟨1, by omega, Routine.runs_ret _⟩
  | true =>
    obtain ⟨t,ht,h⟩ := SliceArithmetic.NegCall.machine_runs hw a.digits (packed v (List.ofFn c))
    refine ⟨t,by omega,?_⟩
    apply SliceArithmetic.NegCall.machine.runs_onPorts_framed negPorts_injective h
    · rintro (k|k) <;> rfl
    · rintro (k|k)
      · rfl
      · cases k <;> first | rfl | (change scalar v (-a) = _; simp only [scalar,negative_digits]; rfl)
    · intro k hk
      cases k with
      | mul z => rcases z with z|z
                 · rfl
                 · exact (hk (.inr z) rfl).elim
      | _ => rfl

/-- Time bound for Gram index dispatch, two entry reads of at most `B` steps each, the product
or zero branch and the optional field negation. -/
def clock (w v e B : ℕ) := Operation.gram.clock w + 2 +
  (2*B + SliceArithmetic.MultiplyCall.callCap e v + 7*(e*v)+3) +
  (5*(e*v)+2+SliceArithmetic.AddCall.callCap e v+1)

theorem machine_runs (read : FiniteRoutine (MacaulayRead.Port K)) (M : Matrix (Fin n) (Fin m) (Scalar c))
    {ready : Stacks K → Prop} (hc : MacaulayRead.Correct read M w v B ready)
    (hw : SliceArithmetic.Word.workingWidth p ≤ v) (hw₁ : 1 ≤ w) (hp : (d+1)*widthFactor ≤ w)
    (i j : Fin n) (z : ℕ) (neg : Bool) (persist : Word w) (rs : Registers w)
    (he : ∀ a, gramInput i j z m a < 2^d) (hr : ∀ a, (rs (Code.inReg capacity a)).val = gramInput i j z m a)
    (aux : Stacks K) (hs : ready aux) :
    ∃ t ≤ clock w v e B, ∃ rs' aux', ready aux' ∧
      (∀ a, rs' (Code.inReg capacity a) = rs (Code.inReg capacity a)) ∧ (machine read neg).Runs t
      (bank (wordBank persist rs) (GramRead.arithmeticBank v c [] []) aux)
      (bank (wordBank persist rs') (GramRead.arithmeticBank v c []
        (scalar v (if neg then -weightedGramEntryCoeff M i j z else weightedGramEntryCoeff M i j z))) aux') := by
  obtain ⟨t₀,ht₀,regs,h₀,hkeep,hout⟩ := Operation.gram.run _ rs hp he hr Fin.elim0 persist
  let rb := wordBank persist regs
  have load : (Operation.gram.machine.onPorts (Port.words (K := K))).Runs t₀
      (bank (wordBank persist rs) (GramRead.arithmeticBank v c [] []) aux)
      (bank rb (GramRead.arithmeticBank v c [] []) aux) := by
    apply Operation.gram.machine.runs_onPorts_framed (fun _ _ h => Port.words.inj h) h₀
    · intro k; rfl
    · intro k; rfl
    · intro k hk; cases k <;> first | rfl | exact (hk _ rfl).elim
  have words (a : Fin 6) : rb (.reg (Code.outReg capacity a)) =
      UniversalCountStack.digits w (Operation.gram.tree.eval (gramInput i j z m) a) := by
    change wordBits (regs _) = _
    rw [raw_word, hout]
  simp only [gram_words] at words
  by_cases hvalid : i.val+2 ≤ z ∧ z-i.val-2 < m
  · simp only [hvalid] at words
    let k : Fin m := ⟨z-i.val-2,hvalid.2⟩
    let x := M i k * M j k
    obtain ⟨t₁,ht₁,s₁,hs₁,h₁⟩ := GramRead.machine_runs read M hc hw i j k aux hs
    have run : (branch read 1).Runs t₁
        (bank rb (GramRead.arithmeticBank v c [] []) aux)
        (bank rb (GramRead.arithmeticBank v c [] (scalar v x)) s₁) := by
      change ((GramRead.machine read).onPorts reads).Runs _ _ _
      apply (GramRead.machine read).runs_onPorts_framed reads_injective h₁
      · intro a; cases a <;> first | rfl | exact words _
      · intro a; cases a <;> first | rfl | exact words _
      · intro a ha; cases a with
        | mul x => exact (ha (.arithmetic x) rfl).elim
        | aux x => exact (ha (.aux x) rfl).elim
        | _ => rfl
    have selected := TagRouter.digits_runs (outWord 0) (branch read) hw₁ (by decide : 1 < 2^1) _ _ (words 0) run
    obtain ⟨t₂,ht₂,h₂⟩ := sign_runs hw neg x rb s₁
    refine ⟨t₀+(2*1+t₁)+t₂,by unfold clock; omega,regs,s₁,hs₁,hkeep,?_⟩
    have hx : weightedGramEntryCoeff M i j z = x := by simp [weightedGramEntryCoeff,hvalid.1,hvalid.2,k,x]
    rw [hx]
    exact (load.followedBy selected).followedBy h₂
  · simp only [hvalid,ite_false] at words
    have hzero := zero_runs (c := c) hw rb aux
    have selected := TagRouter.digits_runs (outWord 0) (branch read) hw₁ (by decide : 0 < 2^1) _ _ (words 0) hzero
    obtain ⟨t₂,ht₂,h₂⟩ := sign_runs hw neg (0 : Scalar c) rb aux
    refine ⟨t₀+(2*1+(7*(e*v)+3))+t₂,by unfold clock; omega,regs,aux,hs,hkeep,?_⟩
    have hx : weightedGramEntryCoeff M i j z = 0 := by
      simp [weightedGramEntryCoeff,hvalid]
    rw [hx]
    exact (load.followedBy selected).followedBy h₂

end RankQuery.Stack.GramScalar

end VPVNP
end Computability
end OAI
