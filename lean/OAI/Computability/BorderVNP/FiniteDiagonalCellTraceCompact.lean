import OAI.Computability.BorderVNP.FiniteDiagonalCellTraceNative
import OAI.Computability.BorderVNP.FiniteProcessorWeightPrivate
import OAI.Computability.BorderVNP.RoutingISACompactDirectory

/-! # Private choice tapes of the compact sparse cell evaluator

The genuine burst parser, generator and bytecode reversal are deterministic.
The tape compiler preserves every accepted binary choice tape of the emitted
interpreter, with its terminal sign. The inclusive native clock may be odd.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.CellTrace.Compact

open VPVNP RAMTape BurstRAM TeamPrivateTape TeamPrivateValue TeamPrivateFragment
open RoutingISA RoutingISA.CompactMachine CellMacro.Generator CellMacro.StackTape
open private installed bytePort_injective from OAI.Computability.BorderVNP.RoutingISACompactMachine

private theorem leaves_lift {K L Q S : Type} {V : Type*} [DecidableEq K] [DecidableEq L]
    {c : StackCode K Q} {d : StackCode L S} (port : K → L) (hp : Function.Injective port) (label : Q → S)
    (base : Stacks L) (out : S → V) (w : Q → V)
    (hc : ∀ q, d (label q) = (c q).rename port label) (hw : ∀ q, out (label q) = w q)
    (fuel : ℕ) (q : Q) (s : Stacks K) :
    FieldReplay.leaves d out fuel (label q) (installStacks port base s) = FieldReplay.leaves c w fuel q s := by
  induction fuel generalizing q s with
  | zero => rfl
  | succ f ih =>
    rw [FieldReplay.leaves,hc,FieldReplay.leaves]
    cases c q <;> simp only [StackOp.rename,Function.comp_apply,installStacks_at hp,installStacks_update hp,ih,hw]

/-- Extending a stopping clock preserves every consumed tape and terminal output. -/
theorem stableLeaves {K Q : Type} {V : Type*} [DecidableEq K] (C : StackCode K Q)
    (w : Q → V) {small big : ℕ} {q : Q} {s : Stacks K} (halt : StopsWithin C small q s) (le : small ≤ big) :
    FieldReplay.leaves C w big q s = FieldReplay.leaves C w small q s := by
  induction small generalizing big q s with
  | zero => exact halt.elim
  | succ f ih =>
    obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : big ≠ 0)
    have fb : f ≤ b := by omega
    cases h : C q <;> simp only [StopsWithin,h] at halt <;> simp only [FieldReplay.leaves,h]
    case choose => simp only [ih halt.1 fb,ih halt.2 fb]
    all_goals exact ih halt fb

private theorem stableReturn {Q Γ : Type} {V : Type*} {m : ℕ} (P : TapeTable Q Γ m) (blank : Γ)
    (w : FieldSelect.Return Q Γ V m) {small big : ℕ} {q : Q} {s : Fin m → SymbolTape Γ}
    (halt : TapeStops P blank small q s) (le : small ≤ big) (bs : List Bool) :
    FieldSelect.nativeReturn P blank w big q s bs = FieldSelect.nativeReturn P blank w small q s bs := by
  induction small generalizing big q s bs with
  | zero => exact halt.elim
  | succ f ih =>
    obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : big ≠ 0)
    have fb : f ≤ b := by omega
    cases h : P q (fun i => (s i).head) <;> simp only [TapeStops,h] at halt <;> simp only [FieldSelect.nativeReturn,h]
    case one => exact ih halt fb bs
    case two =>
      cases bs with
      | nil => rfl
      | cons bit bs => cases bit <;> first | exact ih halt.1 fb bs | exact ih halt.2 fb bs

private theorem observedSign {Q : Type} {d : ℕ} (T : Table Q d) (f : ℕ) (q : Q) (t : Fin d → Track) (bs : List Bool) :
    (TeamPrivateCall.evaluate T f q t bs).bind Prod.fst =
      FieldProcessor.trackReturn T (fun _ _ neg => neg) f q t bs := by
  induction f generalizing q t bs with
  | zero => rfl
  | succ f ih =>
    cases h : T q (heads t) with
    | halt a sg => cases a <;> cases bs <;> simp [TeamPrivateCall.evaluate,FieldProcessor.trackReturn,h]
    | one => simpa only [TeamPrivateCall.evaluate,FieldProcessor.trackReturn,h] using ih _ _ _
    | two =>
      cases bs with
      | nil => simp only [TeamPrivateCall.evaluate,FieldProcessor.trackReturn,h]; rfl
      | cons b bs => simp only [TeamPrivateCall.evaluate,FieldProcessor.trackReturn,h]; exact ih _ _ _

private theorem returnSigns {K Q : Type} {m : ℕ} (e : K ≃ Fin m) (c : StackCode K Q)
    (neg : Q → Bool) (f : ℕ) (q : Control Q m) (t : Fin m → SymbolTape (Option Bool)) (bs : List Bool) :
    FieldSelect.nativeReturn (table e c neg) none (fun _ _ b => b) f q t bs =
      FieldSelect.nativeReturn (table e c neg) none (terminalOutput neg) f q t bs := by
  induction f generalizing q t bs with
  | zero => rfl
  | succ f ih =>
    cases h : table e c neg q (fun i => (t i).head) with
    | halt a b =>
      have eq : b = terminalOutput neg q (fun i => (t i).head) b := by
        cases q with
        | ready q => cases hc : c q <;> simp [table,hc,terminalOutput] at h ⊢; tauto
        | idle | write => simp [table] at h
      simp only [FieldSelect.nativeReturn,h,← eq]
    | one => simpa only [FieldSelect.nativeReturn,h] using ih _ _ _
    | two =>
      cases bs with
      | nil => simp [FieldSelect.nativeReturn,h]
      | cons => simp only [FieldSelect.nativeReturn,h]; exact ih _ _ _

private noncomputable def signedMacro (gen : Fragment IO) :
    TeamSite.Macro (Control (Label (frontend gen)) (tapeCount gen)) (Option Bool)
      (tapeCount gen) CellDispatch.PrivateCell.symbolWidth where
  alphabet := CellDispatch.PrivateCell.alphabet
  digit := some
  inputTape := tapePorts gen (.inl IO.env)
  table := tapeTable gen
  start := entry gen

private theorem choiceSign {w : ℕ} (gen : Fragment IO) (n : ℕ) (words : List (Word w))
    (bs : List Bool) (sg : Bool) :
    (bs,TeamPrivateCall.sign (some sg)) ∈ choices gen n words ↔
      FieldSelect.nativeReturn (tapeTable gen) none (terminalOutput (negative (frontend gen)))
        (nativeClock n) (entry gen) (input none some (tapePorts gen (.inl IO.env)) (TeamPrivateCall.inputBits words)) bs =
        some sg := by
  let M := signedMacro gen
  let t := input none some (tapePorts gen (.inl IO.env)) (TeamPrivateCall.inputBits words)
  rw [choices,TeamPrivateCall.mem_outcomes_iff]
  have he := FieldProcessor.trackReturn_eq M (fun _ _ b => b) (nativeClock n) (entry gen) t bs
  change FieldProcessor.trackReturn (trackTable CellDispatch.PrivateCell.alphabet (tapeTable gen))
    (fun _ _ b => b) _ _ (inputTracks gen words) bs = FieldSelect.nativeReturn (tapeTable gen) none
    (fun _ _ b => b) _ _ t bs at he
  have hs := returnSigns (tapePorts gen) (program (frontend gen)) (negative (frontend gen)) (nativeClock n) (entry gen) t bs
  change _ ↔ FieldSelect.nativeReturn (tapeTable gen) none (terminalOutput (negative (frontend gen))) _ _ t bs = _
  change FieldSelect.nativeReturn (tapeTable gen) none (fun _ _ b => b) _ _ t bs =
    FieldSelect.nativeReturn (tapeTable gen) none (terminalOutput (negative (frontend gen))) _ _ t bs at hs
  rw [← hs,← he,← observedSign]
  cases hx : TeamPrivateCall.evaluate _ _ _ _ _ with
  | none => simp
  | some p => rcases p with ⟨out,u⟩; cases out with
    | none => cases sg <;> simp [TeamPrivateCall.sign]
    | some b => cases b <;> cases sg <;> simp [TeamPrivateCall.sign]

/-- Membership in the real native outcome enumeration, on the compact argument
words, equals membership in the emitted interpreter's dictionary of individual
accepting tapes. No preparatory phase consumes a branch bit. -/
theorem packed_choices_iff {w : ℕ} (gen : Fragment IO) (n : ℕ) (hw : 0 < w)
    (payload : List Bool) (ops : List CellMacro.Op) {genCost : ℕ}
    (compiled : gen.Runs genCost (io payload [] []) (io [] [] (CellMacro.stream ops).reverse))
    (time : 2 * (3*((CompactFrame.pack w payload).length*w) + genCost +
      (2*(CellMacro.stream ops).length+1)+CellMacro.budget ops) ≤ n^25) (bs : List Bool) (sg : Bool) :
    (bs,TeamPrivateCall.sign (some sg)) ∈ choices gen n (CompactFrame.pack w payload) ↔
      (bs,sg) ∈ FieldReplay.leaves CellMacro.code CellMacro.negative (CellMacro.budget ops)
        byteStart (CellMacro.bank (CellMacro.stream ops) [] []) := by
  let words := CompactFrame.pack w payload
  let wire := TeamPrivateCall.inputBits words
  let prep := frontend gen
  obtain ⟨a,ha,parsed⟩ := CompactFrame.decode_packed (src := IO.env) (dst := IO.row) (by decide) hw payload
    (io [] wire []) rfl rfl
  have image : Function.update (Function.update (io [] wire []) IO.env []) IO.row payload = io payload [] [] := by
    funext i; cases i <;> simp [io]
  rw [image] at parsed
  have pre := prefix_run (CompactFrame.decode IO.env IO.row) gen parsed compiled
  have lim : a+(genCost+(2*(CellMacro.stream ops).length+1))+CellMacro.budget ops ≤ stackClock n := by
    unfold stackClock; omega
  let t := input none some (tapePorts gen (.inl IO.env)) wire
  have bank : values (tapePorts gen) t = prep.bank (io [] wire []) := by
    rw [show t = _ from rfl,values_input]
    funext p
    cases p with
    | inl i => cases i <;> simp [Fragment.bank,io]
    | inr j => simp [Fragment.bank]
  have halt := (stack_value prep wire ops pre lim).1
  have stops := (simulation (tapePorts gen) (program prep) (negative prep) (stackClock n)
    (.inl prep.body.body.entry) t).1.2 (bank ▸ halt)
  rw [choiceSign]
  change FieldSelect.nativeReturn (tapeTable gen) none (terminalOutput (negative prep)) (nativeClock n)
    (entry gen) t bs = _ ↔ _
  have clock : 2*stackClock n ≤ nativeClock n := (Nat.mul_div_le ..).trans (Nat.le_succ _)
  change FieldSelect.nativeReturn (table (tapePorts gen) (program prep) (negative prep)) none
    (terminalOutput (negative prep)) (nativeClock n) (.ready (.inl prep.body.body.entry)) t bs = _ ↔ _
  rw [stableReturn _ _ _ stops clock,nativeReturn_iff,bank]
  let cost := a+(genCost+(2*(CellMacro.stream ops).length+1))
  let available := stackClock n - cost
  have remain : CellMacro.budget ops ≤ available := by dsimp [available,cost]; omega
  have run := TeamLink.routine_id pre (program prep) Sum.inl (.inr byteStart) (fun _ => rfl)
  change (bs,sg) ∈ FieldReplay.leaves (program prep) (negative prep) (stackClock n)
    (.inl prep.body.body.entry) (prep.bank (io [] wire [])) ↔ _
  have front := FieldSelect.leaves_segment run (negative prep) available
  change FieldReplay.leaves (program prep) (negative prep) (available+cost) (.inl prep.body.body.entry)
    (prep.bank (io [] wire [])) = FieldReplay.leaves (program prep) (negative prep) available
    (.inr byteStart) (prep.bank (io (CellMacro.stream ops) [] [])) at front
  rw [show stackClock n = available + cost by dsimp [available,cost]; omega,front]
  let store := prep.bank (io (CellMacro.stream ops) [] [])
  have hl := leaves_lift (c := CellMacro.code) (d := program prep) (bytePort prep) (bytePort_injective prep)
    Sum.inr store (negative prep) CellMacro.negative (fun _ => rfl) (fun _ => rfl)
    available byteStart (CellMacro.bank (CellMacro.stream ops) [] [])
  rw [show installStacks (bytePort prep) store (CellMacro.bank (CellMacro.stream ops) [] []) = store
    from installed prep _] at hl
  rw [hl,byteStart,stableLeaves _ _ (CellMacro.execute ops ⟨true,false⟩ [] _ le_rfl).1 remain]

end FiniteDiagonal.CellTrace.Compact

end BorderVNP
end Computability
end OAI
