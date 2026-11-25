import OAI.Computability.VPVNP.LiveHeaderBits
import OAI.ThreeFlat.Diagonal.TraceAdjacent
import OAI.ThreeFlat.Diagonal.TracePairInputs

namespace OAI
/-! # Reading instruction operands and selectors from the physical word fields -/

namespace ThreeFlat.Diagonal.TracePair

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM TraceBanks TraceRows TraceWords TraceIssue
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {w p r k : ℕ}

abbrev CPU w p r := Snapshot w p r
abbrev Record (w p r : ℕ) := Row (w+1) (Snapshot w p r)
abbrev StepResult (w p r : ℕ) := Proposal (w+1) (Snapshot w p r)

def current (s : CPU w p r) : StepResult w p r → Record w p r
  | .move e _ => .move s e
  | .halt out => .halt s out

def nextMatches (y : Record w p r) : StepResult w p r → Prop
  | .move _ after => before y = some after
  | .halt _ => True

def packed (h : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (x y : Record w p r) (z : Raw w r) : Bool :=
  bits ((rowFormat h hp).words (if z.1 then y else x) z.2.1) z.2.2

theorem packed_encode (h : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (x y : Record w p r)
    (side : Bool) (i : Fin (5+r)) (j : Fin (w+1)) :
    packed h hp x y (side,i,j) =
      (rowFormat h hp).encode (if side then y else x) (finProdFinEquiv (i,j)) := by
  unfold packed Computability.VPVNP.RAMSerialization.Format.encode
  rw [Computability.VPVNP.RAMSerialization.arrayBits_at]
  exact Computability.VPVNP.LiveHeader.testBit_wordBits _ _

private theorem current_header (h : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (s : CPU w p r) (q : StepResult w p r) :
    header h hp (current s q) = ![tagWord h (tagNumber q.tag), pcWord hp s.pc, wide s.persistent,
      q.address, q.data] := by
  cases q with
  | halt out => cases out <;> rfl
  | move e z => cases e with
    | tick | read | write => rfl
    | choice b => cases b <;> rfl

private theorem current_regs (s : CPU w p r) (q : StepResult w p r) :
    regs (current s q) = wide ∘ s.reg := by cases q <;> rfl

private theorem current_before (s : CPU w p r) (q : StepResult w p r) :
    before (current s q) = some s := by cases q <;> rfl

private theorem exists_current {z : Record w p r} {s : CPU w p r} (h : before z = some s) :
    ∃ q : StepResult w p r, z = current s q := by
  cases z with
  | pad => simp [before] at h
  | halt t out =>
    have := Option.some.inj h
    subst t
    exact ⟨.halt out,rfl⟩
  | move t e =>
    have := Option.some.inj h
    subst t
    exact ⟨.move e s,rfl⟩

variable (h : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (x y : Record w p r)

theorem headerWire_eval (side : Bool) (i : Fin 5) (j : Fin (w+1)) :
    ((headerWire (r:=r) side i j).eval (packed h hp x y)) =
      bits (header h hp (if side then y else x) i) j := by
  simp [headerWire, packed, Expr.eval]

theorem registerWire_eval (side : Bool) (a : Fin r) (j : Fin w) :
    (registerWire side a j).eval (packed h hp x y) =
      bits (regs (if side then y else x) a) j.castSucc := by
  simp [registerWire, packed, Expr.eval]

private theorem wordIs_true (side : Bool) (i : Fin 5) (v : Word (w+1)) :
    (wordIs side i v).eval (packed h hp x y) = true ↔
      header h hp (if side then y else x) i = v :=
  sameWord_at _ _ _ (headerWire_eval h hp x y side i) (fun _ => rfl)

theorem reg_active (side : Bool) (a : Fin r) (j : Fin w) (s : CPU w p r)
    (hs : before (if side then y else x) = some s) :
    (registerWire side a j).eval (packed h hp x y) = bits (s.reg a) j := by
  obtain ⟨q,hq⟩ := exists_current hs
  rw [registerWire_eval, hq, current_regs]
  rfl

theorem state_active (side : Bool) (j : Fin w) (s : CPU w p r)
    (hs : before (if side then y else x) = some s) :
    (headerWire side 2 j.castSucc).eval (packed h hp x y) = bits s.persistent j := by
  obtain ⟨q,hq⟩ := exists_current hs
  rw [headerWire_eval, hq, current_header]
  rfl

theorem pc_active (side : Bool) (i : Fin p) (s : CPU w p r)
    (hs : before (if side then y else x) = some s) :
    (pcIs side i).eval (packed h hp x y) = decide (s.pc = i) := by
  obtain ⟨q,hq⟩ := exists_current hs
  apply Bool.eq_iff_iff.mpr
  rw [pcIs, wordIs_true, hq, current_header]
  have hi := i.isLt.trans_le hp
  simp [pcWord, Fin.ext_iff, Nat.mod_eq_of_lt hi]

theorem tag_current (side : Bool) (s : CPU w p r) (q : StepResult w p r) (t : Fin 8)
    (hs : (if side then y else x) = current s q) :
    (tagIs side t).eval (packed h hp x y) = decide (tagNumber q.tag = t) := by
  apply Bool.eq_iff_iff.mpr
  rw [tagIs, wordIs_true, hs, current_header]
  have ht := t.isLt.trans_le (show 8 ≤ 2^(w+1) from Nat.pow_le_pow_right (by decide : 0 < 2) h)
  simp [tagWord, Fin.ext_iff, Nat.mod_eq_of_lt ht]

theorem tagIs_pad (side : Bool) :
    (tagIs side 0).eval (packed h hp x y) = decide ((if side then y else x) = .pad) := by
  generalize he : (if side then y else x) = z
  cases z with
  | pad =>
    change (tagIs side 0).eval (packed h hp x y) = true
    rw [tagIs, wordIs_true, he]
    simp [header]
  | move s e =>
    have hq : (if side then y else x) = current s (.move e s) := he
    rw [tag_current h hp x y side s (.move e s) 0 hq]
    cases e with
    | tick | read | write => rfl
    | choice b => cases b <;> rfl
  | halt s out =>
    rw [tag_current h hp x y side s (.halt out) 0 he]
    cases out <;> rfl

theorem terminal_current (s : CPU w p r) (q : StepResult w p r) :
    terminal.eval (packed h hp (current s q) y) = (match q with | .halt _ => true | .move .. => false) := by
  unfold terminal
  rw [Expr.eval, tag_current h hp (current s q) y false s q 6 rfl,
    tag_current h hp (current s q) y false s q 7 rfl]
  cases q with
  | halt out => cases out <;> rfl
  | move e t => cases e with
    | tick | read | write => rfl
    | choice b => cases b <;> rfl

private theorem next_eval (s : CPU w p r) (q : StepResult w p r) (hy : nextMatches y q)
    (e : Bool → Expr (Raw w r)) (f : CPU w p r → Bool)
    (he : ∀ side z, before (if side then y else current s q) = some z →
      (e side).eval (packed h hp (current s q) y) = f z) :
    (next e).eval (packed h hp (current s q) y) = f (q.after s) := by
  rw [next, Expr.eval_mux, terminal_current]
  cases q with
  | halt out => exact he false s (current_before s (.halt out))
  | move ev t => exact he true t hy

private theorem operandInput_eval (s : CPU w p r) (q : StepResult w p r) (a b : Fin r) :
    (fun i => (operandInput a b i).elim (packed h hp (current s q) y) id) =
      Fin.append (bits (s.reg a)) (bits (s.reg b)) := by
  funext i
  induction i using Fin.addCases with
  | left j =>
    simpa [operandInput, registerWire, Expr.eval] using
      reg_active h hp (current s q) y false a j s (current_before s q)
  | right j =>
    simpa only [operandInput, registerWire, Expr.eval, Fin.addCases_right, Fin.append_right, Sum.elim_inl] using
      reg_active h hp (current s q) y false b j s (current_before s q)

private theorem aluPacket_eval (pub : Fin k → Word w) (s : CPU w p r) (q : StepResult w p r) (i : Instr w p r k) (j : Fin w) :
    (aluPacket pub j i).2.eval (packed h hp (current s q) y) = bits (aluWord pub s i) j := by
  cases i <;> simp [aluPacket, aluWord, Expr.eval, bits, operandInput_eval, TraceBinaryOps.network_correct]

private theorem cmpExpr_eval (s : CPU w p r) (q : StepResult w p r) (i : Instr w p r k) :
    (cmpExpr i).eval (packed h hp (current s q) y) = compareBit s i := by
  have hr (a j) := reg_active h hp (current s q) y false a j s (current_before s q)
  cases i with
  | jumpEq a b yes no =>
    apply Bool.eq_iff_iff.mpr
    simpa [cmpExpr, compareBit] using (sameWord_at _ _ _ (hr a) (hr b))
  | jumpLt a b yes no => exact lessWord_at _ _ _ _ _ (hr a) (hr b)
  | _ => rfl

theorem tagNumber_injective : Function.Injective tagNumber := by
  intro x y
  cases x <;> cases y <;> decide

/-- Every computed local input agrees with the information decoded from an
active row, including the fetched opcode's wrapped arithmetic bits. -/
theorem packet_active (M : Machine w p r k) (s : CPU w p r) (q : StepResult w p r)
    (hy : nextMatches y q) (a : Port w p r) :
    ((packet M (.inl a)).2.eval (packed h hp (current s q) y)) = valuation M s q a := by
  cases a with
  | pc i => exact (formulaPacket_eval ..).trans (pc_active h hp _ y false i s (current_before ..))
  | nextPC i =>
    rw [packet, formulaPacket_eval]
    apply next_eval h hp y s q hy _ (fun t => decide (t.pc = i))
    exact fun b t h => pc_active _ _ _ _ b i t h
  | state j =>
    exact (formulaPacket_eval ..).trans (state_active h hp _ y false j s (current_before ..))
  | nextState j =>
    rw [packet, formulaPacket_eval]
    apply next_eval h hp y s q hy _ (fun t => bits t.persistent j)
    exact fun b t h => state_active _ _ _ _ b j t h
  | reg i j =>
    exact (formulaPacket_eval ..).trans (reg_active h hp _ y false i j s (current_before ..))
  | nextReg i j =>
    rw [packet, formulaPacket_eval]
    apply next_eval h hp y s q hy _ (fun t => bits (t.reg i) j)
    exact fun b t h => reg_active _ _ _ _ b i j t h
  | tag t =>
    rw [packet, formulaPacket_eval, tag_current h hp (current s q) y false s q (tagNumber t) rfl]
    simp [valuation, tagNumber_injective.eq_iff]
  | address j =>
    rw [packet, formulaPacket_eval, headerWire_eval]
    simp [valuation, current_header]
  | data j =>
    rw [packet, formulaPacket_eval, headerWire_eval]
    simp [valuation, current_header]
  | alu i j => exact aluPacket_eval h hp y M.publicData s q (M.code i) j
  | cmp i => exact (formulaPacket_eval ..).trans (cmpExpr_eval h hp y s q (M.code i))

end ThreeFlat.Diagonal.TracePair

end OAI
