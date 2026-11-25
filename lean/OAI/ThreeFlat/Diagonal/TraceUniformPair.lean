import OAI.ThreeFlat.Diagonal.TraceUniformCircuit
import OAI.ThreeFlat.Diagonal.TracePairCorrect

namespace OAI
/-! # Uniform native instruction dispatch from the physical program text -/

namespace ThreeFlat.Diagonal.TraceProgram

open RAM TraceWords TraceIssue TracePair TraceDecodeShape TraceRows TraceBanks
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {w p r k : ℕ}

theorem candidateCircuit_correct (h : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (data : Memory w) (x y : Record w p r) (i : Fin p) (z : Instr 0 p r k) :
    (candidateCircuit i z).2.eval (Sum.elim (packed h hp x y) (contents data)) = true ↔
      pair (exposed (native data i z)) x y := by
  rw [candidateCircuit_eval, pairCircuit_correct]

/-- The fully decoded machine for a successful header. -/
def machine (data : Memory w) (entry : Fin p) : Machine w p r k :=
  ⟨entry,fun i => (decodeRow w p r k (fetchRow data i.val)).getD .reject,publicValues (p:=p) data⟩

theorem readProgram_machine {data : Memory w} {M : Machine w p r k}
    (h : readProgram w p r k data = some M) : M = machine data M.entry := by
  unfold readProgram at h
  cases he : bounded p (data 0).val with
  | none => simp [he] at h
  | some e =>
    simp [he] at h
    subst M
    rfl

private theorem pair_step {s : CPU w p r} {x y : Record w p r}
    (hx : before x = some s) (P Q : Program (w+1) (CPU w p r)) (h : P.step s = Q.step s) :
    pair P x y ↔ pair Q x y := by
  cases x with
  | move c e => have hc : c = s := Option.some.inj hx; subst c; simp only [pair, h]
  | halt c out => have hc : c = s := Option.some.inj hx; subst c; simp only [pair, h]
  | pad => contradiction

private theorem pair_reject {s : CPU w p r} {x y : Record w p r}
    (hx : before x = some s) (P : Program (w+1) (CPU w p r)) (h : P.step s = .reject) :
    ¬ pair P x y := by
  cases x with
  | move c e =>
    have hc : c = s := Option.some.inj hx
    subst c
    cases e <;> simp [pair, h, next?]
  | halt c out => have hc : c = s := Option.some.inj hx; subst c; simp [pair, h]
  | pad => contradiction

private theorem decode_literal {data : Memory w} {i : Fin p} {ins : Instr w p r k}
    (hi : decodeRow w p r k (fetchRow data i.val) = some ins) :
    instantiate (erase ins) (literalAt data i) = ins := by
  have hw : (fetchRow data i.val).b < 2^w := (literalAt data i).isLt
  have he := Option.some.inj ((decode_of_matches hw (erase ins) (matches_erase_of_decode hi)).symm.trans hi)
  have hv : (Fin.ofNat (2^w) (fetchRow data i.val).b : Word w) = literalAt data i :=
    Fin.ext (Nat.mod_eq_of_lt hw)
  rwa [hv] at he

private theorem slot_correct (h : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (data : Memory w)
    (entry : Fin p) (x y : Record w p r) (s : CPU w p r) (hx : before x = some s) :
    (slot (k:=k) s.pc).eval (fun a => (source a).2.eval (Sum.elim (packed h hp x y) (contents data))) = true ↔
      pair (exposed (machine (k:=k) data entry)) x y := by
  rw [slot,selectSlot_true _ _ _ data s.pc (fun _ _ => rfl)]
  cases hi : decodeRow w p r k (fetchRow data s.pc.val) with
  | none =>
    have hs : (exposed (machine (k:=k) data entry)).step s = .reject := by simp [exposed,machine,hi,step]
    simp [pair_reject hx _ hs]
  | some ins =>
    have hs : (exposed (native data s.pc (erase ins))).step s = (exposed (machine (k:=k) data entry)).step s := by
      simp [exposed,native,single,machine,hi,decode_literal hi]
    simpa [hi,Expr.eval,source,candidateCircuit_correct] using pair_step hx _ _ hs (y:=y)

/-- The circuit depends only on the public widths. Its input supplies both
serialized rows and every bit of the program text and public-operand table. -/
theorem uniformPair_correct (h : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (data : Memory w)
    (entry : Fin p) (x y : Record w p r) :
    (uniformPair (w:=w) (p:=p) (r:=r) (k:=k)).2.eval (Sum.elim (packed h hp x y) (contents data)) = true ↔
      pair (exposed (machine (k:=k) data entry)) x y := by
  let v := fun a : Control w p r k => (source a).2.eval (Sum.elim (packed h hp x y) (contents data))
  have hr (e : Expr (Raw w r)) : (rowControl e).eval v = e.eval (packed h hp x y) := by
    simp [rowControl,v,source]
  have active (s : CPU w p r) (hx : before x = some s) :
      (TraceFetch.fetch (fun i => rowControl (pcIs false i)) slot).eval v = true ↔
        pair (exposed (machine (k:=k) data entry)) x y := by
    rw [TraceFetch.fetch_eval _ _ _ s.pc (fun i => (hr _).trans (pc_active h hp x y false i s hx))]
    exact slot_correct h hp data entry x y s hx
  simp only [uniformPair,TraceCompose.substituteFintype_eval,formulaPacket_eval]
  change control.eval v = true ↔ _
  simp only [control,Expr.eval_mux,hr,tagIs_pad]
  cases x with
  | pad => simp [pair]
  | move s e => simpa using active s rfl
  | halt s out => simpa using active s rfl

theorem uniformPair_readProgram (h : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) {data : Memory w} {M : Machine w p r k}
    (hd : readProgram w p r k data = some M) (x y : Record w p r) :
    (uniformPair (w:=w) (p:=p) (r:=r) (k:=k)).2.eval (Sum.elim (packed h hp x y) (contents data)) = true ↔ pair (exposed M) x y := by
  rw [uniformPair_correct h hp data M.entry, ← readProgram_machine hd]

end ThreeFlat.Diagonal.TraceProgram

end OAI
