import OAI.ThreeFlat.Diagonal.TraceClockFactors
import OAI.ThreeFlat.Diagonal.TraceUniformPair
import OAI.ThreeFlat.Diagonal.TraceRelay

namespace OAI
/-! # Evaluating the universal local checks on a copied program -/

namespace ThreeFlat.Diagonal.TraceUniformRow

open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM RAMSerialization BooleanTranscript
open Computability.VPVNP.VerifierNetwork (Frame)
open TraceBanks TraceWords TraceRows TraceCompose TraceRowPackets TraceProgram
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {F : Type*} [Fintype F] [CommRing F] {w p r k f S d : ℕ}

private abbrev R w p r := Row (w+1) (Snapshot w p r)

private theorem literal_eval {σ : Type*} (b : Bool) (v : σ → Bool) : (literal b).2.eval v=b := rfl

theorem all_header (hw : 2 ≤ w+1) (header : Fin S → Word w) (cpu : CpuBits w r f)
    (z : SortBits d (w+1)) (data : Memory w) :
    (∀ v : Fin (2^d), (programHeader (p:=p) (k:=k) v).2.eval
        (valuation hw v header cpu z (fun _ => contents data)) = true) ↔
      (RAM.readProgram w p r k data).isSome = true := by
  have zero : 0 < 2^d := by positivity
  have atRow (v : Fin (2^d)) (h : v.val = 0) :
      (programHeader (p:=p) (k:=k) v).2.eval (valuation hw v header cpu z (fun _ => contents data)) =
        (RAM.readProgram w p r k data).isSome := by
    unfold programHeader
    rw [packetIf_eval,ite_eq_left h,substituteFintype_eval]
    exact headerCircuit_valid (r:=r) (k:=k) (p:=p) data
  constructor
  · intro h; simpa only [atRow ⟨0,zero⟩ rfl] using h ⟨0,zero⟩
  · intro h v
    by_cases hv : v.val=0
    · simpa only [atRow v hv] using h
    · unfold programHeader
      rw [packetIf_eval,ite_eq_right hv]
      rfl

private theorem joint_packed (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (v : Fin (2^d)) (s : Fin 2)
    (header : Fin S → Word w) (xs : Fin f → R w p r) (z : SortBits d (w+1))
    (ha : S ≤ slotAddress d v s) (data : Memory w) :
    (fun i => (joint s i).2.eval (valuation (by omega) v header (writeCpu hw hp xs) z (fun _ => contents data))) =
      Sum.elim (TracePair.packed hw hp (clockAt xs (slotAddress d v s-S))
        (clockAt xs (slotAddress d v s-S+1))) (contents (p:=p) (k:=k) data) := by
  funext i
  cases i with
  | inl i => exact (ordinary_eval _ _).trans (pairRead_clock hw hp v s header xs z ha i)
  | inr i => rfl

private theorem expr_agree {α β : Type*} (w : ℕ) {r p : ℕ} (hp : p ≤ 2^(w+1))
    (entry : Fin p) (st : Word w) (x : α → Bool) (y : β → Bool)
    (a : CodePin w r → Expr α) (b : CodePin w r → Expr β)
    (hab : ∀ j, (a j).eval x = (b j).eval y) :
    (initialCheck hp entry (fun j => .const (bits (wide st) j)) a).eval x =
      (initialCheck hp entry (fun j => .const (bits (wide st) j)) b).eval y := by
  apply Bool.eq_iff_iff.mpr
  simp only [initialCheck,Expr.eval,Bool.and_eq_true,Bool.not_eq_true',Bool.eq_false_iff,
    ne_eq,sameWord_true,allBits_true,hab]; rfl

private theorem dynamicOne (hF : Fintype.card F ≤ 2^w) (hw : 3≤w+1) (hp : p≤2^(w+1))
    (hp0 : 0<p) (st : Word w) (hs : S≤2^w) (hf : f≤2^(w+1)) (v : Fin (2^d)) (s : Fin 2) :
    dynamic (k:=k) (r:=r) hF hw hp hp0 st hs hf v (.inr (s,.inl 1)) =
      if S ≤ slotAddress d v s ∧ slotAddress d v s-S<f then
        substituteFintype (joint s) (uniformPair (w:=w) (p:=p) (r:=r) (k:=k)).2 else literal true := rfl

private theorem dynamicTwo (hF : Fintype.card F ≤ 2^w) (hw : 3≤w+1) (hp : p≤2^(w+1))
    (hp0 : 0<p) (st : Word w) (hs : S≤2^w) (hf : f≤2^(w+1)) (v : Fin (2^d)) (s : Fin 2) :
    dynamic (k:=k) (r:=r) hF hw hp hp0 st hs hf v (.inr (s,.inl 2)) =
      if slotAddress d v s=S ∧ 0<f then
        TracePair.formulaPacket (startFromText hp textExpr (fun j => .const (bits (wide st) j)) (cpuExpr' s))
      else literal (decide (0<f)) := rfl

/-- Once the local copies contain a valid program, evaluating an arbitrary
row on canonically represented CPU data agrees with the fixed-program row. -/
theorem dynamic_agrees (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (hp0 : 0 < p) (M : Machine w p r k) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (header : Fin S → Word w) (xs : Fin f → R w p r) (z : SortBits d (w+1)) (data : Memory w)
    (hd : RAM.readProgram w p r k data = some M) (v : Fin (2^d)) (a : Factor F) :
    (dynamic (r:=r) (k:=k) hF hw hp hp0 st hs hf v a).2.eval
        (valuation (by omega) v header (writeCpu hw hp xs) z (fun _ => contents (p:=p) (k:=k) data)) =
      rowBits hF hw hp M st hs hf header (writeCpu hw hp xs) z v a := by
  let x := valuation (r:=r) (p:=p) (k:=k) (by omega) v header (writeCpu hw hp xs) z (fun _ => contents data)
  let y := TracePhysical.valuation (by omega) v header (writeCpu hw hp xs) z
  change _ = (packet hF hw hp M st hs hf v a).2.eval y
  cases a with
  | inl u => exact ordinary_eval _ _
  | inr q =>
    obtain ⟨s,j|i⟩ := q
    · fin_cases j
      · exact ordinary_eval _ _
      · change (dynamic (k:=k) (r:=r) hF hw hp hp0 st hs hf v (.inr (s,.inl 1))).2.eval x =
          (packet hF hw hp M st hs hf v (.inr (s,.inl 1))).2.eval y
        rw [dynamicOne hF hw hp hp0 st hs hf v s,guardOne hF hw hp M st hs hf v s]
        by_cases ha : S ≤ slotAddress d v s ∧ slotAddress d v s-S < f
        · rw [ite_eq_left ha,ite_eq_left (show decide (S ≤ slotAddress d v s ∧ slotAddress d v s-S<f)=true from decide_eq_true ha)]
          simp only [x,substituteFintype_eval]
          rw [joint_packed hw hp v s header xs z ha.1 data]
          have hraw := funext (pairRead_clock hw hp v s header xs z ha.1)
          change _=(TracePair.pairCircuit M).2.eval (fun i => (pairRead s i).2.eval y)
          rw [hraw]
          apply Bool.eq_iff_iff.mpr
          exact (uniformPair_readProgram hw hp hd _ _).trans (TracePair.pairCircuit_correct hw hp M _ _).symm
        · have off : ¬decide (S ≤ slotAddress d v s ∧ slotAddress d v s-S < f)=true := by
            simp [ha]
          rw [ite_eq_right ha,ite_eq_right off]; rfl
      · change (dynamic (k:=k) (r:=r) hF hw hp hp0 st hs hf v (.inr (s,.inl 2))).2.eval x =
          (packet hF hw hp M st hs hf v (.inr (s,.inl 2))).2.eval y
        rw [dynamicTwo hF hw hp hp0 st hs hf v s,guardTwo hF hw hp M st hs hf v s]
        by_cases ha : slotAddress d v s = S ∧ 0 < f
        · rw [ite_eq_left ha,ite_eq_left ha,TracePair.formulaPacket_eval,TracePair.formulaPacket_eval]
          rw [startFromText_correct hp _ _ _ x hd (fun j => rfl)]
          exact expr_agree w hp M.entry st x y (cpuExpr' s) (cpuExpr s.castSucc) (fun j => rfl)
        · rw [ite_eq_right ha,ite_eq_right ha]; rfl
    · exact ordinary_eval _ _

/-- The canonical bit test does not depend on the data or the program at
all. It still rejects noncanonical binary assignments before any dynamic
transition is used. -/
theorem dynamic_canonical (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (hp0 : 0 < p) (M : Machine w p r k) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (header : Fin S → Word w) (cpu : CpuBits w r f) (z : SortBits d (w+1)) (data : Memory w)
    (v : Fin (2^d)) (s : Fin 2) :
    (dynamic hF hw hp hp0 st hs hf v (.inr (s,.inl 0))).2.eval
        (valuation (by omega) v header cpu z (fun _ => contents (p:=p) (k:=k) data)) =
      rowBits hF hw hp M st hs hf header cpu z v (.inr (s,.inl 0)) :=
  ordinary_eval _ _

end ThreeFlat.Diagonal.TraceUniformRow

end OAI
