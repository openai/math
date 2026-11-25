import OAI.ThreeFlat.Diagonal.TraceUniformNetwork
import OAI.ThreeFlat.Diagonal.TraceNetworkValue
import OAI.ThreeFlat.Diagonal.TraceUniformChecks
import OAI.ThreeFlat.RAM.ProgramValue

namespace OAI
/-! # The universal trace network computes weighted self-advised execution -/

namespace ThreeFlat.Diagonal.TraceUniformRow

open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM RAMMemory RAMSerialization
open TraceRows TraceBanks TraceCompose TraceRowPackets TraceProgram

variable {F : Type*} [CommRing F] [Fintype F] {w p r k d f S : ℕ}

omit [Fintype F] in
private theorem product_choices {V A B : Type*} [Fintype V] [Fintype A] [Fintype B]
    (weight : V → A → F) (ok : V → B → Bool) :
    (∏ v, ∏ i : A ⊕ B, Sum.elim (weight v) (fun j => if ok v j then 1 else 0) i) =
      if ∀ v j, ok v j = true then ∏ v, ∏ i, weight v i else 0 := by
  classical
  simp only [Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr,Fintype.prod_boole,
    Finset.prod_mul_distrib]
  split <;> simp_all

private theorem guardKinds {A : Type*} (b : Unit ⊕ A × Bool → Bool) :
    (∀ j, b j = true) ↔ b (.inl ()) = true ∧ ∀ j side, b (.inr (j,side)) = true := by
  constructor
  · exact fun h => ⟨h _,fun _ _ => h _⟩
  · rintro ⟨h,h'⟩ (u|⟨j,b⟩)
    · cases u; exact h
    · exact h' j b

theorem eliminateCopies (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (hp0 : 0 < p) (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (header : Fin S → Word w) (cpu : CpuBits w r f) (z : SortBits d (w+1))
    (fit : base+(1+6*p+k)*w ≤ S) (bound : S ≤ 2^(1+d)) :
    let copies := fun _ : Fin (2^d) => textBits (by omega) base fit header
    (∑ c : Fin (2^d) → Text w p k → Bool, ∏ v : Fin (2^d), ∏ j : Check F w p k,
      coefficient j ((check hF hw hp hp0 base st hs hf v j).2.eval (valuation (by omega) v header cpu z c))) =
      if ∀ v, (programHeader (p:=p) (k:=k) v).2.eval (valuation (by omega) v header cpu z copies) = true
      then ∏ v, ∏ a : Factor F, scalar a ((dynamic (k:=k) (r:=r) hF hw hp hp0 st hs hf v a).2.eval
        (valuation (by omega) v header cpu z copies)) else 0 := by
  classical
  intro copies
  let x := fun (c : Fin (2^d) → Text w p k → Bool) (v : Fin (2^d)) => valuation (by omega) v header cpu z c
  let g := fun c v (a : Factor F) => scalar a ((dynamic (k:=k) (r:=r) hF hw hp hp0 st hs hf v a).2.eval (x c v))
  let h := fun c v (j : Unit ⊕ Text w p k × Bool) =>
    ((check hF hw hp hp0 base st hs hf v (.inr j)).2.eval (x c v))
  have wo c : (∏ v : Fin (2^d), ∏ j : Check F w p k, coefficient j
      ((check hF hw hp hp0 base st hs hf v j).2.eval (x c v))) =
      if (∀ v, (programHeader v).2.eval (x c v) = true) ∧ c = copies then ∏ v, ∏ a, g c v a else 0 := by
    trans ∏ v, ∏ j, Sum.elim (g c v) (fun i => if h c v i then 1 else 0) j
    · apply Finset.prod_congr rfl
      intro v _
      apply Finset.prod_congr rfl
      intro j _
      cases j <;> rfl
    have both : (∀ v j,h c v j=true) ↔ (∀ v,(programHeader v).2.eval (x c v)=true) ∧ c=copies := by
      have relays := relays_iff (by omega) (by omega) base fit bound header cpu z c
      constructor
      · intro all
        exact ⟨fun v=>all v (.inl ()), relays.mp (fun v j b=>all v (.inr (j,b)))⟩
      · rintro ⟨head,copy⟩ v (unitArg|⟨j,b⟩)
        · cases unitArg; exact head v
        · exact relays.mpr copy v j b
    rw [product_choices]
    by_cases on : ∀ v j,h c v j=true
    · exact (ite_eq_left on).trans (ite_eq_left (both.mp on)).symm
    · exact (ite_eq_right on).trans (ite_eq_right (fun good=>on (both.mpr good))).symm
  change (∑ c, ∏ v, ∏ j, coefficient j ((check hF hw hp hp0 base st hs hf v j).2.eval (x c v))) = _
  simp_rw [wo]
  rw [Finset.sum_eq_single copies]
  · simp [g,x]
  · intro c _ hne; simp [hne]
  · simp

theorem uniformWeight (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (hp0 : 0 < p) (M : Machine w p r k) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (header : ℕ → Word w) (cpu : CpuBits w r f) (z : SortBits d (w+1)) (fit : S+f ≤ 2^(1+d))
    (data : Memory w) (hd : RAM.readProgram w p r k data = some M) :
    (∏ v : Fin (2^d), ∏ a : Factor F, scalar a ((dynamic (k:=k) (r:=r) hF hw hp hp0 st hs hf v a).2.eval
      (valuation (by omega) v (fun i : Fin S => header i.val) cpu z (fun _ => contents (p:=p) (k:=k) data)))) =
      binaryWeight (RAM.FieldCode.ofCardLe hF) M hw hp st S d f header cpu z := by
  classical
  let xs := readCpu hw hp cpu
  let h := fun i : Fin S => header i.val
  by_cases hc : writeCpu hw hp xs=cpu
  · rw [← product_binaryWeight hF hw hp M st hs hf header cpu z fit, ← hc]
    apply Finset.prod_congr rfl; intro v _
    apply Finset.prod_congr rfl; intro a _
    exact congrArg (scalar a) (dynamic_agrees hF hw hp hp0 M st hs hf h xs z data hd v a)
  · rw [factorProduct]
    rw [ite_eq_right]
    · simp [binaryWeight,xs] at hc ⊢
      simp [hc]
    · intro ok
      apply hc
      apply (all_canonical hF hw hp M st hs hf h cpu z fit).mp
      intro v s
      exact (dynamic_canonical hF hw hp hp0 M st hs hf h cpu z data v s).symm.trans (ok v (.inr (s,0)))

/-- Evaluate the same network for every setting of the program prefix,
including a rejecting malformed entry word. The rest of the header and
the memory trace may also depend on that prefix. -/
theorem network_eval_program (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (hp0 : 0 < p) (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (header : ℕ → Word w) (fit : S+f ≤ 2^(1+d)) (textFit : base+(1+6*p+k)*w ≤ S)
    (data : Memory w) (textOk : textBits (by omega) base textFit (fun i : Fin S => header i.val) =
        contents (p:=p) (k:=k) data) :
    (network hF hw hp hp0 base st hs hf r k d).eval (TracePhysical.headerPins (fun i : Fin S => header i.val)) =
      ((RAM.readProgram w p r k data).map (fun M => RAM.value (RAM.FieldCode.ofCardLe hF) M f st
        (initialMemory S header))).getD 0 := by
  classical
  rw [network_eval]
  simp_rw [eliminateCopies (r:=r) (f:=f) (d:=d) hF hw hp hp0 base st hs hf (fun i : Fin S => header i.val) _ _ textFit (show S ≤ 2^(1+d) by omega),
    textOk,all_header]
  cases hd : RAM.readProgram w p r k data with
  | none => simp
  | some M =>
    simp only [Option.isSome_some,ite_true,Option.map_some,Option.getD_some]
    rw [value_eq_sum_binary (RAM.FieldCode.ofCardLe hF) M hw hp st S d f header hs hf fit]
    apply Finset.sum_congr rfl; intro cpu _
    apply Finset.sum_congr rfl; intro z _
    exact uniformWeight hF hw hp hp0 M st hs hf header cpu z fit data hd

/-- Keeping all initialization inside the declared input header gives
exactly the native semantics with the program text in the advice segment. -/
theorem network_eval_advice (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (hp0 : 0 < p) (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (fit : S+f ≤ 2^(1+d)) {q : ℕ} (textFit : (1+6*p+k)*w ≤ q) (adviceFit : base+q ≤ S)
    (D : Fin q → Bool) (input : Memory w) :
    let original := initialMemory S input
    let header := RAM.memoryWithAdvice base D original
    (network hF hw hp hp0 base st hs hf r k d).eval (TracePhysical.headerPins (fun i : Fin S => header i.val)) =
      RAM.adviceValue (RAM.FieldCode.ofCardLe hF) p r k textFit D f st base original := by
  let original := initialMemory S input
  let header := RAM.memoryWithAdvice base D original
  let data := RAM.adviceWords w (1+6*p+k) (fun i => D (i.castLE textFit))
  have hd : initialMemory S header = header := by
    funext a
    by_cases h : a < S
    · simp [initialMemory,h]
    · have ha : base+q ≤ a := by omega
      rw [show header a = original a from RAM.memoryWithAdvice_outside base D _ (.inr ha)]
      simp [initialMemory,original,h]
  change (network hF hw hp hp0 base st hs hf r k d).eval (TracePhysical.headerPins (fun i : Fin S => header i.val)) = _
  rw [network_eval_program hF hw hp hp0 base st hs hf header fit (by omega) data
    (textBits_advice (by omega) base textFit adviceFit D original), hd]
  unfold RAM.adviceValue RAM.readAdvicePrefix
  cases h : RAM.readProgram w p r k data <;> simp [h,data,original,header] at *

end ThreeFlat.Diagonal.TraceUniformRow

end OAI
