import OAI.Hierarchy.CorrectionRetained
import OAI.Hierarchy.Catalyst
import OAI.Hierarchy.SparseCorrection
import OAI.Hierarchy.CorrectionWiring
import OAI.Hierarchy.CorrectionMask

namespace OAI
/-! # Trivalent assembly of sparse exact corrections

The checked compactor preserves the multiset of active data words. Its terminal
bank applies one optional exact test per physical output slot. The two selector
bits distinguish ordinary, positive exact, and negative approximate factors.
-/

noncomputable section
open scoped Classical BigOperators
namespace Hierarchy.CorrectionAssembly
open ThreeFlat
open Routing Routing.Spill

open CorrectionWiring
variable {F : Type*} [Field F]
variable {k p s r L : ℕ} {b : Fin k → ℕ}
private abbrev Data (s p : ℕ) {k : ℕ} (b : Fin k → ℕ) := Fin s × Catalyst.Port p b
private abbrev Pins (s p : ℕ) {k : ℕ} (b : Fin k → ℕ) := (Data s p b ⊕ Fin s) ⊕ Fin s

private def choice (sel ex : Bool) : F := if ex then (if sel then 1 else 0) else (if sel then -1 else 1)

private def pass (ex : Bool) (x : Catalyst.Port p b → Bool) : F :=
  if ex = true ∧ ¬∀ w : Catalyst.Wire b, x (.inr (w,false)) = x (.inr (w,true)) then 0 else 1

private def row (X : Catalyst.Approximation F k p) (i : Fin s) (y : Pins s p X.width → Bool) : F :=
  let sel := y (.inl (.inr i))
  let ex := y (.inr i)
  let x := fun j => y (.inl (.inl (i,j)))
  choice sel ex * (if ex = false then X.coeff x else 1) * pass ex x

private theorem revise {P : Type} [Fintype P] {f g : (P → Bool) → F} {c d : ℕ}
    (h : Realizes P f c) (hc : c ≤ d) (same : ∀ x, f x = g x) : Realizes P g d := by
  obtain ⟨N,cost,ev⟩ := h
  exact ⟨N,cost.trans hc,fun x => (ev x).trans (same x)⟩

private theorem row_realizes (X : Catalyst.Approximation F k p) (i : Fin s) :
    Realizes (Pins s p X.width) (row X i)
      ((16+(176*X.network.cells+29*X.network.internal))+40*Fintype.card (Catalyst.Wire X.width)) := by
  let W := Catalyst.Wire X.width
  let T := Pins s p X.width
  let ctrl (y : T → Bool) := choice (F:=F) (y (.inl (.inr i))) (y (.inr i))
  have control : Realizes T ctrl 16 := by
    let w : Bool → T := fun t => if t then .inr i else .inl (.inr i)
    simpa [w,ctrl,Function.comp_def] using
      pull (table (fun x : Bool → Bool => choice (F:=F) (x false) (x true))) w
  let pin (j : Option (Catalyst.Port p X.width)) : T :=
    j.elim (.inr i) (fun q => .inl (.inl (i,q)))
  have ordinary := pull (enabled X.network false) pin
  let a (j : W) (y : T → Bool) : F :=
    if y (.inr i) = true → y (.inl (.inl (i,.inr (j,false)))) = y (.inl (.inl (i,.inr (j,true))))
      then 1 else 0
  have bypass (j : W) : Realizes T (a j) 40 := by
    let w : Fin 3 → T := ![.inr i,.inl (.inl (i,.inr (j,false))),.inl (.inl (i,.inr (j,true)))]
    apply revise (pull (table (fun x : Fin 3 → Bool =>
      if x 0 = true → x 1 = x 2 then (1:F) else 0)) w) (by norm_num)
    intro y
    simp only [a,w,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two];
      split_ifs <;> rfl
  have prodPass (y : T → Bool) : (∏ j, a j y) = pass (y (.inr i)) (fun j => y (.inl (.inl (i,j)))) := by
    simp only [a,Fintype.prod_boole,pass]
    by_cases el : y (.inr i) = true
    · simp only [el,eq_self,true_implies,true_and,ite_not]
      split_ifs <;> first | rfl
    · simp [el]
  have built := multiply (multiply control ordinary) (product a _ bypass)
  apply revise built (by
    have cardW : Fintype.card W = Fintype.card (Catalyst.Wire X.width) :=
      Fintype.card_congr (Equiv.refl W)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,cardW]
    omega)
  intro y
  rw [prodPass]
  cases h : y (.inr i) <;>
    simp [row,ctrl,pin,Function.comp_def,h,Catalyst.Approximation.coeff,TypedWiring.value]

private def inputWire (z : RecordPins s p) : Pins s p b :=
  z.2.elim (.inr z.1) (fun j => .inl (.inl (z.1,.inl j)))

private def body (X : Catalyst.Approximation F k p) (C : Compactor F s r p)
    (f : (Fin p → Bool) → F) (L : ℕ) (y : Pins s p X.width → Bool) : F :=
  let J := Finset.univ.filter fun i : Fin s => y (.inl (.inr i)) = true
  (if J.card ≤ L then 1 else 0) *
    ((∏ i, row X i y) * bank C f (y ∘ inputWire))

private def rowCost (X : Catalyst.Approximation F k p) : ℕ :=
  (16+(176*X.network.cells+29*X.network.internal))+40*Fintype.card (Catalyst.Wire X.width)

private theorem body_realizes (X : Catalyst.Approximation F k p) (C : Compactor F s r p)
    (N : BitNetwork F (Fintype.card (Fin p))) {m : ℕ}
    (mask : Realizes (Fin s) (fun y => if (Finset.univ.filter (fun i => y i = true)).card ≤ L
      then (1:F) else 0) m) :
    Realizes (Pins s p X.width) (body X C (TypedWiring.value N) L)
      (m+(s*rowCost X+(C.network.cells+r*(176*N.cells+29*N.internal)))) := by
  have h := multiply (pull mask (fun i => (Sum.inl (Sum.inr i) : Pins s p X.width)))
    (multiply (product (row X) _ (row_realizes X)) (pull (bank_realizes C N) inputWire))
  apply revise h (by simp [rowCost])
  intro y
  unfold body
  dsimp only [Function.comp_apply]

private def selected (z : Fin s → Bool) := Finset.univ.filter (fun i => z i = true)

private def factor (sel ex : Bool) (ideal approx : F) : F :=
  if ex then (if sel then ideal else 0) else (if sel then -approx else approx)

private theorem body_eq (X : Catalyst.Approximation F k p) (C : Compactor F s r p)
    (f : (Fin p → Bool) → F) (hr : 2*L ≤ r) (x : Data s p X.width → Bool)
    (sel ex : Fin s → Bool) :
    body X C f L (Sum.elim (Sum.elim x sel) ex) =
      if (selected sel).card ≤ L then
        ∏ i, factor (sel i) (ex i) (Catalyst.ideal X.width f (fun j => x (i,j)))
          (X.coeff (fun j => x (i,j))) else 0 := by
  let y := Sum.elim (Sum.elim x sel) ex
  let z := y ∘ (inputWire : RecordPins s p → Pins s p X.width)
  have hz : occupied z = selected ex := by
    ext i
    simp only [occupied,selected,Finset.mem_filter,Finset.mem_univ,true_and]; rfl
  by_cases legal : (selected sel).card ≤ L
  · change (if (selected sel).card ≤ L then 1 else 0) * ((∏ i, row X i y)*bank C f z) = _
    rw [ite_eq_left legal,one_mul,ite_eq_left legal]
    by_cases sub : selected ex ⊆ selected sel
    · have capacity : 2*(occupied z).card ≤ r := by
        rw [hz]
        have := Finset.card_le_card sub
        omega
      rw [show bank C f z = _ from compact_eval C f z capacity,← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      cases hs : sel i <;> cases he : ex i <;>
        by_cases eqn : ∀ w : Catalyst.Wire X.width, x (i,.inr (w,false)) = x (i,.inr (w,true)) <;>
        simp [row,choice,pass,z,y,inputWire,Function.comp_def,Catalyst.ideal,hs,he,eqn,factor]
    · obtain ⟨i,hi,hn⟩ := Finset.not_subset.mp sub
      have he : ex i = true := (Finset.mem_filter.mp hi).2
      have hs : sel i = false := by simpa [selected] using hn
      have zeroRow : row X i y = 0 := by simp [row,choice,y,hs,he]
      have zeroFactor : factor (sel i) (ex i) (Catalyst.ideal X.width f (fun j => x (i,j)))
          (X.coeff (fun j => x (i,j))) = 0 := by simp [factor,he,hs]
      have leftZero : (∏ j, row X j y) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) zeroRow
      have rightZero : (∏ j, factor (sel j) (ex j) (Catalyst.ideal X.width f (fun q => x (j,q)))
          (X.coeff (fun q => x (j,q)))) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) zeroFactor
      rw [leftZero,zero_mul,rightZero]
  · change (if (selected sel).card ≤ L then 1 else 0) * _ = _
    simp only [ite_eq_right legal,zero_mul]

private def maskEquiv (s : ℕ) : Finset (Fin s) ≃ (Fin s → Bool) where
  toFun J i := decide (i ∈ J)
  invFun := selected
  left_inv J := by ext; simp [selected]
  right_inv m := by funext i; simp [selected]

private theorem inner_sum (sel : Fin s → Bool) (ideal approx : Fin s → F) :
    (∑ ex : Fin s → Bool, ∏ i, factor (sel i) (ex i) (ideal i) (approx i)) =
      SparseCorrection.term (ideal-approx) approx (selected sel) := by
  let g (i : Fin s) (b : Bool) := factor (sel i) b (ideal i) (approx i)
  have expand : (∑ ex : Fin s → Bool, ∏ i, g i (ex i)) = ∏ i, ∑ b, g i b := by
    refine Eq.trans ?_ (Fintype.prod_sum g).symm
    apply Finset.sum_congr (univ_congr _ _)
    intro x _
    rfl
  change (∑ ex : Fin s → Bool, ∏ i, g i (ex i)) = _
  rw [expand]
  dsimp only [g]
  have point (i : Fin s) : (∑ b : Bool, factor (sel i) b (ideal i) (approx i)) =
      if i ∈ selected sel then ideal i-approx i else approx i := by
    cases h : sel i <;> simp [factor,selected,h,sub_eq_add_neg]
  simp_rw [point]
  rw [Finset.prod_ite]
  simp [SparseCorrection.term,Finset.filter_notMem_eq_sdiff,
    Finset.compl_eq_univ_sdiff]

/-- The exact coefficient of the assembled network, with all data and catalyst
bits exposed. Selector multiplicities persist in arbitrary characteristic. -/
theorem exists_network_of_compactor (X : Catalyst.Approximation F k p) (C : Compactor F s r p)
    (N : BitNetwork F (Fintype.card (Fin p))) {m : ℕ}
    (mask : Realizes (Fin s) (fun y => if (selected y).card ≤ L then (1:F) else 0) m)
    (hr : 2*L ≤ r) :
    ∃ A : BitNetwork F (Fintype.card (Fin s × Catalyst.Port p X.width)),
      A.cells + A.internal ≤
        4*(m+(s*((16+(176*X.network.cells+29*X.network.internal))+
        40*Fintype.card (Catalyst.Wire X.width))+
        (C.network.cells+r*(176*N.cells+29*N.internal))))+1 ∧
      ∀ x, TypedWiring.value A x =
        ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin s) => J.card ≤ L),
          SparseCorrection.term
            (fun i => Catalyst.ideal X.width (TypedWiring.value N) (fun j => x (i,j)) -
              X.coeff (fun j => x (i,j))) (fun i => X.coeff (fun j => x (i,j))) J := by
  obtain ⟨A,bd,ev⟩ := hide (hide (body_realizes X C N mask))
  refine ⟨A.compactHidden,(A.compactHidden_size).trans (by dsimp [rowCost] at bd; omega),fun x => ?_⟩
  rw [show TypedWiring.value A.compactHidden x = TypedWiring.value A x from
    A.compactHidden_eval _,ev]
  simp_rw [body_eq X C _ hr]
  let a (i : Fin s) := Catalyst.ideal X.width (TypedWiring.value N) (fun j => x (i,j))
  let q (i : Fin s) := X.coeff (fun j => x (i,j))
  have inner (sel : Fin s → Bool) :
      (∑ ex : Fin s → Bool, if (selected sel).card ≤ L then
        ∏ i, factor (sel i) (ex i) (a i) (q i) else 0) =
        if (selected sel).card ≤ L then SparseCorrection.term (a-q) q (selected sel) else 0 := by
    by_cases hl : (selected sel).card ≤ L <;> simp [hl,inner_sum]
  change (∑ sel : Fin s → Bool, ∑ ex : Fin s → Bool, if (selected sel).card ≤ L then
      ∏ i, factor (sel i) (ex i) (a i) (q i) else 0) = _
  simp_rw [inner]
  rw [← (maskEquiv s).sum_comp]
  have re (J : Finset (Fin s)) : selected (maskEquiv s J) = J := (maskEquiv s).left_inv J
  simp only [re, ← Finset.sum_filter]; rfl


/-- Uniform physical size, with only a constant multiple of the correction
quota many exact modules and one switchable approximate module per copy. -/
def NetworkBound (F : Type*) [Field F] (K c : ℕ) : Prop :=
    ∀ {k p s : ℕ} (X : Catalyst.Approximation F k p)
      (N : BitNetwork F (Fintype.card (Fin p))) (L : ℕ), 2*L ≤ s →
      ∃ A : BitNetwork F (Fintype.card (Fin s × Catalyst.Port p X.width)),
        A.cells+A.internal ≤
          4*((32768*(s+1)*(Nat.log 2 (s+1)+2)^3+1) +
          (s*((16+(176*X.network.cells+29*X.network.internal))+
           40*Fintype.card (Catalyst.Wire X.width))+
          (s*(Nat.log 2 s+p+4)*c+K*L*(176*N.cells+29*N.internal))))+1 ∧
        ∀ x, TypedWiring.value A x = retained X (TypedWiring.value N) L x

theorem sparse_networks_uniform :
    ∃ K c : ℕ, ∀ (F : Type*) [Field F], NetworkBound F K c := by
  obtain ⟨K,c,banks⟩ := exists_bank ℕ
  refine ⟨K,c,fun F _ {k p s} X N L hs => ?_⟩
  by_cases hL : 0 < L
  · obtain ⟨r,D,lo,hi,bd⟩ := banks s L p hL hs
    let C := castCompactor F D
    have cb : C.network.cells ≤ s*(Nat.log 2 s+p+4)*c := bd
    have mask : Realizes (Fin s) (fun y => if (selected y).card ≤ L then (1:F) else 0)
        (32768*(s+1)*(Nat.log 2 (s+1)+2)^3+1) :=
      ⟨CorrectionMask.network F s L, CorrectionMask.cells F s L, CorrectionMask.eval F⟩
    obtain ⟨A,cost,ev⟩ := exists_network_of_compactor X C N mask lo
    refine ⟨A,cost.trans ?_,ev⟩
    have := Nat.mul_le_mul_right (176*N.cells+29*N.internal) hi
    omega
  · have hz : L = 0 := by omega
    subst L
    let T := Data s p X.width
    let f (i : Fin s) (x : T → Bool) := X.coeff (fun j => x (i,j))
    have realized (i : Fin s) : Realizes T (f i) X.network.cells :=
      pull (show Realizes (Catalyst.Port p X.width) X.coeff X.network.cells from
        ⟨X.network,le_rfl,fun _ => rfl⟩) (fun j => (i,j))
    obtain ⟨A,bd,ev⟩ := product f (fun _ => X.network.cells) realized
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at bd
    refine ⟨A.compactHidden,A.compactHidden_size.trans ?_,fun x => ?_⟩
    · have := Nat.mul_le_mul_left s (show X.network.cells ≤
          (16+(176*X.network.cells+29*X.network.internal))+40*Fintype.card (Catalyst.Wire X.width)
          by omega)
      omega
    · rw [show TypedWiring.value A.compactHidden x = TypedWiring.value A x from
          A.compactHidden_eval _,ev]
      have onlyEmpty : Finset.univ.filter (fun J : Finset (Fin s) => J.card ≤ 0) = {∅} := by
        ext J
        simp
      unfold retained
      rw [onlyEmpty,Finset.sum_singleton]
      simp [SparseCorrection.term,f]

theorem sparse_networks (F : Type*) [Field F] : ∃ K c : ℕ, NetworkBound F K c := by
  obtain ⟨K,c,h⟩ := sparse_networks_uniform
  exact ⟨K,c,h F⟩

end Hierarchy.CorrectionAssembly

end
end OAI
