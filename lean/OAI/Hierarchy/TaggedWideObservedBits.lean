import OAI.Hierarchy.TaggedWideObservationCore

namespace OAI
/-! # Closing the native verifier over one untyped binary workspace -/

noncomputable section
namespace Hierarchy.TaggedShorterControlHistory
open ThreeFlat Routing Diagonal TraceRows TraceBanks
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory
open scoped Classical BigOperators

def observationBits (u w : ℕ) : (Fin u → Word w) ≃ (Fin u × Fin w → Bool) :=
  let bitword : Word w ≃ (Fin w → Bool) := Equiv.ofBijective TraceWords.bits
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨TraceWords.bits_injective,by
      simp [Word]⟩)
  (Equiv.piCongrRight fun _ => bitword).trans (Equiv.curry _ _ _).symm

abbrev HiddenBits (w r f u m a : ℕ) :=
  TaggedShorterClock.Pin w r f ⊕ (Fin u × Fin (w+1)) ⊕ Hole m a

/-- Count every physical hidden bit in the verified history, including
all observed memory words and the data pins of the tagged control slices. -/
theorem hiddenBits_card (w r f u m a : ℕ) :
    Fintype.card (HiddenBits w r f u m a) =
      f*((5+r)*(w+1)) + u*(w+1) + a*Tagged.pins m m := by
  simp [HiddenBits,TaggedShorterClock.Pin,Hole,Tagged.ControlSort.Hole,Nat.add_assoc]

theorem hiddenBits_bound (w r f u m a rows : ℕ) (count : f+u≤rows) :
    Fintype.card (HiddenBits w r f u m a) ≤
      rows*((5+r)*(w+1)) + 3*a*2^m*m := by
  rw [hiddenBits_card]
  have pad := Nat.mul_le_mul_right ((5+r)*(w+1)) count
  have obs : u*(w+1) ≤ u*((5+r)*(w+1)) :=
    Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  calc
    _ ≤ (f+u)*((5+r)*(w+1)) + a*Tagged.pins m m := by
      rw [Nat.add_mul f u ((5+r)*(w+1))]
      exact Nat.add_le_add_right (Nat.add_le_add_left obs _) _
    _ ≤ rows*((5+r)*(w+1)) + a*Tagged.pins m m := Nat.add_le_add_right pad _
    _ = _ := by unfold Tagged.pins; ring

/-- The hidden bits for the observed words occur in the common workspace
and can also be read directly by every site of the native host. -/
theorem bitWorkspace {F : Type*} [CommRing F] {w p r k S f u m a : ℕ}
    (M : Machine w p r k) (hw : 3≤w+1) (hp : p≤2^(w+1)) (st : Word w)
    (addr : Fin u → Word w) (header : ℕ → Word w) (hs : S≤2^w) (clock : f+u≤2^(w+1))
    (φ : (Fin u × Fin (w+1) → Bool) → F) :
    let hS : S≤2^(w+1) := hs.trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
    (∑ y : HiddenBits w r f u m a → Bool,
      TypedWiring.value (network (F:=F) M hw hp st hS clock (wide ∘ addr))
        (Sum.elim (Sum.elim (fun i => TraceWords.bits (wide (header i.1.val)) i.2)
          (Sum.elim (y ∘ Sum.inl) (fun i => y (Sum.inr (.inl i)))))
          (fun z => y (.inr (.inr z)))) *
      (∏ b : Fin a,Tagged.coeff F m m (fun j => y (.inr (.inr (b,j))))) *
        φ (fun i => y (.inr (.inl i)))) =
      observationSum (m:=m) a M hw hp st addr header hs clock (fun obs => φ (observationBits u (w+1) obs)) := by
  classical
  intro hS
  unfold observationSum
  rw [←(Equiv.sumArrowEquivProdArrow (TaggedShorterClock.Pin w r f)
    ((Fin u × Fin (w+1)) ⊕ Hole m a) Bool).symm.sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro raw _
  rw [←(Equiv.sumArrowEquivProdArrow (Fin u × Fin (w+1)) (Hole m a) Bool).symm.sum_comp,Fintype.sum_prod_type]
  rw [←(observationBits u (w+1)).sum_comp]
  apply Finset.sum_congr rfl
  intro seen _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  rfl

/-- The actual CPU, its fixed sort occurrences and every site's binary
pin tuple coexist in one Boolean workspace. Arbitrary signed site and
bank factors may inspect the same terminal words under this sum. -/
theorem sum_site_workspace {F X : Type*} [CommRing F] [Fintype X] {W p r k S f u m a t : ℕ}
    (M : Machine W p r k) (ww : 3≤W+1) (hp : p≤2^(W+1)) (st : Word W)
    (addr : Fin u→Word W) (header : ℕ→Word W) (hs : S≤2^W) (clock : f+u≤2^(W+1))
    (fits : S+(f+u)≤2^m) (positive : 0<a) (record : TaggedShorterHistoryOrder.RecordWidth (W+1)≤a*m)
    (done : Config W p r) (out : Memory W) (result : Option (Word W)) (fuel : t<f)
    (ran : RAM.advance M.program t (M.program.start st) (initialMemory S header)=some (done,out))
    (halt : M.program.step done=.finish result)
    (site : (X→Bool)→(Fin u × Fin (W+1)→Bool)→F) :
    let hS : S≤2^(W+1) := hs.trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
    (∑ all : X ⊕ HiddenBits W r f u m a→Bool,
      let y := all ∘ Sum.inr
      TypedWiring.value (network (F:=F) M ww hp st hS clock (wide ∘ addr))
        (Sum.elim (Sum.elim (fun i=>TraceWords.bits (wide (header i.1.val)) i.2)
          (Sum.elim (y ∘ Sum.inl) (fun i=>y (.inr (.inl i))))) (fun z=>y (.inr (.inr z))))*
      (∏ j : Fin a,Tagged.coeff F m m (fun b=>y (.inr (.inr (j,b)))))*
      site (all ∘ Sum.inl) (fun i=>y (.inr (.inl i)))) =
      ∑ x : X→Bool,site x (observationBits u (W+1) (fun j=>wide (out (addr j).val))) := by
  intro hS
  rw [←(Equiv.sumArrowEquivProdArrow X (HiddenBits W r f u m a) Bool).symm.sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro data _
  refine (bitWorkspace M ww hp st addr header hs clock (m:=m) (a:=a) (site data)).trans ?_
  exact observed_weight M ww hp st addr header hs clock fits positive record done out result fuel ran halt _

end Hierarchy.TaggedShorterControlHistory

end
end OAI
