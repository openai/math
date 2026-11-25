import OAI.Computability.IntegerMultiplication.Direct

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Fix
open Strip Code Optic
variable {I A : Type} [Codec A] {O X B : I→Type} [(i:I)→DecidableEq (X i)]
variable {s : (i:I)→Series (O i)} {t : (i:I)→Series (B i)}
variable (g : (i:I)→File (s i) (X i) (t i)) (q : (i:I)→X i≃X i)
variable (bad : (i:I)→X i→Bool) (ids : (i:I)→X i→Key)
variable (hi : ∀ i,Function.Injective (ids i))
variable (f : (i:I)→O i→A)
variable (S : ∀ i x,bad i x=false → q i x=x) {d : I→ℕ}
variable (eq : ∀ i a,(ids i a).length=d i)

include S hi eq
omit [Codec A] in
theorem ruling :
    Rule s s (fun i => sheet (g i) (bad i) (ids i ∘ q i))
      (fun i => sheet (g i) (bad i) (ids i)) f
      (fun i => Optic.travel (Optic.field (g i).focus (q i)) (f i)) d where
  snag i _ h :=
    let ⟨a,_ha,hh⟩ := came.mp h
    hh ▸ eq i (q i (slot (g i) a))
  tagEnd i _ h :=
    let ⟨_a,_ha,hh⟩ := came.mp h
    hh ▸ eq i _
  same i k := intend (g i) (q i) (bad i) (ids i) (hi i) (f i) (S i) k
  stationary i := untreated (g i) (q i) (bad i) (ids i) (f i) (S i)

variable [(i:I)→Fintype (X i)] [(i:I)→Fintype (B i)] [(i:I)→Fintype (O i)] [(i:I)→DecidableEq (O i)]
variable {r : Regime I} {n l : I→ℕ} {p : I→Tree}
theorem Palace
    (dataR : Rip r n l p (stackRun s fun i a => send (f i a)))
    (tagsR : Rip r n l p (stackRun s fun i a => send (sheet (g i) (bad i) (ids i ∘ q i) a)))
    (tagsQ : Rip r n l p (stackRun s fun i a => send (sheet (g i) (bad i) (ids i) a)))
    (size0 : ∀ i,(s i).count ≤ n i)
    (H : Dom r.scale d)
    (C : ℕ) (f0 : ∀ i j,size (f i j) ≤ C*(l i+1))
    (few : ∃ N : ℕ,∀ i,(d i+1)*((Finset.univ.filter fun x => (bad i x)).card)≤
      N*Fintype.card (X i)) :
    Rip r n l p (stackRun s fun i a => send (Optic.travel (Optic.field (g i).focus (q i)) (f i) a)) := by
  apply allocate _ _ (fun i => sheet (g i) (bad i) (ids i ∘ q i)) (fun i => sheet (g i) (bad i) (ids i)) f _
    (ruling g q bad ids hi f S eq) dataR tagsR tagsQ size0 size0 H C f0 (fun i _ => f0 i _)
  obtain ⟨N,g0⟩ := few
  refine ⟨2*N,fun i => ?_⟩
  have z := filter_rate (g i) (bad i)
  obtain x := (Fintype.card_congr (g i).focus)
  simp only [Fintype.card_prod] at x
  have e := Nat.mul_le_mul_right ((t i).count) (g0 i)
  unfold rarity sheet
  simp only [z,Nat.mul_add]
  rw [← Nat.mul_assoc]
  specialize size0 i
  simp only [Strip.Series.total] at *
  rw [x] at size0 -- second maybe no
  -- convert
  have := Nat.mul_le_mul_left (2*N) size0
  simp only [← Nat.mul_assoc, two_mul,Nat.add_mul] at *
  omega
end Fix

end IntegerMultiplication
end Computability
end OAI
