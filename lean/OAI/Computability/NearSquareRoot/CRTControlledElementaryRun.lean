import OAI.Computability.NearSquareRoot.CRTControlledElementary

/-! # Linear time and space for a two-position operation on whole records -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Thin
open NearSquareRoot.Space

theorem boundedOfCarries {I : Type*} {V : I → ℕ} {input output : I → Tree}
    (h : Carries (fun i => (V i : ℝ)) input output) : BoundedTask V V input output := by
  obtain ⟨C, cap⟩ := h.small
  have t : Code.Task V input output := by simpa only [Nat.ceil_natCast] using h.runs.release
  apply (BoundedTask.of_time t).bound 1 (C+1)
  · intro i; simp
  · intro i
    have hc := cap i
    change ((input i).count : ℝ) ≤ C * (V i : ℝ) at hc
    have h₁ : (input i).count ≤ C * V i := by exact_mod_cast hc
    rw [Nat.succ_mul, Nat.mul_add, Nat.mul_one]
    omega

abbrev ElementLayout {I : Type} (p g b : I → ℕ) i :=
  (Series.natural (p i)).cart ((Series.natural 2).cart ((Series.natural (g i)).cart
    ((Series.natural 2).cart (Series.natural (b i)))))

def elementRulers {I : Type} (p g b : I → ℕ) (i : I) := (tally (p i), tally (g i), tally (b i))

/-- Recover three dimension tallies from the shared packet and call a linear array
routine. Only the header is inspected to obtain the range markers. -/
theorem withRulers {I : Type} (p g b V : I → ℕ) (payload output : I → Tree)
    (positive : ∀ i, 0 < p i ∧ 0 < g i ∧ 0 < b i) (area : ∀ i, p i * g i * b i ≤ V i)
    (inputCap : ∀ i, (payload i).count ≤ V i)
    (act : ∀ (src : I → Tree) (w : I → ℝ),
      let P := fun i => Series.natural (p i)
      let G := fun i => Series.natural (g i)
      let B := fun i => Series.natural (b i)
      Rim w src P → Rim w src G → Rim w src B →
      (∃ D : ℕ, ∀ i, ((P @@ G @@ B) i).count ≤ (D:ℝ)*w i) →
      Carries w src payload → Carries w src output) :
    BoundedTask V V (fun i => .fork (send (elementRulers p g b i)) (payload i)) output := by
  let w := fun i => (V i : ℝ)
  let src := fun i => Tree.fork (send (elementRulers p g b i)) (payload i)
  let P := fun i => Series.natural (p i)
  let G := fun i => Series.natural (g i)
  let B := fun i => Series.natural (b i)
  have dims (i : I) : 1 ≤ V i ∧ p i ≤ V i ∧ g i ≤ V i ∧ b i ≤ V i := by
    obtain ⟨hp,hg,hb⟩ := positive i
    have h := area i
    have xp : p i ≤ p i * g i * b i :=
      (Nat.le_mul_of_pos_right _ hg).trans (Nat.le_mul_of_pos_right _ hb)
    have xg : g i ≤ p i * g i * b i :=
      (Nat.le_mul_of_pos_left _ hp).trans (Nat.le_mul_of_pos_right _ hb)
    have xb : b i ≤ p i * g i * b i := Nat.le_mul_of_pos_left _ (Nat.mul_pos hp hg)
    omega
  have hw (i) : 1 ≤ w i := by dsimp [w]; exact_mod_cast (dims i).1
  have hhead : Volume w (fun i => send (elementRulers p g b i)) := by
    refine ⟨12,fun i => ?_⟩
    change (size (elementRulers p g b i) : ℝ) ≤ _
    have h : size (elementRulers p g b i) ≤ 12*V i := by
      simp only [elementRulers,size_prod,size_tally,tally_length]
      obtain ⟨h₁,h₂,h₃,h₄⟩ := dims i
      omega
    dsimp [w]
    exact_mod_cast h
  have hdata : Volume w payload := by
    exact ⟨1,fun i => by simpa only [Nat.cast_one,one_mul,w] using Nat.cast_le.mpr (inputCap i)⟩
  have header := Carries.dropRight hw hhead hdata
  have get (proj : Tally × Tally × Tally → Tally) (easy : Easy proj) :=
    header.chain (Carries.func hw hhead proj easy)
  have hp : Rim w src P :=
    ⟨by simpa only [Roll, P, Series.count_natural, src, elementRulers] using get (fun a => a.1) Easy.fst,
     fun i => by simpa only [P,Series.count_natural] using Nat.succ_le_of_lt (positive i).1⟩
  have hg : Rim w src G :=
    ⟨by simpa only [Roll, G, Series.count_natural, src, elementRulers] using get (fun a => a.2.1) (Easy.snd.compose Easy.fst),
     fun i => by simpa only [G,Series.count_natural] using Nat.succ_le_of_lt (positive i).2.1⟩
  have hb : Rim w src B :=
    ⟨by simpa only [Roll, B, Series.count_natural, src, elementRulers] using get (fun a => a.2.2) (Easy.snd.compose Easy.snd),
     fun i => by simpa only [B,Series.count_natural] using Nat.succ_le_of_lt (positive i).2.2⟩
  have fit : ∃ D : ℕ, ∀ i, ((P @@ G @@ B) i).count ≤ (D:ℝ)*w i := by
    refine ⟨1,fun i => ?_⟩
    simp only [fusion,P,G,B,Series.count_cart,Series.count_natural,Nat.cast_one,one_mul,w]
    exact_mod_cast (by simpa only [Nat.mul_assoc] using area i : p i * (g i * b i) ≤ V i)
  exact boundedOfCarries (act src w hp hg hb fit (Carries.dropLeft hw hhead hdata))

/-- A concrete packet and a uniform command for a two-bit gate. Each leaf is an
arbitrary complete record. In particular the same proof applies to one-bit payloads. -/
theorem elementaryTimeSpace {I : Type} (p g b V : I → ℕ) (gate : Fin 2 × Fin 2 → Fin 2 × Fin 2)
    (f : (i : I) → Fin (p i) × Fin 2 × Fin (g i) × Fin 2 × Fin (b i) → Tree)
    (positive : ∀ i, 0 < p i ∧ 0 < g i ∧ 0 < b i)
    (area : ∀ i, p i * g i * b i ≤ V i)
    (inputCap : ∀ i, (stackRun (ElementLayout p g b) f i).count ≤ V i) :
    BoundedTask V V
      (fun i => .fork (send (elementRulers p g b i)) (stackRun (ElementLayout p g b) f i))
      (stackRun (ElementLayout p g b) (fun i v =>
        let q := gate (v.2.1,v.2.2.2.1)
        f i (v.1,q.1,v.2.2.1,q.2,v.2.2.2.2))) := by
  exact withRulers p g b V _ _ positive area inputCap (fun _ _ hp hg hb hf input =>
    elementaryGate _ _ _ (Series.natural 2) (by simp) hp hg hb hf gate f input)

/-- Move one selected bit ahead of both preceding ranges, preserving their internal
order. The inverse moves it past both ranges, with the same linear time and space. -/
theorem moveBitToFront {I : Type} (p g b V : I → ℕ)
    (f : (i : I) → Fin (p i) × Fin (g i) × Fin 2 × Fin (b i) → Tree)
    (positive : ∀ i, 0 < p i ∧ 0 < g i ∧ 0 < b i)
    (area : ∀ i, p i * g i * b i ≤ V i) :
    let p' := fun i => Series.natural (p i)
    let g' := fun i => Series.natural (g i)
    let b' := fun i => Series.natural (b i)
    let bit := sr (I:=I) (Series.natural 2)
    let input := stackRun (p' @@ g' @@ bit @@ b') f
    (∀ i, (input i).count ≤ V i) →
    BoundedTask V V (fun i => .fork (send (elementRulers p g b i)) (input i))
      (stackRun (bit @@ p' @@ g' @@ b') (fun i v => f i (v.2.1,v.2.2.1,v.1,v.2.2.2))) := by
  intro p' g' b' bit input sz
  exact withRulers p g b V input _ positive area sz (fun _ _ hp hg hb fit act =>
    Thin.mount p' g' b' (Series.natural 2) (by simp) hp hg hb fit f act)

theorem moveBitFromFront {I : Type} (p g b V : I → ℕ)
    (f : (i : I) → Fin 2 × Fin (p i) × Fin (g i) × Fin (b i) → Tree)
    (positive : ∀ i, 0 < p i ∧ 0 < g i ∧ 0 < b i)
    (area : ∀ i, p i * g i * b i ≤ V i) :
    let p' := fun i => Series.natural (p i)
    let g' := fun i => Series.natural (g i)
    let b' := fun i => Series.natural (b i)
    let bit := sr (I:=I) (Series.natural 2)
    let input := stackRun (bit @@ p' @@ g' @@ b') f
    (∀ i, (input i).count ≤ V i) →
    BoundedTask V V (fun i => .fork (send (elementRulers p g b i)) (input i))
      (stackRun (p' @@ g' @@ bit @@ b') (fun i v => f i (v.2.2.1,v.1,v.2.1,v.2.2.2))) := by
  intro p' g' b' bit input sz
  exact withRulers p g b V input _ positive area sz (fun _ _ hp hg hb fit act =>
    Thin.slide p' g' b' (Series.natural 2) (by simp) hp hg hb fit f act)

end Controlled

end NearSquareRoot
end Computability
end OAI
