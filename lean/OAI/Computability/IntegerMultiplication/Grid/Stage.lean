import OAI.Computability.IntegerMultiplication.Grid.Faith
import OAI.Computability.IntegerMultiplication.Hook.Test

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Grid
open Strip Dims Loom Adic Code Net Net.Walsh Haze Earth Phase Packed Axon Staff Dusk Bits Hook
noncomputable section
variable {I J W A : Type} [Fintype J] [DecidableEq J] [Fintype W] (dl : Guild J W A Motif.sigma) (R₁ : Series W)
variable (p t : I→Tape) (f g j y w U frac : I→ℕ) {T:I→Type} (z:(i:I)→Series (T i)) {r:Regime I}
variable (h : ArrayCards r p t w)
variable (F: Realizes r f) (G:Realizes r g) (J₁:Realizes r j) (Y:Realizes r y)
variable (u:∀ i,((z i).count+1)*(w i+1)≤U i)
variable (s:∀ i,Phase.safe (f i) (j i)) (q:∀ i,Phase.safe (f i) (y i)) (m:∀ i,f i≤w i+1)
variable (hn:∀ i,1≤f i)
variable (o : (i:I)→Fin (f i)→Word) (O:r.Has (fun i=>List.ofFn (o i)))
variable (K e m₁ : I→ℕ) (data_ : Hook.Slice r (Hook.norm f g j y) K e m₁ w)
variable (b : (i:I)→ ℕ→Grain (w i))
abbrev boxB (i:I) (x : ℕ) : Orb := (tally (frac i),Dusk.mark (b i x))
abbrev desk {w_ : ℕ} (k p : ℕ) (b : ℕ → Grain w_) (j : Fin (2^k)) : Ask.Card Orb :=
  (phrase k j.val,tally p,Dusk.mark (b j))
def telex {w_ : ℕ} (p k : ℕ) (b : ℕ → Grain w_) := List.ofFn (desk k p b)
abbrev call (i:I) := telex (frac i) (altitude g j y i) (b i)
variable (ha : ∀i,frac i≤w i+1)
    (hr : ∀i,altitude g j y i≤w i+1)
    (ho : ∀i,(2^altitude g j y i) * (w i+1) ≤ U i)
include ha hr ho
private theorem machine_v :
    Register g j y w U (call g j y w frac b) (fun _=> Grid.adjust)
      (boxB w frac b) (fun _=> Grid.launch) (fun i=> (Grid.tax (w i):ℝ)) where
  correct i a v := by
    let k := altitude g j y i
    change a∈ List.ofFn _ at v
    obtain ⟨r,t⟩ := List.mem_ofFn.mp v; subst a
    change boxB w frac b i r.val=boxB w frac b i (Bits.value (Bits.phrase k r.val))
    rw [Bits.value_phrase r.isLt]
  full i n v := ⟨desk _ (frac i) (b i) ⟨n,v⟩,
    List.mem_ofFn.mpr ⟨⟨n,v⟩,rfl⟩, value_phrase v⟩
  width := by
    refine ⟨11,fun i x=>?_⟩
    rw [boxB,size_prod,size_tally,tally_length,Dusk.volume]
    specialize ha i; omega -- 4(w+1)+3+1+2f+1≤11
  released i x k := Grid.inject x _
  volume := by
    let n := altitude g j y
    have e i (t:Fin (2^n i)) : Code.size (desk _ (frac i) (b i) t) ≤ 15*(w i+1) := by
      rw [desk,size_prod,size_word,size_prod,size_tally,Dusk.volume,phrase_length,tally_length]
      have f : n i ≤ w i+1 := hr i
      specialize ha i; omega
    have S {A : Type} [Codec A] (l : List A) (n:ℕ) (g:∀ i∈l,size i≤ n) :
        size l ≤ l.length*(n+1)+1 := by
      induction l with
      | nil => simp
      | cons a m ih =>
        rw [size_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
        have t := ih (fun i v=> g i (List.mem_cons_of_mem _ v))
        have u := g a List.mem_cons_self; omega
    refine ⟨16,fun i=> ?_⟩
    refine (S _ (15*(w i+1)) (fun x (h:x∈List.ofFn _)=>?_)).trans ?_
    · obtain ⟨t,rfl⟩ := List.mem_ofFn.mp h; exact e i _
    rw [List.length_ofFn]; specialize ho i; nlinarith
  fare := by
    refine ⟨4,fun i=>?_⟩
    change (List.length (List.ofFn _)+1)*_ ≤ _
    rw [List.length_ofFn]
    have := hr i; specialize ho i
    have t := Nat.pow_pos (n:=altitude g j y i) (by decide:(0:ℕ)<2)
    nlinarith
  consumes := by
    let f : Sigma (fun i:I=>Grain (w i)×ℕ) → Orb := fun x=> boxB w frac b x.1 x.2.2
    exact Grid.ferry _ f _ 11 (fun i=> by unfold f; rw [boxB,size_prod,size_tally,tally_length,Dusk.volume]; have := ha i.1; omega)
-- canonical multiplication driver gift + analytic
abbrev mercy i := Hook.cost_ f g j y (fun i=> (Grid.tax (w i):ℝ)) K e i
include h dl R₁ F G J₁ Y s q m hn u O data_
theorem sheer (x:(i:I)→ Datum p t f g j y w (T:=T) i) :
    let N := Globe p t f g j y
    let C := crate p t f g j y w z
    Breeze (mercy f g j y w K e) r N U (together r.header (together (send ∘ call g j y w frac b) (C x)))
      (C fun i=> Hook.complete_ p t f g j y w o (boxB w frac b)
        (fun _=>Grid.launch) i (x i)) :=
  gift (([]:Tally),([]:Bits.Word),([]:Bits.Word)) dl R₁ p t f g j y w U z h F G J₁ Y u s q m hn o O _ _ _ _ _
    (fun i=> by exact_mod_cast tax_pos (w i)) (machine_v g j y w U frac b ha hr ho)
    K e m₁ data_ x
end
end Grid

end IntegerMultiplication
end Computability
end OAI
