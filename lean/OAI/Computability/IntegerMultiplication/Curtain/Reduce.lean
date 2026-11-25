import OAI.Computability.IntegerMultiplication.Curtain.Freedom

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Curtain
open Code Dusk Loom Earth Strip Strip.Dims Adic Net Net.Tensor Net.Walsh Phase Packed Haze Bits
open Matrix
variable {I J W L : Type} [Fintype J] [DecidableEq J] [Fintype W] (d : Guild J W L Motif.sigma) (R : Series W)
variable {r : Regime I} (p v : I→Tape) (K e m w U : I→ℕ) {T:I→ Type} (s : (i:I)→Series (T i))
variable (hp : Told r p) (hv : Told r v) (guard : ∀i a,a∈p i++v i→a≤Net.Shuttle.base)
variable (H : r.Has (tally ∘ K)) (n : r.Has (tally ∘ e)) (B : r.Has (tally ∘ m)) (y : r.Has (tally ∘ w))
variable (l : ∀i,1≤e i) (m0 : ∀i,m i≤K i)
variable (t : ∀ i,(s i).count*(w i+1)≤U i) (a₀ : ∀i,safe (e i) (K i)) (h : ∀i,e i≤w i+1)

-- general length variant of phase Had etc via helper theorem if desired later.
-- word packs
noncomputable section
def mint (k : ℕ) (x : Word) : Grain k := ⟨(value x : ℕ),0⟩
def table (x : Word) : Dusk.Pair :=
  (x++[false],fill false (()::ruler x))
def steal (x : Dusk.Pair) : Word :=
  (x.1.reverse.tail).reverse
@[fun_prop] theorem easy_table : Easy table := by unfold table; fun_prop
@[fun_prop] theorem easy_steal : Easy steal := by
  have h : Easy (fun x:Word=> x.tail) := by
    suffices eq : (fun x:Word=> x.tail) = (fun x=> List.casesOn (motive:=fun _=>Word) x [] fun _ u=>u) from eq ▸ Easy.listCase [] Easy.snd
    funext x; cases x <;> rfl
  exact ((Easy.fst.compose Easy.reverse).compose h).compose Easy.reverse
theorem mint_table {k} (x : Word) (e : x.length=k) : table x=Dusk.mark (mint k x) := by
  subst k
  unfold table Dusk.mark mint; dsimp only
  apply Prod.ext <;> dsimp only <;>
    apply word_inject _ _ (by simp [fill])
  · rw [value_append,trips,ZMod.val_natCast]
    have h : value x < Dusk.period x.length := by
      refine lt_of_lt_of_le (value_lt x) ?_
      have e := period_s x.length
      rw [pow_succ] at e
      have : 0 < 2^x.length := pow_pos (by decide) _
      omega
    simp [Nat.mod_eq_of_lt h]
  rw [trips,fill_eq]; simp
theorem thieve {k} x (t : x.length=k) : steal (Dusk.mark (mint k x)) = x := by
  rw [← mint_table _ t]; simp [table,steal]

-- effect at Word tape level
variable (π : (i:I) → Equiv.Perm (Fin (V K e m i)))
variable (hπ : r.Has (fun i=> Curtain.paint (π i)))
variable (hw : ∀ i,V K e m i≤w i+1)

include d R hp hv guard H n B y l m0 t a₀ h hπ hw
theorem salute (x : (i:I)→block_s p v (V K e m) i→T i→Bits.Word)
    (z : ∀ i a b,(x i a b).length=w i) :
    let P := spec p v (V K e m)
    let N i := (P i).count
    Breeze (feeK K e) r N U (together r.header (cloth P s x))
      (cloth P s (fun i=> x i ∘ induce (π i))) := by
  let g (i:I) := induce (P:=p i) (T:=v i) (π i)
  let T₁ := fun i=> x i ∘ g i
  let Y (i:I) a b := mint (w i) (x i a b)
  let h0 := spec p v (V K e m)
  let N i := (h0 i).count
  have v₁ := effect d R p v K e m w U s hp hv guard H n B y l m0 t a₀ h π hπ hw Y
  have u : r.Has (tally ∘ V K e m) := by
    let z := fun (x:Roll)=>ruler x
    have χ := hπ.ez (f:=z) (by unfold z; fun_prop)
    have e i : z (Curtain.paint (π i))=tally (V K e m i) := by simp [z,Curtain.paint,ruler,tally]
    simpa only [Function.comp_def,e] using χ
  have sta :=
    hp.station.product ((Adic.terminal (p:=2) (by decide) _ u).product hv.station)
  have c (v : (i:I)→block_s p v (V K e m) i→T i→Bits.Word)
      (z : ∀ i a b,(v i a b).length=w i) :
      Alive r N U (cloth h0 s v) := by
    apply Manifest.lives (s:=h0) _ sta
    refine ⟨6,fun i a=> ?_⟩
    have f := stripe_size (s i) (send ∘ (v i a)) (2*w i+1)
      (fun b=> show (send _).count≤_ from by change size (v i a b)≤_; rw [size_word,z])
    specialize t i
    exact f.trans (by nlinarith)
  have E :=
    map_open h0 s x table easy_table (Drive.self (n:=N) sta.1 (c x z))
  have d :=
    map_open h0 s (fun i a b=> Dusk.mark (Y i (g i a) b)) steal easy_steal
      (Drive.self (n:=N) sta.1 (shelter h0 s _ (fun i=> Y i ∘ g i) sta t))
  unfold Y at d
  simp_rw [thieve _ (z _ _ _)] at d
  simp_rw [mint_table _ (z _ _ _)] at E
  exact Spindle.Breeze.pipe (Breeze.launch E v₁.1)
    (Spindle.Breeze.pipe v₁ (Breeze.launch d v₁.1) (Drive.fetch sta.1 (shelter h0 s _ _ sta t)))
    (Drive.fetch sta.1 (c x z))
end
end Curtain

end IntegerMultiplication
end Computability
end OAI
