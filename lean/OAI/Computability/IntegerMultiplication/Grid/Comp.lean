import OAI.Computability.IntegerMultiplication.Grid.Estimate

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Grid
open Strip Dims Loom Adic Code Net Net.Walsh Haze Earth Phase Packed Axon Staff Dusk Bits Hook
open Matrix Finset
noncomputable section
variable {n f k : ℕ} (p : ℕ) (q : Fin f→Word) (b : ℕ → Grain k)
abbrev Sat := Axon.Scr (Fin f) n
-- telescope FFT
def azimuth (x: Sat (n:=n) (f:=f) → Grain k) :=
  let y := (layers n).foldl (fun a i=> effort p q b i a) x
  y ∘ reface
def aim (x:Sat (n:=n) (f:=f)→ℂ) :=
  Axon.mDFT (Qu q) (x ∘ (pixel (I:=Fin f)).symm) ∘ Axon.pix
variable (n)
def raygain (f:ℕ) := (4*amps f)^n
variable {n}
variable (odd : ∀ i, Odd (Bits.value (q i):ℕ))
include odd
theorem arp (x:Sat (n:=n) (f:=f)→ℂ) :
    ((layers n).foldl (fun a i=> spirit q i a) x ∘ reface)=Grid.aim (n:=n) q x := by
  funext i
  have hh a : Odd (Qu q a) := by
    obtain ⟨k,s⟩ := odd a; exact ⟨k,by rw [Qu,s]; push_cast; rfl⟩
  have g := Axon.use (k:=n) (Qu q) hh (x ∘ (pixel (I:=Fin f)).symm) i
  suffices e : x ∘ ⇑(pixel (I:=Fin f) (k:=n)).symm ∘ (pix (I:=Fin f) (k:=n))=x by
    rw [← show ((x ∘ ⇑(pixel (I:=Fin f) (k:=n)).symm) ∘ (pix (I:=Fin f) (k:=n)))=x from e]
    -- rewrites RHS too causing aim of composed x, simplify
    simpa only [e, Function.comp_assoc, Grid.aim,Function.comp_apply,spirit] using g -- maybe
  exact funext fun t=> congrArg x (Equiv.symm_apply_apply (pixel (I:=Fin f)) t)
theorem latitude {d B:ℝ} (d0 : 0≤d) (B0:1≤B) (d1:d≤1)
    (RD:2/(2:ℝ)^p ≤ d)
    (a : ∀ i:Fin (2^n),‖Msec p (b i)-Axon.R n (i.val:ℕ)‖≤d)
    (x: Sat (n:=n) (f:=f) → Grain k)
    (t:∀i,‖Msec p (x i)‖ ≤ B)
    (fit : (2:ℝ)^p*2*(B*raygain n f)+2 < 2^k) :
    (∀ i,‖Msec p (azimuth p q b x i)‖≤B*raygain n f) ∧
    (∀ i,‖Msec p (azimuth p q b x i) - Grid.aim q (Msec p ∘ x) i‖ ≤ d*n*(B*raygain n f)) := by
  rw [← arp q odd]
  have e := traverse p q b d0 B0 d1 a RD x t (layers n) (by simpa only [layers,List.length_ofFn])
  dsimp only at e
  simp only [layers,List.length_ofFn] at e
  exact ⟨fun t=> e.1 _,fun t=> e.2 _⟩
-- hook input correspondence selectors
variable {I : Type}
variable (P T:I→Tape) (F G J Y k p:I→ℕ)
    (o:(i:I)→Fin (F i)→Word)
    (r:(i:I)→ ℕ →Grain (k i)) {A : I→Type}
omit odd
theorem date (i:I) (x : Hook.Datum P T F G J Y k (T:=A) i)
    (v : Pin (P i) × Pin (T i)) (y:Sat (n:=Hook.altitude G J Y i) (f:=F i)) (a) :
    Hook.complete_ P T F G J Y k o (boxB k p r) (fun _=>Grid.launch) i x (v,y) a =
    azimuth (p i) (o i) (r i) (fun y=> x (v,y) a) y := by
  let B := Hook.Datum P T F G J Y k (T:=A) i
  let W := Sat (f:=F i) (n:=Ht (G i) (J i) (Y i))
  let δ := Hook.drift P T F G J Y k o (boxB k p r) (fun _=>Grid.launch) (T:=A) i
  let e0 (k) (x:W→Grain _) := effort (p i) (o i) (r i) k x
  have e (l:List (Fin (altitude G J Y i))) (x:B) (w:W):
      l.foldl (fun x i=> δ i x) x (v,w) a = l.foldl (fun x i=>e0 i x) (fun w=> x (v,w) a) w := by
    induction l generalizing x with
    | nil=>rfl
    | cons j l ih=> exact ih (δ j x)
  exact e (layers _) _ _
end
end Grid

end IntegerMultiplication
end Computability
end OAI
