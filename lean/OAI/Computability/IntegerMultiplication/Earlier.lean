import OAI.Computability.IntegerMultiplication.Strip.Fleet
import OAI.Computability.IntegerMultiplication.Adic.Suffix

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Code
variable {I : Type}
theorem Station.adapt {P S : I→Type} {r : Regime I} (x : (i:I)→P i→Tree)
    (h : Dom (fun i:Sigma P => r.scale i.1) (fun i => (x i.1 i.2).count))
    (s : (i:I)→Series (S i)) (g : Station r s) :
    Station (onboard r x h) (fun a:Sigma P => s a.1) := by
  refine ⟨fun a => g.1 a.1, ?_⟩
  apply Rip.chain (q := (onboard r x h).header)
    (Rip.header (fun a => g.1 a.1) (onboard_small _ h _ Regime.self : (onboard r x h).Small _)) _
  exact g.2.pull _
end Strip

namespace Adic
open IntegerMultiplication.Port Strip Code
open Strip.Fleet
variable {I : Type} {p : ℕ} [NeZero p] (hp : 2 ≤ p)
variable {r : Regime I} {l : I→ℕ}
variable (j : I→ℕ) (h : r.Has (tally ∘ j))
include hp h
omit [NeZero p] h in
private theorem positive (s:ℕ) : 1 ≤ p^s := Nat.one_le_pow _ _ (by omega)
-- no prefix
theorem within {S : I→Type} {s : (i:I)→Series (S i)}
    (g : Station r s)
    (v : (i:I)→Block p (j i) × S i→Tree) (m : Manifest _ l v) (a : Span p) :
    Fleet r l (stations j s) (stations j s) v
      (fun i x => v i ((sweep a (j i)).symm x.1,x.2)) := by
  unfold Fleet
  simp only [stations,Series.count_cart,lineSize]
  apply sail hp _ _ h g
  have e := Manifest.lives m ((terminal hp j h).product g)
  unfold luggage
  simpa only [Series.count_cart,lineSize] using e

theorem offset {S : I→Type} {s : (i:I)→Series (S i)}
    (g : Station r s)
    (sig : I→Raw p) (t : (i:I)→Tower p (j i)) (e : ∀ i,Holds (j i) (sig i) (t i))
    (q : r.Has sig)
    (v : (i:I)→Block p (j i) × S i→Tree) (m : Manifest _ l v) (a : Pinpoint p) :
    Fleet r l (stations j s) (stations j s) v
      (fun i x => v i ((glide (a.stamp (j i)*t i)).symm x.1,x.2)) := by
  unfold Fleet; simp only [stations,Series.count_cart,lineSize]
  apply takeOff hp _ _ h g a sig t e q
  have z := m.lives ((terminal hp j h).product g)
  unfold luggage
  simpa only [Series.count_cart,lineSize] using z

/-- At earlier axis choose an offset at each address (here a rational multiple of
axis value), deliver to later through unchanged dynamic gap. -/
theorem along {G S : I→Type} {g : (i:I)→Series (G i)} {s : (i:I)→Series (S i)}
    (jG : Station r g) (jS : Station r s)
    (v : (i:I)→Block p (j i) × G i × Block p (j i) × S i → Tree) (m : Manifest _ l v)
    (a : Pinpoint p) :
    Fleet r l (cartS (fun i => line p (j i)) (cartS g (stations j s)))
      (cartS (fun i => line p (j i)) (cartS g (stations j s))) v
      (fun i x => v i (x.1,x.2.1,(glide (a.stamp (j i)*index p (j i) x.1)).symm x.2.2.1,x.2.2.2)) := by
  let X i := Block p (j i)
  let t i := line p (j i)
  have z := terminal hp j h
  let sig := (fun (i:I) (x:X i) => send (least x))
  obtain ⟨M,u⟩ : ∃ C : ℕ,∀ d : Fin p,size d+1 ≤ C :=
    ⟨∑ d:Fin p,(size d+1),fun d => Finset.single_le_sum (f:=fun d:Fin p=>size d+1)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)⟩
  have hj : Dom r.scale j := (Regime.Small.extent (k:=send ∘ tally ∘ j) h).mono
    (fun i => by change _ ≤ size (tally _); rw [size_tally,tally_length]; omega)
  let ss := fun (x:Sigma X) => r.scale x.1
  have hs : Dom ss (fun x => (sig x.1 x.2).count) := (((Dom.const ss M).mul
    (hj.map Sigma.fst)).add (Dom.const ss 1)).mono (fun i => by
      change size _ ≤ M*j i.1+1; simpa using raw_size _ _ u (least i.2))
  apply Fleet.guide z (jG.product (z.product jS)) m sig hs
    (marked hp j h (fun _ => lineSize .. |>.ge))
  -- Regime I2 header with sig
  let r' := onboard r sig hs
  let f (i:Sigma X) (x : G i.1 × Block p (j i.1) × S i.1) := v i.1 (i.2,x)
  have gT := jG.adapt sig hs g -- parameter order dot
  have hz := jS.adapt sig hs s
  have ht := z.adapt sig hs t
  let m' : Manifest _ (fun i:Sigma X => l i.1) f :=
    Manifest.localize (s:=fun i x y => v i (x,y)) m
  apply Fleet.wind gT (ht.product hz) m'
  let H := fun i:Sigma X => g i.1
  let Y := Sigma (fun i:Sigma X => G i.1)
  let t' (i:Y) := j i.1.1
  let r'' := r'.pull (Sigma.fst : Y → Sigma X)
  have hh : r''.Has (tally ∘ t') :=
    Task.BT.map (onboard_small sig hs _ h) (Sigma.fst : Y → Sigma X)
  have okSig : r''.Has (fun i:Y => least i.1.2) :=
    Task.BT.map (onboard_hat (r:=r) sig hs) (Sigma.fst : Y → Sigma X)
  have m'' := Manifest.localize (s:=fun (i:Sigma X) x y => f i (x,y)) m'
  exact offset hp t' hh (s:=fun (x:Y) => s x.1.1) (hz.pull _) (fun i:Y => least i.1.2)
    (fun i:Y => index p (t' i) i.1.2) (fun i => Holds.std _) okSig _ m'' a
end Adic

end IntegerMultiplication
end Computability
end OAI
