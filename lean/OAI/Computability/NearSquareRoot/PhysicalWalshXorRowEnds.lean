import OAI.Computability.NearSquareRoot.PhysicalWalshXorRowData
import OAI.Computability.NearSquareRoot.CRTControlledPrefixFlatten
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask

/-! # Named row preparation and collection for a variable packed XOR window -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorWindow

open IntegerMultiplication Code Adic Strip Staff Loom Packed Controlled Controlled.PositionProgram Space XorReserve
open private volume_of_count from OAI.Computability.NearSquareRoot.CRTControlledRowPackets

private theorem store_cart {P k : ℕ} {U : Type} (u : Series U) (v : Input P k U) :
    stripe ((line 2 P).cart (line 2 k)) (fun z => strip u (v (prefixBit z.2) z.1)) = store u v := by
  rw [store,(prefixView (rfl : P+k = P+k)).packet]
  apply congrArg (stripe _)
  funext z
  exact (cell_at u v z.1 z.2).symm

private theorem price {a n u b : ℕ} (hn : 0 < n) (hb : 0 < b) (hu : u ≤ b) :
    a*(n*(2*u+2)+2)+1 ≤ 6*(a*n*b)+1 := by
  have first : n*(2*u+2) ≤ 4*(n*b) := by
    rw [Nat.mul_left_comm 4]
    exact Nat.mul_le_mul_left _ (by omega)
  have pos : 1 ≤ n*b := Nat.mul_pos hn hb
  have step := Nat.mul_le_mul_left a (show n*(2*u+2)+2 ≤ 6*(n*b) by omega)
  rw [show a*(6*(n*b)) = 6*(a*n*b) by ring] at step
  omega

/-- The head and tail programs are chosen on the whole semantic domain,
before any family of reserve guesses is introduced. -/
theorem rowEnds {X : Type} (r : Regime X) (P k : X → ℕ) (hP : Realizes r P) (hk : Realizes r k)
    {U : X → Type} (u : (x : X) → Series (U x)) (f g : (x : X) → Input (P x) (k x) (U x)) :
    ∃ (pre post : Cmd) (e : ℕ), ∀ {Y : Type} (select : Y → X) (B m Q : Y → ℕ),
      (∀ y, (u (select y)).count ≤ pack (B y) (m y)) → (∀ y, r.scale (select y) ≤ Q y) →
      (∀ y, 0 < m y) → (∀ y, payloadBits e (Q y) ≤ B y) →
      let V y := volume (P (select y)) (k (select y)) (B y) (m y)
      EffectiveBoundedTask.Runs pre V V
        (fun y => .fork (r.header (select y)) (store (u (select y)) (f (select y))))
        (beforeRows r P k hP u f ∘ select) ∧
      EffectiveBoundedTask.Runs post V V (afterRows P k u g ∘ select)
        (fun y => store (u (select y)) (g (select y))) := by
  let s x := line 2 (P x)
  let t x := line 2 (k x)
  let leaf (v : (x : X) → Input (P x) (k x) (U x)) (x : X) (z : Block 2 (P x) × Block 2 (k x)) :=
    strip (u x) (v x (prefixBit z.2) z.1)
  obtain ⟨d,rulersReady⟩ := packetRulers (Adic.terminal (p := 2) (by decide) P hP) (Adic.terminal (p := 2) (by decide) k hk)
  obtain ⟨h,headersReady⟩ := fixedHeaderCarries P hP
  let e := max d h
  let metaCost x := max (2^P x) (2^k x)*(r.scale x+1)^e
  let nested x := 2^P x*(2^k x*(2*(u x).count+2)+2)+1
  let cost x := metaCost x+nested x
  have rulers := rulersReady cost (fun x => by
    simp only [lineSize]
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (le_max_left d h))).trans (Nat.le_add_right ..))
  have heads := headersReady cost (fun x => (Nat.mul_le_mul (le_max_left ..)
    (Nat.pow_le_pow_right (by omega) (le_max_right d h))).trans (Nat.le_add_right ..))
  have sizeNested x : (afterRows P k u g x).count ≤ nested x := by
    simpa only [s,t,afterRows,nested,lineSize] using PrefixCommand.nested_size (s x) (t x) (u x)
      (fun z => g x (prefixBit z.2) z.1)
  have small x : (stripe ((s x).cart (t x)) (leaf f x)).count ≤ cost x := by
    have hx := PrefixCommand.flat_size (s x) (t x) (u x) (fun z => f x (prefixBit z.2) z.1)
    change (stripe ((s x).cart (t x)) (leaf f x)).count ≤ (s x).count*(t x).count*(2*(u x).count+2)+1 at hx
    rw [show (s x).count = 2^P x from lineSize ..,show (t x).count = 2^k x from lineSize ..] at hx
    refine hx.trans ((show _ ≤ nested x from ?_).trans (Nat.le_add_left ..))
    dsimp only [nested]
    rw [Nat.mul_assoc]
    gcongr
    omega
  have geo : ∃ E : ℕ, ∀ x, ((s x).count+1:ℝ)*((t x).count+1) ≤ (E:ℝ)*cost x := by
    refine ⟨4,fun x => ?_⟩
    simp only [s,t,lineSize]
    have hs := Nat.two_pow_pos (P x)
    have ht := Nat.two_pow_pos (k x)
    have area : 2^P x*2^k x ≤ nested x := by
      dsimp only [nested]
      have hx := Nat.le_mul_of_pos_right (2^k x) (by omega : 0 < 2*(u x).count+2)
      exact (Nat.mul_le_mul_left _ (hx.trans (Nat.le_add_right ..))).trans (Nat.le_succ _)
    exact_mod_cast (calc
      (2^P x+1)*(2^k x+1) ≤ (2*(2^P x))*(2*(2^k x)) := Nat.mul_le_mul (by omega) (by omega)
      _ = 4*(2^P x*2^k x) := by ring
      _ ≤ 4*cost x := Nat.mul_le_mul_left _ (area.trans (Nat.le_add_left ..)))
  have build := boundedOfCarries (prepareRowPackets s t (leaf f) rulers heads geo (volume_of_count small))
  have finish := boundedOfCarries (collectRowPackets s t (leaf g)
    (fun x => by exact_mod_cast (show 1 ≤ cost x from (Nat.succ_le_succ (Nat.zero_le _)).trans (Nat.le_add_left ..)))
    (volume_of_count (fun x => (sizeNested x).trans (Nat.le_add_left ..))))
  have build' := build.conform (fun _ => rfl) (fun _ => rfl) (fun x => congrArg (Tree.fork (r.header x)) (store_cart (u x) (f x))) (fun _ => rfl)
  have finish' := finish.conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun x => store_cart (u x) (g x))
  obtain ⟨pre,runPre⟩ := build'
  obtain ⟨post,runPost⟩ := finish'
  refine ⟨pre,post,e,?_⟩
  intro Y select B m Q fits scale positive reserve V
  have cover (y : Y) : cost (select y)+1 ≤ 8*(V y+1) := by
    have metaBound : metaCost (select y) ≤ V y := metadata_le_volume (scale y) (positive y) (reserve y)
    have rowsBound := price (a := 2^P (select y)) (Nat.two_pow_pos (k (select y)))
      (Nat.mul_pos (Nat.two_pow_pos (B y)) (positive y)) (fits y)
    have volume_eq : 2^P (select y)*2^k (select y)*pack (B y) (m y) = V y := by
      dsimp only [V,XorReserve.volume,XorReserve.pack]
      rw [pow_add,pow_add]; ring
    change nested (select y) ≤ 6*(2^P (select y)*2^k (select y)*pack (B y) (m y))+1 at rowsBound
    rw [volume_eq] at rowsBound
    change metaCost (select y)+nested (select y)+1 ≤ 8*(V y+1)
    omega
  exact ⟨((show EffectiveBoundedTask.Runs pre cost cost _ _ from runPre).on select).bound 8 8 cover cover,
    ((show EffectiveBoundedTask.Runs post cost cost _ _ from runPost).on select).bound 8 8 cover cover⟩

end PhysicalWalsh.XorWindow

end NearSquareRoot
end Computability
end OAI
