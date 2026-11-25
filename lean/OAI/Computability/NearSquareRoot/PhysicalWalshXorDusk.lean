import OAI.Computability.NearSquareRoot.PhysicalWalshXorGate
import OAI.Computability.NearSquareRoot.PhysicalWalshXorFrames
import OAI.Computability.NearSquareRoot.PhysicalWalshXorWindow
import OAI.Computability.NearSquareRoot.PhysicalWalshSwapCodec

/-! # An aligned XOR on the original flat tape of fixed-point records -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorWindow
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Adic
open IntegerMultiplication.Strip IntegerMultiplication.Staff IntegerMultiplication.Loom
open IntegerMultiplication.Packed NearSquareRoot.Space NearSquareRoot.Controlled
open NearSquareRoot.Controlled.PositionProgram XorReserve XorSweep PhysicalWalshSwapCodec

/-- Physical rulers used before and after the window program. -/
def duskHeader (h : Tree) (n s w : ℕ) :=
  Tree.fork (send (tally n,tally (s*(2*(w+1))))) (.fork h (send (tally (n*s),tally (2*(w+1)))))

noncomputable def duskRow {P L S w : ℕ} (x : ℕ → Dusk.Grain w) :
    Input P (3*L) (Fin (S*(2*(w+1)))) := fun bits pref =>
  payloadBeads S x (wordAddress L 1 (number pref) 0 bits)

private theorem ordered {A : Type} [Codec A] {K : ℕ} (f : Block 2 K → Tree) (y : ℕ → A)
    (eqn : ∀ a, f a = send (y (number a))) :
    stripe (line 2 K) f = send ((List.range (2^K)).map y) := by
  let record (i:Fin (2^K)) := y i.val
  have same : f = fun a => send ((record ∘ flatAddress 2 K) a) := by
    funext a; simpa only [record,Function.comp_apply,flatAddress_val] using eqn a
  rw [same,stripe_eq',line_tab_addresses]
  congr 1
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range,record]

theorem store_row {P L S w : ℕ} (x : ℕ → Dusk.Grain w) :
    store (Series.natural (S*(2*(w+1)))) (duskRow (P:=P) (L:=L) x) =
      send ((List.range (2^(P+3*L))).map (payload S x)) := by
  apply ordered
  intro a
  obtain ⟨⟨pref,b⟩,rfl⟩ := (prefixView (rfl : P+3*L=P+3*L)).cast.surjective a
  rw [cell_at,duskRow,strip_payload,wordAddress_prefix]
  simp

private theorem read_payload {L S w : ℕ} (hs : 0 < S) (x : ℕ → Dusk.Grain w) (n : ℕ) :
    payload S (x ∘ directedRead L S) n = payload S x (directedRead L 1 n) := by
  have eqn : x ∘ directedRead L S = fun j => x (directedRead L 1 (j/S)*S+j%S) := by
    funext j; simp [directedRead_window,Nat.mod_one]
  rw [eqn,payload_map hs]

theorem store_result {P L S w : ℕ} (hs : 0 < S) (x : ℕ → Dusk.Grain w) :
    store (Series.natural (S*(2*(w+1)))) (duskRow (P:=P) (L:=L) x ∘ directed (gate L)) =
      send ((List.range (2^(P+3*L))).map (payload S (x ∘ directedRead L S))) := by
  apply ordered
  intro a
  obtain ⟨⟨pref,b⟩,rfl⟩ := (prefixView (rfl : P+3*L=P+3*L)).cast.surjective a
  rw [cell_at]; simp only [Function.comp_apply,duskRow,strip_payload,wordAddress_directed,wordAddress_prefix,mul_one,
    Fin.val_zero,Nat.add_zero,read_payload hs]

/-- Execute the aligned native XOR on a flat Dusk record stream. The low
spectator stride is an arbitrary positive integer. Its packed lower field
supplies the polynomial workspace for the native instruction interpreter. -/
theorem boundedDuskOn {ρ : ℝ} (hρ : 1/2 < ρ)
    {X : Type} {r : Regime X} (P L S w : X → ℕ) (hP : Realizes r P) (hL : Realizes r L) :
    ∃ D : ℕ, ∀ {Y : Type} (select : Y → X) (B m Q factor : Y → ℕ),
      (∀ y, S (select y)*(2*(w (select y)+1)) = XorReserve.pack (B y) (m y)) → (∀ y, r.scale (select y) ≤ Q y) →
      (∀ y, 0 < m y) → (∀ y, payloadBits D (Q y) ≤ B y) →
      (∀ y, 2*Spindle.modes (fun x => 3*L x) (τ:=ρ) (select y) ≤ factor y) →
      (∀ y, factor y ≤ 2^P (select y)) → ∀ xrow : (y:Y) → ℕ → Dusk.Grain (w (select y)),
      let n y := 2^(P (select y)+3*L (select y))
      let V y := volume (P (select y)) (3*L (select y)) (B y) (m y)
      BoundedTask (fun y => (4+3*guardWidth (3*L (select y)))*(V y*(factor y+1))+1) V
        (fun y => .fork (duskHeader (r.header (select y)) (n y) (S (select y)) (w (select y)))
          (send ((List.range (n y*S (select y))).map (Dusk.mark ∘ xrow y))))
        (fun y => send ((List.range (n y*S (select y))).map
          (Dusk.mark ∘ xrow y ∘ directedRead (L (select y)) (S (select y))))) := by
  let series x := Series.natural (S x*(2*(w x+1)))
  obtain ⟨D,run⟩ := boundedGateOn hρ P (fun x => 3*L x) hP ((Realizes.fix 3).times hL) series
  refine ⟨D,fun select B m Q factor sizes scale pos low rate high xrow => ?_⟩
  intro n V
  have ss y : 0 < S (select y) := by
    have h : 0 < XorReserve.pack (B y) (m y) := Nat.mul_pos (Nat.two_pow_pos _) (pos y)
    rw [← sizes y] at h
    exact Nat.pos_of_mul_pos_right h
  have budget y : V y = n y*(S (select y)*(2*(w (select y)+1))) := by
    rw [sizes]
    simp only [V,n,XorReserve.volume,XorReserve.pack,pow_add,mul_assoc]
  have io y : (n y*S (select y)+1)*(w (select y)+1) ≤ V y := by
    rw [budget]
    have h := Nat.mul_pos (Nat.two_pow_pos (P (select y)+3*L (select y))) (ss y)
    change 0 < n y*S (select y) at h
    have subs := Nat.mul_le_mul_right (w (select y)+1) (show n y*S (select y)+1 ≤ (n y*S (select y))*2 by omega)
    simpa only [Nat.mul_assoc] using subs
  have time y : V y ≤ (4+3*guardWidth (3*L (select y)))*(V y*(factor y+1))+1 :=
    ((Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans (Nat.le_mul_of_pos_left _ (by omega))).trans (Nat.le_add_right ..)
  let out y := xrow y ∘ directedRead (L (select y)) (S (select y))
  have first := packOrdinal (fun y => w (select y)) (fun y => S (select y)) n xrow (fun _ => Nat.two_pow_pos _) ss
  have last := unpackOrdinal (fun y => w (select y)) (fun y => S (select y)) n out (fun _ => Nat.two_pow_pos _) ss
  have full := run select B m Q factor (fun y => by simpa [series] using sizes y) scale pos low rate high
  have core := full.on (fun y => ⟨y,duskRow (P:=P (select y)) (L:=L (select y)) (S:=S (select y)) (xrow y)⟩)
  apply threeKeys time (first.mono io io) _ (last.mono io io)
  apply core.conform (fun _ => rfl) (fun _ => rfl)
  · intro y; simp only [series,store_row]; rfl
  · intro y
    dsimp only
    rw [show 3*L (select y)/3=L (select y) by omega]
    exact store_result (ss y) (xrow y)

end PhysicalWalsh.XorWindow

end NearSquareRoot
end Computability
end OAI
