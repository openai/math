import OAI.Computability.NearSquareRoot.CRTControlledRepair
import OAI.Computability.IntegerMultiplication.Code.Pace

/-! # Packed XOR of a computed Boolean control vector

The virtual chunk encodes one Boolean per segment and has zero in every other
position. A polynomial-time program constructs its actual P192 badge. Supplying
this program to the two-chunk row operation gives simultaneous XOR at the
designated target bits, preserving all other address fields.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Adic
open IntegerMultiplication.Packed IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
open IntegerMultiplication.Loom

def zeroDigits (t : Tally) : Raw 2 := t.map (fun _ => (0 : Fin 2))

def maskDigit (b : Bool) : Fin 2 := if b then 1 else 0

def maskBadge (v : Tally × Tally × List Bool) : Raw 2 :=
  Packed.flatten_ (zeroDigits v.1 ++ [0],
    v.2.2.map (fun b => zeroDigits v.2.1 ++ zeroDigits v.1 ++ [maskDigit b]), zeroDigits v.2.1)

theorem poly_maskBadge : Poly maskBadge := by
  have zd : Easy zeroDigits := by unfold zeroDigits; fun_prop
  have d : Easy maskDigit := Easy.finite maskDigit
  let part := fun v : Raw 2 × Bool => v.1 ++ [maskDigit v.2]
  have p : Easy part := by unfold part; fun_prop
  let input := fun v : Tally × Tally × List Bool => (zeroDigits v.2.1 ++ zeroDigits v.1, v.2.2)
  have setup : Easy input := by unfold input; fun_prop
  have body := setup.poly.compose (Poly.push [] false p.poly)
  let head := fun v : Tally × Tally × List Bool => zeroDigits v.1 ++ [0]
  let tail := fun v : Tally × Tally × List Bool => zeroDigits v.2.1
  have h : Easy head := by unfold head; fun_prop
  have t : Easy tail := by unfold tail; fun_prop
  exact (h.poly.pair (body.pair t.poly)).compose Packed.easy_flat.poly


private def zeroBlock : (n : ℕ) → Block 2 n
  | 0 => ()
  | n+1 => Adic.head 0 (zeroBlock n)

private theorem most_zeroBlock (n : ℕ) : most (zeroBlock n) = zeroDigits (tally n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 0 :: most (zeroBlock n) = _
    rw [ih]
    simp [zeroDigits, tally, List.replicate_succ]

/-- The low-order bit of each segment carries its corresponding external control. -/
def controlMask (H L : ℕ) {i : ℕ} (b : Fin i → Bool) : Queue H L i :=
  ((zeroBlock H,0), fun j => (zeroBlock L,zeroBlock H,maskDigit (b j)), zeroBlock L)

theorem badge_controlMask (H L : ℕ) {i : ℕ} (b : Fin i → Bool) :
    badge (controlMask H L b) = maskBadge (tally H, tally L, List.ofFn b) := by
  rw [Packed.restored]
  unfold maskBadge
  apply congrArg Packed.flatten_
  apply Prod.ext
  · change most ((flag H).cast (zeroBlock H, 0)) = _
    rw [flag_word, most_zeroBlock]
  · apply Prod.ext
    · change List.ofFn (fun j => most ((furrow H L).cast ((controlMask H L b).2.1 j))) = _
      rw [List.map_ofFn]
      apply congrArg List.ofFn
      funext j
      rw [furrow_word, Packed.guard, tile_most]
      simp only [controlMask, most_zeroBlock, Function.comp_apply]
    · exact most_zeroBlock L

/-- Broadcast an arbitrary per-prefix control vector into the guarded mask at the
local regime's polynomial budget. The controls are listed in segment order. -/
theorem controlMaskTrace {X : Type} {r : Regime X} {A : X → Type} {s : (x : X) → Series (A x)}
    (H L i : X → ℕ) (shape : r.Has fun x => signs (H x) (L x) (i x))
    (controls : (x : X) → A x → Fin (i x) → Bool)
    (ready : Strip.Trace r s (fun x a => send (List.ofFn (controls x a)))) :
    Strip.Trace r s (fun x a => send (badge (controlMask (H x) (L x) (controls x a)))) := by
  let header (x : X) (a : A x) := send (List.ofFn (controls x a))
  let rr := onboard r header ready.meter
  apply ready.tune
  have dim : rr.Has (fun y : Sigma A => signs (H y.1) (L y.1) (i y.1)) :=
    onboard_small header ready.meter _ shape
  have ctrl : rr.Has (fun y : Sigma A => List.ofFn (controls y.1 y.2)) :=
    onboard_hat header ready.meter
  have hh := dim.ez (Easy.fst : Easy (fun v : Packed.Dim => v.1))
  have hl := dim.ez (Easy.snd.compose Easy.fst : Easy (fun v : Packed.Dim => v.2.1))
  simp only [badge_controlMask]
  exact (hh.pair (hl.pair ctrl)).thenDo poly_maskBadge

/-- Toggle the one addressed bit per segment using Boolean XOR. -/
def maskTarget {H L i : ℕ} (b : Fin i → Bool) (y : Queue H L i) : Queue H L i :=
  (y.1, fun j => ((y.2.1 j).1, (y.2.1 j).2.1,
    maskDigit (Bool.xor (title (y.2.1 j).2.2) (b j))), y.2.2)

private theorem other_maskDigit (a : Fin 2) (b : Bool) :
    Packed.other a (maskDigit b) = maskDigit (Bool.xor (title a) b) := by
  fin_cases a <;> cases b <;> decide

theorem guide_controlMask {H L i : ℕ} (b : Fin i → Bool) (y : Queue H L i) :
    Packed.guide (controlMask H L b) y = maskTarget b y := by
  simp [Packed.guide, controlMask, maskTarget, other_maskDigit]

theorem rowIdeal_controlMask {H L i : ℕ} (b : Fin i → Bool) (yz : Row H L i) :
    rowIdeal (controlMask H L b) yz = (maskTarget b yz.1,yz.2) :=
  congrArg (fun v => (v, yz.2)) (guide_controlMask b yz.1)

theorem rowIdeal_controlMask_symm {H L i : ℕ} (b : Fin i → Bool) (yz : Row H L i) :
    (rowIdeal (controlMask H L b)).symm yz = (maskTarget b yz.1,yz.2) :=
  rowIdeal_controlMask b yz

/-- The two-chunk traversal and actual radix repair implement the Boolean XOR
on the selected bits of the first chunk, under computed per-prefix controls. -/
theorem maskedXorStage {X : Type} {r : Regime X} {l : X → ℕ} (H L i : X → ℕ)
    (P G S : X → Tape) (ρ : ℝ) {U : X → Type} (u : (x : X) → Series (U x))
    (b : (x : X) → Pin (P x) → Fin (i x) → Bool)
    (hc : r.Has (tally ∘ extent H L i))
    (shape : r.Has fun x => Packed.signs (H x) (L x) (i x))
    (sparse : ∀ x, (3 * extent H L i x + 1) * (32 * i x) ≤ 2 ^ width (H x) (L x))
    (hp : Told r P) (hg : Told r G) (hs : Told r S)
    (guard : ∀ x j, j ∈ P x ++ G x ++ S x → j ≤ Net.Shuttle.base)
    (sw : RectInterchange r (extent H L i) ρ)
    (ready : Strip.Trace r (fun x => layout (P x)) (fun x a => send (List.ofFn (b x a))))
    (z : ∀ x, (u x).count ≤ l x) (hr : 0 ≤ ρ)
    (f : (x : X) → RotationAddress H L i P G S x → U x → Bead) :
    let rows := rotationLayout H L i P G S
    Breeze (Spindle.modes (extent H L i) (τ := ρ)) r (fun x => (rows x).count) l
      (together r.header (cloth rows u f)) (cloth rows u fun x a =>
        f x (a.1, maskTarget (b x a.1) a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2)) := by
  have move := rowIdealStage H L i P G S ρ u (fun x p => controlMask (H x) (L x) (b x p))
    hc shape sparse hp hg hs guard sw (controlMaskTrace H L i shape b ready) z hr f
  simpa only [rowIdeal_controlMask_symm] using move

end Controlled

end NearSquareRoot
end Computability
end OAI
