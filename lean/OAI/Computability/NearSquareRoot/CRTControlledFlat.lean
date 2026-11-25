import OAI.Computability.NearSquareRoot.CRTControlledWordSlots
import OAI.Computability.NearSquareRoot.CRTControlledResidues
import OAI.Computability.IntegerMultiplication.Curtain.Scanner

/-! # Controlled XOR on contiguous slices of a single binary address -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

open IntegerMultiplication IntegerMultiplication.Packed IntegerMultiplication.Adic
open IntegerMultiplication.Code IntegerMultiplication.Loom IntegerMultiplication.Strip
open IntegerMultiplication.Strip.Dims

noncomputable section

/-- Dropping the high partial group and reserving one leading segment gives
the largest whole guarded width available above the residual low bits. -/
theorem residueCap {N G r : ℕ} (hg : 0 < G) (fit : r+G ≤ N) :
    cap (slots N G r) (G-1) 0 = ((N-r)/G)*G := by
  have full : 1 ≤ (N-r)/G := (Nat.le_div_iff_mul_le hg).2 (by omega)
  unfold cap slots width
  rw [Nat.sub_add_cancel full, Nat.sub_add_cancel hg]

theorem residueCap_fits {N G r : ℕ} (hg : 0 < G) (fit : r+G ≤ N) :
    r + cap (slots N G r) (G-1) 0 ≤ N := by
  rw [residueCap hg fit]
  have h := Nat.div_mul_le_self (N-r) G
  omega

/-- Concatenate five binary fields in MSB order, in the physical stock order. -/
def flatSpan (p h g s : ℕ) : Adopt (stock 2 (field 2 p) (field 2 g) (field 2 s) h)
    (line 2 (p+h+g+h+s)) :=
  let a := tile 2 h s
  let b := ((Adopt.same _).split a).thenDo (tile 2 g (h+s))
  let c := ((Adopt.same _).split b).thenDo (tile 2 h (g+(h+s)))
  (((Adopt.same _).split c).thenDo (tile 2 p (h+(g+(h+s))))).thenDo
    (castN 2 _ _ (by omega))

theorem flatSpan_most {p h g s : ℕ} (a : SpanKey (field 2 p) (field 2 g) (field 2 s) (Block 2 h)) :
    most ((flatSpan p h g s).cast a) =
      most a.1 ++ most a.2.1 ++ most a.2.2.1 ++ most a.2.2.2.1 ++ most a.2.2.2.2 := by
  change most ((castN 2 _ _ _).cast ((tile 2 _ _).cast (a.1,(tile 2 _ _).cast
    (a.2.1,(tile 2 _ _).cast (a.2.2.1,(tile 2 h s).cast a.2.2.2)))) ) = _
  rw [castN_most, tile_most, tile_most, tile_most, show a.2.2.2 = (a.2.2.2.1, a.2.2.2.2) from rfl,
    tile_most]
  simp only [List.append_assoc]

theorem flatSpan_least {p h g s : ℕ} (a : SpanKey (field 2 p) (field 2 g) (field 2 s) (Block 2 h)) :
    least ((flatSpan p h g s).cast a) =
      least a.2.2.2.2 ++ least a.2.2.2.1 ++ least a.2.2.1 ++ least a.2.1 ++ least a.1 := by
  simp only [least, flatSpan_most, List.reverse_append, List.append_assoc]

/-- Apply a masked XOR to the first active slice of one flat binary address. -/
def flatMask {H i : ℕ} (p g s : ℕ) (b : Block 2 p → Fin i → Bool)
    (y : Block 2 (p+cap i H 0+g+cap i H 0+s)) : Block 2 (p+cap i H 0+g+cap i H 0+s) :=
  let view := flatSpan p (cap i H 0) g s
  let a := view.cast.symm y
  view.cast (a.1,maskBlock (b a.1) a.2.1,a.2.2.1,a.2.2.2.1,a.2.2.2.2)

theorem flatMask_parts {H i : ℕ} (p g s : ℕ) (b : Block 2 p → Fin i → Bool)
    (y : Block 2 (p+cap i H 0+g+cap i H 0+s)) :
    let a := (flatSpan p (cap i H 0) g s).cast.symm y
    least (flatMask p g s b y) = least a.2.2.2.2 ++ least a.2.2.2.1 ++ least a.2.2.1 ++
      least (maskBlock (b a.1) a.2.1) ++ least a.1 := flatSpan_least _

/-- Coordinates below and above the target slice are copied. Inside the slice the
guarded XOR acts at local offsets `j*(H+1)` using segment `j.rev`. -/
theorem flatMask_slot {H i : ℕ} (p g s : ℕ) (b : Block 2 p → Fin i → Bool)
    (y : Block 2 (p+cap i H 0+g+cap i H 0+s)) (n : ℕ) :
    let a := (flatSpan p (cap i H 0) g s).cast.symm y
    let start := s + cap i H 0 + g
    let localBit := n-start
    (least (flatMask p g s b y))[n]? =
      if h : start ≤ n ∧ localBit / (H+1) < i ∧ localBit % (H+1) = 0 then
        (least y)[n]?.map (fun d => maskDigit (Bool.xor (title d)
           (b a.1 (⟨localBit/(H+1),h.2.1⟩ : Fin i).rev)))
      else (least y)[n]? := by
  let v := flatSpan p (cap i H 0) g s
  let a := v.cast.symm y
  let low := least a.2.2.2.2 ++ least a.2.2.2.1 ++ least a.2.2.1
  let u := a.2.1
  have lowLen : low.length = s + cap i H 0 + g := by simp [low, Nat.add_assoc]
  have inp : least y = low ++ (least u ++ least a.1) := by
    have e := flatSpan_least a
    change least (v.cast (v.cast.symm y)) = _ at e
    rw [Equiv.apply_symm_apply] at e
    simpa only [low, u, List.append_assoc] using e
  have out : least (flatMask p g s b y) = low ++ (least (maskBlock (b a.1) u) ++ least a.1) := by
    simpa only [low, u, List.append_assoc] using flatMask_parts p g s b y
  dsimp only
  rw [inp,out]
  by_cases hlow : n < low.length
  · rw [dite_eq_right (fun h => (Nat.not_le_of_gt (lowLen ▸ hlow)) h.1)]
    simp only [List.getElem?_append_left hlow]
  · rw [List.getElem?_append_right (Nat.le_of_not_gt hlow), List.getElem?_append_right (Nat.le_of_not_gt hlow)]
    rw [lowLen]
    let m := n-(s+cap i H 0+g)
    have hstart : s+cap i H 0+g ≤ n := by omega
    by_cases hmid : m < cap i H 0
    · rw [List.getElem?_append_left (l₁:=least (maskBlock (b a.1) u)) (by simpa only [length'] using hmid),
        List.getElem?_append_left (l₁:=least u) (by simpa only [length'] using hmid), least_maskBlock]
      split_ifs <;> first | rfl | contradiction | tauto
    · have hq : ¬ m/(H+1) < i := by
        intro h
        have lt := (Nat.div_lt_iff_lt_mul (by omega : 0 < H+1)).mp h
        have bound : i*(H+1) ≤ cap i H 0 := by simp [cap,width,Nat.succ_mul]
        exact hmid (lt.trans_le bound)
      rw [dite_eq_right (fun h => hq h.2.1)]
      change (least (maskBlock (b a.1) u) ++ least a.1)[m]? = (least u ++ least a.1)[m]?
      rw [List.getElem?_append_right (by simpa only [length'] using Nat.le_of_not_gt hmid),
        List.getElem?_append_right (by simpa only [length'] using Nat.le_of_not_gt hmid)]
      simp only [length']

/-- A finite selector reads a bit of the physical prefix in little-endian order. -/
def prefixBit {p : ℕ} (a : Block 2 p) (j : Fin p) : Bool :=
  title ((least a)[j.val]'(by simpa only [length'] using j.isLt))

theorem prefixBit_list {p : ℕ} (a : Block 2 p) :
    List.ofFn (prefixBit a) = (least a).map title := by
  apply List.ext_getElem
  · simp
  · intro j hj hk
    simp [prefixBit]

/-- Absolute position of a source bit embedded in the high prefix. -/
def flatPrefixPort (p h g s : ℕ) (j : Fin p) : Fin (p+h+g+h+s) :=
  ⟨s+h+g+h+j.val, by have := j.isLt; omega⟩

theorem flatPrefixPort_bit (p h g s : ℕ) (y : Block 2 (p+h+g+h+s)) (j : Fin p) :
    prefixBit ((flatSpan p h g s).cast.symm y).1 j = prefixBit y (flatPrefixPort p h g s j) := by
  let v := flatSpan p h g s
  let a := v.cast.symm y
  let low := least a.2.2.2.2 ++ least a.2.2.2.1 ++ least a.2.2.1 ++ least a.2.1
  have hl : low.length = s+h+g+h := by simp [low, Nat.add_assoc]
  have e := flatSpan_least a
  change least (v.cast (v.cast.symm y)) = low ++ least a.1 at e
  rw [Equiv.apply_symm_apply] at e
  have read : (least y)[(flatPrefixPort p h g s j).val]? = (least a.1)[j.val]? := by
    rw [e,List.getElem?_append_right (by dsimp [flatPrefixPort]; omega), hl]
    simp [flatPrefixPort]
  have hsrc : j.val < (least a.1).length := by simp
  have habs : (flatPrefixPort p h g s j).val < (least y).length := by
    simp
  rw [List.getElem?_eq_getElem habs, List.getElem?_eq_getElem hsrc] at read
  exact congrArg title (Option.some.inj read).symm

/-- Execute a guarded XOR on the physical flat word with a computed vector of
controls for each setting of its high prefix. -/
theorem flatControlledStage {X : Type} {r : Regime X} {l : X → ℕ} (H i p g s : X → ℕ)
    (ρ : ℝ) {U : X → Type} (u : (x : X) → Series (U x))
    (b : (x : X) → Block 2 (p x) → Fin (i x) → Bool)
    (hc : r.Has (tally ∘ extent H (fun _ => 0) i))
    (shape : r.Has fun x => Packed.signs (H x) 0 (i x))
    (sparse : ∀ x, (3 * cap (i x) (H x) 0 + 1) * (32 * i x) ≤ 2 ^ width (H x) 0)
    (hp : r.Has (tally ∘ p)) (hg : r.Has (tally ∘ g)) (hs : r.Has (tally ∘ s))
    (sw : RectInterchange r (extent H (fun _ => 0) i) ρ)
    (ctrl : Strip.Trace r (fun x => line 2 (p x)) (fun x a => send (List.ofFn (b x a))))
    (z : ∀ x, (u x).count ≤ l x) (hr : 0 ≤ ρ)
    (f : (x : X) → Block 2 (p x + cap (i x) (H x) 0 + g x + cap (i x) (H x) 0 + s x) → U x → Bead) :
    let n := extent H (fun _ => 0) i
    let flat x := line 2 (p x + n x + g x + n x + s x)
    Breeze (Spindle.modes n (τ := ρ)) r (fun x => (flat x).count) l
      (together r.header (cloth flat u f))
      (cloth flat u fun x a => f x (flatMask (p x) (g x) (s x) (b x) a)) := by
  let n := extent H (fun _ => 0) i
  let P x := field 2 (p x)
  let G x := field 2 (g x)
  let S x := field 2 (s x)
  let raw x := stock 2 (P x) (G x) (S x) (n x)
  let flat x := line 2 (p x + n x + g x + n x + s x)
  let view x := flatSpan (p x) (n x) (g x) (s x)
  have allBits (x : X) (j : ℕ) (e : j ∈ P x ++ G x ++ S x) : j ≤ Net.Shuttle.base := by
    simp only [List.mem_append] at e
    rcases e with (h|h)|h
    all_goals exact ((ivory (p := 2) (by decide) j h).2).trans Net.Shuttle.base_large.le
  have w := maskedBlockStage H i P G S ρ u b hc shape sparse
    (Told.carrier (q := 2) (by decide) p hp) (Told.carrier (q := 2) (by decide) g hg)
    (Told.carrier (q := 2) (by decide) s hs) allBits sw ctrl z hr
    (fun x a => f x ((view x).cast a))
  have transfer (k : (x : X) → Block 2 (p x + n x + g x + n x + s x) → U x → Bead) :
      cloth flat u k = cloth raw u (fun x a => k x ((view x).cast a)) := by
    funext x
    exact (view x).packet _
  dsimp only
  change Breeze _ r (fun x => (flat x).count) l (together r.header (cloth flat u f))
    (cloth flat u fun x a => f x (flatMask (p x) (g x) (s x) (b x) a))
  rw [← funext (fun x => (view x).cost), transfer f, transfer]
  convert w using 1
  apply congrArg (cloth raw u)
  funext x a
  unfold flatMask
  change f x ((view x).cast (((view x).cast.symm ((view x).cast a)).1,
    maskBlock (b x (((view x).cast.symm ((view x).cast a)).1)) (((view x).cast.symm ((view x).cast a)).2.1),
    ((view x).cast.symm ((view x).cast a)).2.2)) = _
  rw [Equiv.symm_apply_apply]

/-- The raw P192 address stream for a flat word, with per-segment Boolean controls
obtained by a unary-addressed lookup into the actual physical prefix. -/
theorem flatSelectedStage {X : Type} {r : Regime X} {l : X → ℕ} (H i p g s : X → ℕ)
    (ρ : ℝ) {U : X → Type} (u : (x : X) → Series (U x))
    (src : (x : X) → Fin (i x) → Option (Fin (p x)))
    (hc : r.Has (tally ∘ extent H (fun _ => 0) i))
    (shape : r.Has fun x => Packed.signs (H x) 0 (i x))
    (sparse : ∀ x, (3 * cap (i x) (H x) 0 + 1) * (32 * i x) ≤ 2 ^ width (H x) 0)
    (hp : r.Has (tally ∘ p)) (hg : r.Has (tally ∘ g)) (hs : r.Has (tally ∘ s))
    (sw : RectInterchange r (extent H (fun _ => 0) i) ρ)
    (indices : r.Has fun x => List.ofFn fun j => tally (((src x j).map Fin.val).getD (p x)))
    (z : ∀ x, (u x).count ≤ l x) (hr : 0 ≤ ρ)
    (f : (x : X) → Block 2 (p x + cap (i x) (H x) 0 + g x + cap (i x) (H x) 0 + s x) → U x → Bead) :
    let n := extent H (fun _ => 0) i
    let flat x := line 2 (p x + n x + g x + n x + s x)
    let b x (a : Block 2 (p x)) j := ((src x j).map (prefixBit a)).getD false
    Breeze (Spindle.modes n (τ := ρ)) r (fun x => (flat x).count) l
      (together r.header (cloth flat u f))
      (cloth flat u fun x a => f x (flatMask (p x) (g x) (s x) (b x) a)) := by
  let b x (a : Block 2 (p x)) j := ((src x j).map (prefixBit a)).getD false
  have bits : Strip.Trace r (fun x => line 2 (p x)) (fun _ a => send (List.ofFn (prefixBit a))) := by
    simp only [prefixBit_list]
    exact Curtain.aims (fun _ a => least a) (Curtain.issues p hp)
      _ (Easy.finite title).mapping.poly
  have ctrl : Strip.Trace r (fun x => line 2 (p x)) (fun x a => send (List.ofFn (b x a))) := by
    have F := selectedTrace _ _ bits indices
    simpa only [selectBits_ofFn, b] using F
  exact flatControlledStage H i p g s ρ u b hc shape sparse hp hg hs sw ctrl z hr f

end
end Controlled

end NearSquareRoot
end Computability
end OAI
