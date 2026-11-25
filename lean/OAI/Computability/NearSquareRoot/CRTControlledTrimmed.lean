import OAI.Computability.NearSquareRoot.CRTControlledFlat

/-! # Controlled XOR on residue classes within two full-width chunks

Both physical chunks retain the slice beginning at residual offset `r`. The
high unused bits of the first chunk follow the original prefix. Its source
selectors are shifted by that many bits in the little-endian prefix trace.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

open IntegerMultiplication IntegerMultiplication.Packed IntegerMultiplication.Adic
open IntegerMultiplication.Code IntegerMultiplication.Loom IntegerMultiplication.Strip

noncomputable section

/-- The spectator bits above the slice in each original chunk. -/
def trimTop (N r h : ℕ) := N-r-h

theorem trimmedWidth (p N g s r h : ℕ) (fit : r+h ≤ N) :
    (p+trimTop N r h)+h+(r+g+trimTop N r h)+h+(r+s) = p+N+g+N+s := by
  unfold trimTop
  omega

theorem trimmedStart (N g s r h : ℕ) (fit : r+h ≤ N) :
    (r+s)+h+(r+g+trimTop N r h) = s+N+g+r := by
  unfold trimTop
  omega

/-- Embed the original prefix after its newly exposed low spectator bits. -/
def trimPort {p : ℕ} (top : ℕ) (j : Fin p) : Fin (p+top) := ⟨j.val+top, by omega⟩

/-- The original prefix begins above both full chunks, the gap and suffix. -/
def wholePrefixPort (p N g s : ℕ) (j : Fin p) : Fin (p+N+g+N+s) :=
  ⟨s+N+g+N+j.val, by omega⟩

def trimCast (p N g s r h : ℕ) (fit : r+h ≤ N) :=
  castN 2 _ _ (trimmedWidth p N g s r h fit)

def trimSource {p i : ℕ} (top : ℕ) (src : Fin i → Option (Fin p))
    (a : Block 2 (p+top)) (j : Fin i) : Bool :=
  ((src j).map (fun q => prefixBit a (trimPort top q))).getD false

/-- Mask on two width-`N` chunks whose active slices start at little-endian bit `r`. -/
def trimmedMask {H i : ℕ} (p N g s r : ℕ) (fit : r + cap i H 0 ≤ N)
    (src : Fin i → Option (Fin p)) (y : Block 2 (p+N+g+N+s)) : Block 2 (p+N+g+N+s) :=
  let h := cap i H 0
  let top := trimTop N r h
  let c := trimCast p N g s r h fit
  c.cast (flatMask (p+top) (r+g+top) (r+s) (trimSource top src) (c.cast.symm y))

private theorem castLeast {n m : ℕ} (e : n = m) (x : Block 2 n) :
    least ((castN 2 n m e).cast x) = least x := by subst m; rfl

private theorem castLeastSymm {n m : ℕ} (e : n = m) (x : Block 2 m) :
    least ((castN 2 n m e).cast.symm x) = least x := by subst m; rfl

private theorem castPrefixSymm {n m : ℕ} (e : n = m) (x : Block 2 m) (j : Fin n) :
    prefixBit ((castN 2 n m e).cast.symm x) j = prefixBit x (j.cast e) := by
  subst m
  rfl

/-- The selected bit in each target segment uses the source in the original prefix.
All indices of this formula are in the full physical word. -/
theorem trimmedMask_slot {H i : ℕ} (p N g s r : ℕ) (fit : r + cap i H 0 ≤ N)
    (src : Fin i → Option (Fin p)) (y : Block 2 (p+N+g+N+s)) (n : ℕ) :
    let start := s+N+g+r
    let bit := n-start
    (least (trimmedMask p N g s r fit src y))[n]? =
      if h : start ≤ n ∧ bit / (H+1) < i ∧ bit % (H+1) = 0 then
        (least y)[n]?.map (fun d => maskDigit (Bool.xor (title d)
          (((src (⟨bit/(H+1),h.2.1⟩ : Fin i).rev).map
            (fun q => prefixBit y (wholePrefixPort p N g s q))).getD false)))
      else (least y)[n]? := by
  let w := cap i H 0
  let top := trimTop N r w
  let c := trimCast p N g s r w fit
  let raw := c.cast.symm y
  let a := (flatSpan (p+top) w (r+g+top) (r+s)).cast.symm raw
  have rd (j : Fin i) : trimSource top src a.1 j =
      ((src j).map (fun q => prefixBit y (wholePrefixPort p N g s q))).getD false := by
    unfold trimSource
    cases val : src j with
    | none => rfl
    | some q =>
      change prefixBit a.1 (trimPort top q) = _
      rw [show prefixBit a.1 (trimPort top q) =
        prefixBit raw (flatPrefixPort (p+top) w (r+g+top) (r+s) (trimPort top q))
        from flatPrefixPort_bit ..]
      rw [show prefixBit raw _ = _ from castPrefixSymm (trimmedWidth p N g s r w fit) y _]
      apply congrArg (prefixBit y)
      apply Fin.ext
      change (r+s)+w+(r+g+top)+w+(q.val+top) = s+N+g+N+q.val
      dsimp [top,trimTop]
      omega
  have h := flatMask_slot (p+top) (r+g+top) (r+s) (trimSource top src) raw n
  have hraw : least raw = least y := castLeastSymm _ _
  have hword : least (trimmedMask p N g s r fit src y) =
      least (flatMask (p+top) (r+g+top) (r+s) (trimSource top src) raw) := castLeast _ _
  dsimp only at h ⊢
  rw [hword]
  have startEq : (r+s) + cap i H 0 + (r+g+top) = s+N+g+r := trimmedStart N g s r w fit
  have rd' (j : Fin i) : trimSource top src
      ((flatSpan (p+top) (cap i H 0) (r+g+top) (r+s)).cast.symm raw).1 j =
      ((src j).map (fun q => prefixBit y (wholePrefixPort p N g s q))).getD false := rd j
  simpa only [hraw, startEq, rd'] using h

private theorem tallyJoin (a b : ℕ) : tally a ++ tally b = tally (a+b) := by
  simp only [tally, List.replicate_add]

private theorem addHeader {X : Type} {r : Regime X} {a b : X → ℕ}
    (ha : r.Has (tally ∘ a)) (hb : r.Has (tally ∘ b)) :
    r.Has (fun x => tally (a x+b x)) := by
  have h := (ha.pair hb).ez (Easy.append (X := Unit))
  simpa only [Function.comp_apply, tallyJoin] using h

private theorem subHeader {X : Type} {r : Regime X} {a b : X → ℕ}
    (ha : r.Has (tally ∘ a)) (hb : r.Has (tally ∘ b)) :
    r.Has (fun x => tally (a x-b x)) := by
  have h := (hb.pair ha).ez (easy_cut (X := Unit) Easy.identity).sndCompose
  simpa only [Function.comp_apply, cutLists, id_eq, tally, List.length_replicate, List.drop_replicate] using h

theorem shiftedSelectorHeader {X : Type} {r : Regime X} {i p top : X → ℕ}
    (src : (x : X) → Fin (i x) → Option (Fin (p x))) (ht : r.Has (tally ∘ top))
    (hs : r.Has fun x => List.ofFn fun j => tally (((src x j).map Fin.val).getD (p x))) :
    r.Has fun x => List.ofFn fun j =>
      tally ((((src x j).map (trimPort (top x))).map Fin.val).getD (p x + top x)) := by
  have push : Poly (fun t : Tally × List Tally => t.2.map (fun k => k ++ t.1)) :=
    Poly.push [] [] (Easy.exchange.compose (Easy.append (X := Unit))).poly
  have h := (ht.pair hs).thenDo push
  convert h using 2 with x
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  cases e : src x j <;> simp [e, trimPort, tallyJoin]

/-- Charge a full-word P192 pass using the widths, residual shift, and original
(unshifted) finite-source table from the header. -/
theorem trimmedSelectedStage {X : Type} {R : Regime X} {l : X → ℕ} (H i p N g s r : X → ℕ)
    (ρ : ℝ) {U : X → Type} (u : (x : X) → Series (U x))
    (src : (x : X) → Fin (i x) → Option (Fin (p x)))
    (fit : ∀ x, r x + cap (i x) (H x) 0 ≤ N x)
    (hc : R.Has (tally ∘ extent H (fun _ => 0) i))
    (shape : R.Has fun x => Packed.signs (H x) 0 (i x))
    (sparse : ∀ x, (3 * cap (i x) (H x) 0 + 1) * (32 * i x) ≤ 2 ^ width (H x) 0)
    (hp : R.Has (tally ∘ p)) (hN : R.Has (tally ∘ N)) (hg : R.Has (tally ∘ g))
    (hs : R.Has (tally ∘ s)) (hr : R.Has (tally ∘ r))
    (sw : RectInterchange R (extent H (fun _ => 0) i) ρ)
    (indices : R.Has fun x => List.ofFn fun j => tally (((src x j).map Fin.val).getD (p x)))
    (z : ∀ x, (u x).count ≤ l x) (hρ : 0 ≤ ρ)
    (f : (x : X) → Block 2 (p x + N x + g x + N x + s x) → U x → Bead) :
    let flat x := line 2 (p x + N x + g x + N x + s x)
    Breeze (Spindle.modes (extent H (fun _ => 0) i) (τ := ρ)) R (fun x => (flat x).count) l
      (together R.header (cloth flat u f))
      (cloth flat u fun x a => f x (trimmedMask (p x) (N x) (g x) (s x) (r x) (fit x) (src x) a)) := by
  let h := extent H (fun _ => 0) i
  let top x := trimTop (N x) (r x) (h x)
  let P x := p x+top x
  let G x := r x+g x+top x
  let S x := r x+s x
  let raw x := line 2 (P x+h x+G x+h x+S x)
  let full x := line 2 (p x+N x+g x+N x+s x)
  let c x := trimCast (p x) (N x) (g x) (s x) (r x) (h x) (fit x)
  have ht : R.Has (tally ∘ top) := subHeader (subHeader hN hr) hc
  have w := flatSelectedStage H i P G S ρ u (fun x j => (src x j).map (trimPort (top x)))
    hc shape sparse (addHeader hp ht) (addHeader (addHeader hr hg) ht) (addHeader hr hs)
    sw (shiftedSelectorHeader src ht indices) z hρ (fun x a => f x ((c x).cast a))
  have transfer (v : (x : X) → Block 2 (p x+N x+g x+N x+s x) → U x → Bead) :
      cloth full u v = cloth raw u (fun x a => v x ((c x).cast a)) := by
    funext x
    exact (c x).packet _
  change Breeze _ R (fun x => (full x).count) l (together R.header (cloth full u f))
    (cloth full u fun x a => f x (trimmedMask (p x) (N x) (g x) (s x) (r x) (fit x) (src x) a))
  rw [← funext (fun x => (c x).cost), transfer f, transfer]
  convert w using 1
  apply congrArg (cloth raw u)
  funext x a
  change f x ((c x).cast (flatMask (P x) (G x) (S x) (trimSource (top x) (src x))
    ((c x).cast.symm ((c x).cast a)))) = _
  rw [Equiv.symm_apply_apply]
  simp only [Option.map_map, Function.comp_def]
  rfl

end
end Controlled

end NearSquareRoot
end Computability
end OAI
