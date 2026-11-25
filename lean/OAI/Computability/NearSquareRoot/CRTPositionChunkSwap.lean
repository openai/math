import OAI.Computability.NearSquareRoot.CRTPositionChunkView
import OAI.Computability.NearSquareRoot.CRTControlledThree
import OAI.Computability.NearSquareRoot.CRTPositionProgramGather
import OAI.Computability.NearSquareRoot.InterchangeRectangular

/-! # Exchanging a compiled pair of chunks in the canonical array -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
open IntegerMultiplication.Adic IntegerMultiplication.Packed IntegerMultiplication.Loom
open IntegerMultiplication.Code

namespace PositionProgram

def swapOf (q : Fin 3 × Fin 3) : ChunkSwap :=
  if q.1 = 0 ∨ q.2 = 0 then
    if q.1 = 1 ∨ q.2 = 1 then .middleRight else .leftRight
  else .leftMiddle

def tripleView (n : ℕ) : Adopt (ChunkSwap.triple n) (line 2 (crossWidth n)) :=
  ((Adopt.same _).split (prefixView (p:=n) (n:=n) rfl)).thenDo
    (prefixView (p:=n) (n:=n+n) (Nat.add_assoc ..).symm)

def tripleFlat {n : ℕ} (q : Fin 3 × Fin 3) (a : Block 2 (crossWidth n)) :=
  (tripleView n).cast ((swapOf q).apply ((tripleView n).cast.symm a))

private def coord {A : Type} (a : A × A × A) (c : Fin 3) : A :=
  if c = 0 then a.1 else if c = 1 then a.2.1 else a.2.2

private theorem coord_swap {A : Type} (a : A × A × A) (s d : Fin 3) (hd : s ≠ d) (c : Fin 3) :
    coord ((swapOf (s,d)).apply a) c.rev = coord a ((Equiv.swap s d c).rev) := by
  fin_cases s <;> fin_cases d <;> fin_cases c <;> first | contradiction | rfl

theorem tripleView_bits {n : ℕ} (a : Block 2 n × Block 2 n × Block 2 n) (c : Fin 3) (j : Fin n) :
    crossBits ((tripleView n).cast a) (c,j) = prefixBit (coord a c) j := by
  let b := (prefixView (p:=n) (n:=n) rfl).cast a.2
  let h : n+(n+n) = crossWidth n := (Nat.add_assoc ..).symm
  change prefixBit ((prefixView h).cast (a.1,b)) (crossPort n (c,j)) = _
  fin_cases c
  · convert highPrefixBit h a.1 b j using 2
    · apply Fin.ext
      simp [crossPort,two_mul]
    · rfl
  · have lo := lowPrefixBit h a.1 b (⟨n+j.val,by omega⟩ : Fin (n+n))
    have mid := highPrefixBit (p:=n) (n:=n) rfl a.2.1 a.2.2 j
    exact (show _ = _ from by convert lo using 2; apply Fin.ext; simp [crossPort]).trans mid
  · have lo := lowPrefixBit h a.1 b (⟨j.val,by omega⟩ : Fin (n+n))
    have last := lowPrefixBit (p:=n) (n:=n) rfl a.2.1 a.2.2 j
    exact (show _ = _ from by convert lo using 2; apply Fin.ext; simp [crossPort]).trans last

def swapNative (k : ℕ) (q : Fin 3 × Fin 3) := underPrefix (chunkFactor k) (tripleFlat q)

theorem swapNative_bits (k : ℕ) (s d : Fin 3) (hd : s ≠ d) (a : Block 2 k) :
    prefixBit (swapNative k (s,d) a) = swapWord (s,d) (prefixBit a) := by
  obtain ⟨⟨hi,low⟩,rfl⟩ := (prefixView (chunkFactor k)).cast.surjective a
  obtain ⟨u,rfl⟩ := (tripleView (k/3)).cast.surjective low
  funext j
  obtain ⟨z,rfl⟩ := (threeChunksWithTail k).symm.surjective j
  cases z with
  | inl cj =>
    obtain ⟨c,j⟩ := cj
    simp only [swapNative,underPrefix_pair,bulkPrefixBit,tripleFlat,Equiv.symm_apply_apply,tripleView_bits,
      swapWord_bulk,coord_swap _ s d hd]
  | inr j => simp [swapNative,tailPrefixBit,swapWord_tail]

open IntegerMultiplication.Staff

private theorem measuredChunk {X : Type} {r : Regime X} {q : X → Fin 3 × Fin 3} {n : X → ℕ}
    (hq : r.Has q) (hn : Realizes r n) (t : ChunkSwap)
    (dim : ChunkSwap → ℕ → ℕ) (agrees : ∀ s k, dim s k = if s = t then k else 0) :
    r.Has fun x => tally (dim (swapOf (q x)) (n x)) := by
  have test := hq.ez (Easy.finite (fun a : Fin 3 × Fin 3 => decide (swapOf a = t)))
  have dec : Classified r (fun x => swapOf (q x) = t) :=
    ⟨_, test, fun _ => by simp⟩
  simpa only [agrees,Realizes,Function.comp_def] using hn.select (Realizes.fix 0) dec

theorem swapFlatStage {X : Type} {r : Regime X} {l : X → ℕ}
    (q : X → Fin 3 × Fin 3) (n : X → ℕ) (hq : r.Has q) (hn : Realizes r n)
    {ρ : ℝ} (hρ : 1/2 < ρ) {U : X → Type} (u : (x : X) → Series (U x))
    (hu : ∀ x, (u x).count ≤ l x)
    (f : (x:X) → Block 2 (crossWidth (n x)) → U x → Bead) :
    let t x := line 2 (crossWidth (n x))
    Breeze (Spindle.modes n (τ:=ρ)) r (fun x => (t x).count) l
      (together r.header (cloth t u f)) (cloth t u (fun x a => f x (tripleFlat (q x) a))) := by
  have fw := measuredChunk hq hn .middleRight ChunkSwap.front (by intro s k; cases s <;> rfl)
  have gw := measuredChunk hq hn .leftRight ChunkSwap.gap (by intro s k; cases s <;> rfl)
  have bw := measuredChunk hq hn .leftMiddle ChunkSwap.back (by intro s k; cases s <;> rfl)
  let A x := line 2 (crossWidth (n x))
  let B x := ChunkSwap.triple (n x)
  let v x := tripleView (n x)
  have run := ChunkSwap.physical (swapOf ∘ q) n ρ u (nearRoot_rectInterchange hρ r n) hn fw gw bw hu
    (fun x a => f x ((v x).cast a))
  have cast (g : (x:X) → Block 2 (crossWidth (n x)) → U x → Bead) :
      cloth A u g = cloth B u (fun x a => g x ((v x).cast a)) := by
    funext x; exact (v x).packet _
  change Breeze _ r (fun x => (A x).count) l (together r.header (cloth A u f)) (cloth A u _)
  rw [← funext (fun x => (v x).cost),cast f,cast]
  simpa only [tripleFlat, v, Equiv.symm_apply_apply, Function.comp_apply] using run

/-- Execute one chunk exchange directly from its finite tag and supplied word width.
The top zero, one, or two padding bits are spectators. -/
theorem swapNativeStage {X : Type} {r : Regime X} {l : X → ℕ}
    (q : X → Fin 3 × Fin 3) (k : X → ℕ) (hq : r.Has q) (hk : Realizes r k)
    {ρ : ℝ} (hρ : 1/2 < ρ) {U : X → Type} (u : (x : X) → Series (U x))
    (hu : ∀ x, (u x).count ≤ l x) (f : (x:X) → Block 2 (k x) → U x → Bead) :
    let t x := line 2 (k x)
    Breeze (Spindle.modes k (τ:=ρ)) r (fun x => (t x).count) l
      (together r.header (cloth t u f)) (cloth t u (fun x a => f x (swapNative (k x) (q x) a))) := by
  have hn := hk.dividing (Realizes.fix 3)
  have hp := hk.rem (Realizes.fix 3)
  have hw := (hn.plus hn).plus hn
  apply binaryPrefixPass (fun x => k x%3) (fun x => crossWidth (k x/3)) k (fun x => chunkFactor (k x))
    hp hw u hu (fun x => tripleFlat (q x)) _ f
  intro fs
  let J := (x : X) × Block 2 (k x%3)
  let proj : J → X := Sigma.fst
  have run := swapFlatStage (r:=r.pull proj) (q ∘ proj) (fun z => k (proj z)/3)
    (Task.BT.map hq proj) (Task.BT.map (show r.Has (fun x => tally (k x/3)) from hn) proj)
    hρ (fun z : J => u (proj z)) (fun z => hu (proj z)) fs
  apply run.raise
  intro z
  apply Real.rpow_le_rpow (by positivity) _ (by linarith : 0 ≤ ρ)
  exact_mod_cast Nat.succ_le_succ (Nat.div_le_self _ _)

end PositionProgram
end Controlled

end NearSquareRoot
end Computability
end OAI
