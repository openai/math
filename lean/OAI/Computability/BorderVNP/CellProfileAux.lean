import OAI.Computability.BorderVNP.CellProfileGenerator
import OAI.Computability.BorderVNP.CellAuxSlabs

/-!
# Exact summation of a profile checker's private guesses

The flag cube of each term occupies every address in its finite physical
slab. Its bits are forced by the selector word. The profile program can
therefore guess the entire slab, run its actual NAND guards, discard the
flags and continue, with signed multiplicity one on valid data.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Profile

open scoped Classical
open CellMacro (Op)

/-- Row-major address of each private prefix flag. This is a bijection
onto the entire allocated contiguous auxiliary block. -/
def flagIndex (copies terms : ℕ) :
    (Fin terms × Fin (copies+1) × Fin (copies+1)) ≃ Fin (auxSize copies terms) :=
  ((Equiv.refl (Fin terms)).prodCongr finProdFinEquiv).trans finProdFinEquiv

/-- The physical address used by the checker is its slab base plus the
numeric row-major index, with the candidate count varying fastest. -/
theorem flagAddress (base copies terms : ℕ) (t : Fin terms) (i k : Fin (copies+1)) :
    Prefix.address (termBase base copies t) copies i k =
      base + (flagIndex copies terms (t, i, k)).val := by
  change base + t.val * ((copies + 1) * (copies + 1)) + i.val * (copies + 1) + k.val =
    base + (k.val + (copies + 1) * i.val + ((copies + 1) * (copies + 1)) * t.val)
  ring

/-- The single physical vector of all true prefix-count flags. -/
def canonicalAux (bank : ℕ → Bool) (copies terms : ℕ) (s : Port) (w : ℕ)
    (q : Fin (auxSize copies terms)) : Bool :=
  let z := (flagIndex copies terms).symm q
  decide (earlier bank s w z.1.val z.2.1.val = z.2.2.val)

/-- Each addressed bit in the canonical auxiliary word equals the corresponding flag. -/
theorem canonicalAux_at (bank : ℕ → Bool) (copies terms : ℕ) (s : Port) (w : ℕ)
    (t : Fin terms) (i k : Fin (copies+1)) :
    canonicalAux bank copies terms s w (flagIndex copies terms (t,i,k)) =
      decide (earlier bank s w t i = k) := by
  unfold canonicalAux
  rw [Equiv.symm_apply_apply]

/-- Characterization for a slab at any offset, including a profile row
embedded between other profile or gadget-count rows. -/
theorem accept_iff_aux (dataBank physical : ℕ → Bool) (base copies : ℕ) (s : Port) (w : ℕ)
    (hist : List ℕ) (routes : List Route) (x : Fin (auxSize copies hist.length) → Bool)
    (hx : ∀ q, physical (base + q.val) = x q) :
    Accept dataBank copies s w hist routes (bankFlags physical base copies) ↔
      profileValid dataBank copies s w hist routes ∧ x = canonicalAux dataBank copies hist.length s w := by
  have hg (t : Fin hist.length) (i k : Fin (copies+1)) :
      bankFlags physical base copies t i k = x (flagIndex copies hist.length (t,i,k)) := by
    rw [bankFlags, flagAddress base copies hist.length t i k, hx]
  rw [accept_iff]
  apply and_congr_right
  intro _
  constructor
  · intro h
    funext q
    obtain ⟨⟨t,i,k⟩, rfl⟩ := (flagIndex copies hist.length).surjective q
    rw [canonicalAux_at, ← hg]
    exact h t t.isLt i (Nat.le_of_lt_succ i.isLt) k (Nat.le_of_lt_succ k.isLt)
  · rintro rfl t ht i hi k hk
    let t' : Fin hist.length := ⟨t, ht⟩
    let i' : Fin (copies+1) := ⟨i, Nat.lt_succ_of_le hi⟩
    let k' : Fin (copies+1) := ⟨k, Nat.lt_succ_of_le hk⟩
    exact (hg t' i' k').trans (canonicalAux_at ..)

/-- The checker sees the untouched original assignment after the prepended
slab and reads the guessed vector at its row-major addresses. -/
theorem accept_stack_iff (copies : ℕ) (s : Port) (w : ℕ) (hist : List ℕ)
    (routes : List Route) (v : List Bool) (x : Fin (auxSize copies hist.length) → Bool) :
    Accept (data (auxSize copies hist.length) (lookup (List.ofFn x ++ v))) copies s w hist routes
        (bankFlags (lookup (List.ofFn x ++ v)) 0 copies) ↔
      profileValid (lookup v) copies s w hist routes ∧ x = canonicalAux (lookup v) copies hist.length s w := by
  have hd : data (auxSize copies hist.length) (lookup (List.ofFn x ++ v)) = lookup v :=
    funext (lookup_after_prefix x v)
  rw [hd]
  apply accept_iff_aux
  intro q
  rw [Nat.zero_add, lookup_prefix]

/-- The genuine signed machine value of the guessed block and compiled
profile guard, followed by a deterministic disposal and an arbitrary
continuation on the original wire bank. -/
theorem value_profileAux (copies : ℕ) (s : Port) (w : ℕ) (hist : List ℕ) (routes : List Route)
    (env : List ℕ) (ops : List Op) (f : CellMacro.Flags) (v : List Bool) :
    let n := auxSize copies hist.length
    CellMacro.value (List.replicate n .guess ++ (profileGen 0 n copies s w hist routes).expand env ++
      CellMacro.discardBlock n ++ ops) f v =
      if profileValid (lookup v) copies s w hist routes then CellMacro.value ops f v else 0 := by
  let n := auxSize copies hist.length
  apply CellMacro.value_uniqueBlock n (canonicalAux (lookup v) copies hist.length s w)
  intro x tail
  have hc := profileGen_checks 0 n copies s w hist routes env tail f (List.ofFn x ++ v)
  simpa only [n, accept_stack_iff] using hc

end CellSparse.Profile

end BorderVNP
end Computability
end OAI
