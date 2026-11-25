import OAI.Computability.NearSquareRoot.CRTControlledReserveFactor
import OAI.Computability.NearSquareRoot.CRTControlledReserveTile
import OAI.Computability.NearSquareRoot.CRTControlledFlatDisjoint
import OAI.Computability.NearSquareRoot.SynchronizedBitAddress

/-! # Physical record addresses for the reserved-position schedule -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication.Adic
noncomputable section

variable {k lo hi : ℕ}

/-- Read position `q j` of an input block at output position `j`. -/
def flatBitPullback (q : Equiv.Perm (Fin k)) : Equiv.Perm (Block 2 k) :=
  (flatAddress 2 k).trans ((BoxFin.bitAddress q.symm).trans (flatAddress 2 k).symm)

theorem flatBitPullback_prefixBit (q : Equiv.Perm (Fin k)) (y : Block 2 k) (j : Fin k) :
    prefixBit (flatBitPullback q y) j = prefixBit y (q j) := by
  rw [flatBitPullback, Equiv.trans_apply, Equiv.trans_apply, prefixBit_address,
    prefixBit_number, ← flatAddress_val]
  simpa only [Equiv.symm_apply_apply] using
    BoxFin.bitAddress_testBit q.symm (flatAddress 2 k y) (q j)

/-- Agreement on all bit lookups identifies the permutation of complete record addresses. -/
theorem eq_flatBitPullback (q : Equiv.Perm (Fin k)) (e : Equiv.Perm (Block 2 k))
    (reads : ∀ y j, prefixBit (e y) j = prefixBit y (q j)) : e = flatBitPullback q := by
  ext y
  apply prefixBit_injective k
  funext j
  rw [reads, flatBitPullback_prefixBit]

namespace ReserveStage

/-- Address read by a forward swap pass, the middle pass, and the reversed swap pass. -/
def flatRead (s : ReserveStage k lo hi) (m : Equiv.Perm (Block 2 k)) : Equiv.Perm (Block 2 k) :=
  ((swapsFlat s.moves.reverse).trans m).trans (swapsFlat s.moves)

/-- Run the listed physical record lookups in their actual chronological order. -/
theorem flatRead_passes {V : Type*} (s : ReserveStage k lo hi) (m : Equiv.Perm (Block 2 k))
    (f : Block 2 k → V) :
    let swaps (g : Block 2 k → V) (p : Fin k × Fin k) := g ∘ swapFlat p
    s.moves.reverse.foldl swaps (s.moves.foldl swaps f ∘ m) = f ∘ s.flatRead m := by
  dsimp only
  rw [foldl_swapFlat, foldl_swapFlat]
  rfl

theorem flatRead_prefixBit (s : ReserveStage k lo hi) (m : Equiv.Perm (Block 2 k))
    (reads : ∀ y j, prefixBit (m y) j = prefixBit y (ReserveMiddle.extend lo hi s.inner j))
    (y : Block 2 k) (j : Fin k) :
    prefixBit (s.flatRead m y) j = prefixBit y (s.act j) := by
  rw [flatRead, Equiv.trans_apply, Equiv.trans_apply, swapsFlat_prefixBit, reads,
    swapsFlat_reverse_prefixBit]
  rfl

theorem ofPerm_flatRead (q : Equiv.Perm (Fin k)) (fit : lo + hi ≤ k)
    (free : lo + hi ≤ (fixedPositions q).card) (m : Equiv.Perm (Block 2 k))
    (reads : ∀ y j, prefixBit (m y) j =
      prefixBit y (ReserveMiddle.extend lo hi (ofPerm q fit free).inner j)) :
    (ofPerm q fit free).flatRead m = flatBitPullback q := by
  apply eq_flatBitPullback
  intro y j
  rw [flatRead_prefixBit _ m reads, ofPerm_act]

/-- The address read by a sequence of physical stages, listed in execution order. -/
def flatReads (stages : List (ReserveStage k lo hi)) (m : ReserveStage k lo hi → Equiv.Perm (Block 2 k)) :
    Equiv.Perm (Block 2 k) :=
  stages.foldr (fun s tail => tail.trans (s.flatRead (m s))) (Equiv.refl _)

/-- Running each record pass in the supplied order reads the original record at
the composite physical address. -/
theorem flatReads_passes {V : Type*} (stages : List (ReserveStage k lo hi))
    (m : ReserveStage k lo hi → Equiv.Perm (Block 2 k)) (f : Block 2 k → V) :
    let swaps (g : Block 2 k → V) (p : Fin k × Fin k) := g ∘ swapFlat p
    stages.foldl (fun g s => s.moves.reverse.foldl swaps (s.moves.foldl swaps g ∘ m s)) f =
      f ∘ flatReads stages m := by
  induction stages generalizing f with
  | nil => rfl
  | cons s stages ih =>
    dsimp only
    rw [List.foldl_cons, flatRead_passes]
    exact ih (f ∘ s.flatRead (m s))

theorem flatReads_prefixBit (stages : List (ReserveStage k lo hi))
    (m : ReserveStage k lo hi → Equiv.Perm (Block 2 k))
    (reads : ∀ s ∈ stages, ∀ y j, prefixBit (m s y) j = prefixBit y (ReserveMiddle.extend lo hi s.inner j))
    (y : Block 2 k) (j : Fin k) :
    prefixBit (flatReads stages m y) j = prefixBit y (stages.foldl (fun z s => s.act z) j) := by
  induction stages generalizing j with
  | nil => rfl
  | cons s stages ih =>
    change prefixBit (s.flatRead (m s) (flatReads stages m y)) j = _
    rw [flatRead_prefixBit _ _ (reads s List.mem_cons_self)]
    exact ih (fun t ht => reads t (List.mem_cons_of_mem s ht)) (s.act j)

theorem four_flatReads (q : Equiv.Perm (Fin k)) (cap : lo + hi ≤ k / 2 - 2)
    (m : ReserveStage k lo hi → Equiv.Perm (Block 2 k))
    (reads : ∀ s ∈ four q cap, ∀ y j,
      prefixBit (m s y) j = prefixBit y (ReserveMiddle.extend lo hi s.inner j)) :
    flatReads (four q cap) m = flatBitPullback q := by
  apply eq_flatBitPullback
  intro y j
  rw [flatReads_prefixBit _ _ reads, four_act]

/-- Four physical passes on the interior fields suffice. The high/low packing
and all forward and reversed flat swaps are included in the address equality. -/
theorem four_middleReads (q : Equiv.Perm (Fin k)) (cap : lo + hi ≤ k / 2 - 2)
    (m : ReserveStage k lo hi → Equiv.Perm (Block 2 (k - lo - hi)))
    (reads : ∀ s ∈ four q cap, ∀ y j, prefixBit (m s y) j = prefixBit y (s.inner j)) :
    flatReads (four q cap) (fun s => ReserveTile.lift (by omega) (m s)) = flatBitPullback q := by
  apply four_flatReads
  intro s hs
  exact ReserveTile.lift_prefixBit _ _ _ (reads s hs)

/-- The coordinate action holds without auxiliary choices when the interior
uses its canonical physical bit permutation. -/
theorem four_canonicalReads (q : Equiv.Perm (Fin k)) (cap : lo + hi ≤ k / 2 - 2) :
    flatReads (four q cap) (fun s => ReserveTile.lift (by omega) (flatBitPullback s.inner)) =
      flatBitPullback q :=
  four_middleReads q cap _ (fun s _ => flatBitPullback_prefixBit s.inner)

end ReserveStage
end
end Controlled

end NearSquareRoot
end Computability
end OAI
