import OAI.Computability.BorderVNP.PackedBottomGridBank
import OAI.Computability.BorderVNP.PackedBottomGridRepeat

/-! # Free original wire choices and forced auxiliary bits at the bottom

Each copy's free private assignment consists precisely of its original
within-cell wires. Once the public incidence words and compact use guesses
are supplied, every other bit of the work slab is determined. The explicit
bijection permits summing the private guesses in the physical order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open scoped Classical

/-- Public and private lengths of one bottom copy. -/
structure Slab where
  /-- Actual private fine wire bits. -/
  guessed : ℕ
  /-- Actual fine external bits (crossing edges and live argument bits). -/
  supplied : ℕ
  /-- Public capacity for both of these regions. -/
  capFine : ℕ
  /-- Full public cable and grouped-port incidence bits per copy. -/
  incoming : ℕ
  /-- Number of private weighted sources. -/
  used : ℕ
  /-- Fixed number of report staging lanes per copy. -/
  capReport : ℕ
  /-- The actual private topology fits the common fine-bit reservation. -/
  fineFits : guessed+supplied ≤ capFine
  /-- The immutable sidecar fits the common report reservation. -/
  reportFits : used ≤ capReport

/-- One-copy storage used before the report staging interval. -/
def Slab.orig (s : Slab) := s.capFine+s.incoming

/-- The physical stride for every copy of the original site's immutable private box. -/
def Slab.stride (s : Slab) := bottomStride s.orig s.capReport

/-- Old fine guesses, old supplied values, zero padding, public incidence, and
reported unary uses in the actual order of the padded private work slab. -/
def Slab.complete (s : Slab) (guess : Fin s.guessed → Bool) (supplied : Fin s.supplied → Bool)
    (input : Fin s.incoming → Bool) (use : Fin s.used → Bool) (k : Fin s.stride) : Bool :=
  if h : k.val < s.guessed then guess ⟨k,h⟩
  else if h : k.val < s.guessed+s.supplied then supplied ⟨k.val-s.guessed,by omega⟩
  else if h : k.val < s.capFine then false
  else if h : k.val < s.capFine+s.incoming then input ⟨k.val-s.capFine,by omega⟩
  else if h : k.val < s.capFine+s.incoming+s.used then use ⟨k.val-(s.capFine+s.incoming),by omega⟩
  else false

/-- Read an independent fine wire choice directly from its physical copy. -/
def Slab.extractGuess (s : Slab) (bank : Fin s.stride → Bool) (j : Fin s.guessed) : Bool :=
  bank ⟨j.val,by have := s.fineFits; have := j.isLt; simp only [stride,orig,bottomStride]; omega⟩

/-- The forced region begins exactly after the original fine wire guesses. -/
def Slab.Forced (s : Slab) (supplied : Fin s.supplied → Bool) (input : Fin s.incoming → Bool)
    (use : Fin s.used → Bool) (bank : Fin s.stride → Bool) : Prop :=
  ∀ k : Fin s.stride, s.guessed ≤ k.val →
    bank k = s.complete (fun _ => false) supplied input use k

/-- The added forced lanes cannot change any of the free original fine bits. -/
@[simp] theorem Slab.extract_complete (s : Slab) (g : Fin s.guessed → Bool) (u i r) :
    s.extractGuess (s.complete g u i r) = g := by
  funext k
  simp only [extractGuess,complete,k.isLt,dite_true]

/-- The genuine auxiliary assignments form one copy of the original fine guess space. -/
def Slab.guessEquiv (s : Slab) (u : Fin s.supplied → Bool) (i : Fin s.incoming → Bool)
    (r : Fin s.used → Bool) : (Fin s.guessed → Bool) ≃ {b : Fin s.stride → Bool // s.Forced u i r b} where
  toFun g := ⟨s.complete g u i r,fun k hk => by simp [complete,Nat.not_lt.mpr hk]⟩
  invFun b := s.extractGuess b.val
  left_inv g := s.extract_complete g u i r
  right_inv b := by
    apply Subtype.ext
    funext k
    by_cases h : k.val < s.guessed
    · simp only [complete,h,dite_true,extractGuess]
    · rw [b.property k (Nat.le_of_not_lt h)]
      simp [complete,h]

/-- The inputs appearing in the physical equalities, separately from all padding. -/
def Slab.Lanes (s : Slab) (u : Fin s.supplied → Bool) (i : Fin s.incoming → Bool)
    (r : Fin s.used → Bool) (bank : Fin s.stride → Bool) : Prop :=
  (∀ (k : Fin s.stride) (j : Fin s.supplied), k.val = s.guessed+j.val → bank k = u j) ∧
  (∀ k : Fin s.stride, s.guessed+s.supplied ≤ k.val → k.val < s.capFine → bank k = false) ∧
  (∀ (k : Fin s.stride) (j : Fin s.incoming), k.val = s.capFine+j.val → bank k = i j) ∧
  (∀ (k : Fin s.stride) (j : Fin s.used), k.val = s.orig+j.val → bank k = r j) ∧
  ∀ k : Fin s.stride, s.orig+s.used ≤ k.val → bank k = false

/-- Satisfaction of the actual five address ranges is equivalent to having the
unique extension of one's own free fine-wire guess. -/
theorem Slab.forced_iff_lanes (s : Slab) (u i r) (bank : Fin s.stride → Bool) :
    s.Forced u i r bank ↔ s.Lanes u i r bank := by
  have hfit := s.fineFits
  constructor
  · intro h
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro k j hk
      have hj := j.isLt
      have hn : ¬ k.val < s.guessed := by omega
      have hy : k.val < s.guessed+s.supplied := by omega
      simp only [h k (by omega),complete,hn,dite_false,hy,dite_true]
      congr 1
      exact Fin.ext (by dsimp only; omega)
    · intro k hl hr
      simp [h k (by omega),complete,Nat.not_lt.mpr (by omega : s.guessed ≤ k.val),Nat.not_lt.mpr hl,hr]
    · intro k j hk
      have hj := j.isLt
      simp only [h k (by omega),complete,Nat.not_lt.mpr (by omega : s.guessed ≤ k.val),
        Nat.not_lt.mpr (by omega : s.guessed+s.supplied ≤ k.val),Nat.not_lt.mpr (by omega : s.capFine ≤ k.val),
        dite_false,dite_eq_left (by omega : k.val < s.capFine+s.incoming)]
      congr 1
      exact Fin.ext (by dsimp only; omega)
    · intro k j hk
      dsimp only [orig] at hk
      have hj := j.isLt
      simp only [h k (by omega),complete,Nat.not_lt.mpr (by omega : s.guessed ≤ k.val),
        Nat.not_lt.mpr (by omega : s.guessed+s.supplied ≤ k.val),Nat.not_lt.mpr (by omega : s.capFine ≤ k.val),
        Nat.not_lt.mpr (by omega : s.capFine+s.incoming ≤ k.val),dite_false,
        dite_eq_left (by omega : k.val < s.capFine+s.incoming+s.used)]
      congr 1
      exact Fin.ext (by dsimp only; omega)
    · intro k hk
      dsimp only [orig] at hk
      simp [h k (by omega),complete,Nat.not_lt.mpr (by omega : s.guessed ≤ k.val),
        Nat.not_lt.mpr (by omega : s.guessed+s.supplied ≤ k.val),Nat.not_lt.mpr (by omega : s.capFine ≤ k.val),
        Nat.not_lt.mpr (by omega : s.capFine+s.incoming ≤ k.val),Nat.not_lt.mpr hk]
  · rintro ⟨hu,hz,hi,hr,ht⟩ k hk
    unfold complete
    split
    · omega
    split
    · exact hu _ _ (by dsimp only; omega)
    split
    · exact hz _ (by omega) (by assumption)
    split
    · exact hi _ _ (by dsimp only; omega)
    split
    · exact hr _ _ (by dsimp only [orig]; omega)
    · exact ht _ (by dsimp only [orig]; omega)

/-- One free fine guess per copy is equivalent to the physical work slab conditioned
on the exact supplied and reported values. -/
noncomputable def Slab.bundleGuessEquiv (s : Slab) (b : ℕ)
    (u : Fin b → Fin s.supplied → Bool) (i : Fin b → Fin s.incoming → Bool) (r : Fin b → Fin s.used → Bool) :
    (Fin b → Fin s.guessed → Bool) ≃
      {bank : Fin (b*s.stride) → Bool // ∀ c : Fin b, s.Lanes (u c) (i c) (r c)
        (fun j => bank (finProdFinEquiv (c,j)))} where
  toFun g := ⟨fun k => s.complete (g (finProdFinEquiv.symm k).1) (u (finProdFinEquiv.symm k).1)
    (i (finProdFinEquiv.symm k).1) (r (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2,by
    intro c
    simp only [Equiv.symm_apply_apply]
    exact (s.forced_iff_lanes ..).mp ((s.guessEquiv (u c) (i c) (r c)) (g c)).property⟩
  invFun bank c := s.extractGuess (fun j => bank.val (finProdFinEquiv (c,j)))
  left_inv g := by
    funext c
    simp only [Equiv.symm_apply_apply,extract_complete]
  right_inv bank := by
    apply Subtype.ext
    funext k
    obtain ⟨⟨c,j⟩,rfl⟩ := finProdFinEquiv.surjective k
    simp only [Equiv.symm_apply_apply]
    let row : {z // s.Forced (u c) (i c) (r c) z} :=
      ⟨fun t => bank.val (finProdFinEquiv (c,t)), (s.forced_iff_lanes ..).mpr (bank.property c)⟩
    exact congrFun (congrArg Subtype.val ((s.guessEquiv (u c) (i c) (r c)).apply_symm_apply row)) j

end Packing.BottomReports

end BorderVNP
end Computability
end OAI
