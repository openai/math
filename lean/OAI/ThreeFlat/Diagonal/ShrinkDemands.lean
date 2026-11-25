import OAI.ThreeFlat.Diagonal.SlotPayload
import OAI.ThreeFlat.Diagonal.CompressorBundleCounts
import OAI.ThreeFlat.Diagonal.CompressorRegularize
import OAI.LinearAlgebra.SpectralBooks.PortWiring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! # The AB and CD demand words of a six-party shrinking step

The same public order packs thick wires at both ends of their source
bundle. Its balanced intervals become the AB demands of the assigned
motifs. Each non-thick wire supplies exactly one CD demand, in the
orientation given by the designated thin endpoint. -/

namespace ThreeFlat.Diagonal.CompressorPacking

open Computability.VPVNP.Compression Computability.BorderVNP.Packing.CellSlabs
open scoped Classical BigOperators
noncomputable section

variable {c d Q : ℕ} {V H Tag L : Type*}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable (P : PackingData V H Tag L d c)

abbrev ThickAt (p : Site V Tag L × Fin d) := {e : Arc V H Tag L d c // e.1 = p ∧
  P.thick (sourcePosition e) ∧ P.thick (sourcePosition (P.actual e))}

abbrev OldWords (w : Arc V H Tag L d c → ℕ) := ∀ e, Fin (2^w e)

/-- Public ordering of the CD demands in each bundle. -/
def motifNumbers (code : Arc V H Tag L d c ↪ ℕ) (hc : 2 ≤ c) :
    P.Motif ≃ (Site V Tag L × Fin d) × Fin (3*(2^c*d)/4) := by
  letI : LinearOrder P.Motif := LinearOrder.lift' (fun m : P.Motif => code m.val)
    (code.injective.comp Subtype.val_injective)
  apply CompressorRegularize.numbering P.bundle
  intro p
  let e : ↥(CompressorRegularize.incident P.bundle p) ≃ {m : P.Motif // P.bundle m = p} :=
    Equiv.subtypeEquivRight (fun _ => by simp [CompressorRegularize.incident])
  rw [← Fintype.card_coe, Fintype.card_congr e]
  exact bundle_three_quarters P p hc

@[simp] theorem motifNumbers_bundle (code : Arc V H Tag L d c ↪ ℕ) (hc : 2 ≤ c) (m : P.Motif) :
    (motifNumbers P code hc m).1 = P.bundle m := rfl

variable (code : Arc V H Tag L d c ↪ ℕ) (w : Arc V H Tag L d c → ℕ)

def thickWidth (p : Site V Tag L × Fin d) : ℕ := ∑ a : ThickAt P p, w a.val

def oldBit (p : Site V Tag L × Fin d) : (Σ a : ThickAt P p, Fin (w a.val)) ≃ Fin (thickWidth P w p) :=
  ordinal ((Function.Embedding.subtype _).trans code) (fun a : ThickAt P p => w a.val)

/-- Read the AB field carried by slot `i` of the packed bundle, in word
coordinates, from the specified old half-wire assignment. -/
def abWord (hQ : 0 < Q) (p : Site V Tag L × Fin d) (i : Fin Q) (x : OldWords w) :
    Fin (2 ^ SlotEnergy.piece (thickWidth P w p) Q i) :=
  finFunctionFinEquiv fun k =>
    let loc := (oldBit P code w p).symm (SlotEnergy.pieceIndex _ _ hQ ⟨i,k⟩)
    finFunctionFinEquiv.symm (x loc.1.val) loc.2

/-- A packed slice only depends on thick–thick wires of its named bundle. -/
theorem abWord_congr (hQ : 0 < Q) (p : Site V Tag L × Fin d) (i : Fin Q) (x y : OldWords w)
    (eq : ∀ a : ThickAt P p, x a.val = y a.val) : abWord P code w hQ p i x = abWord P code w hQ p i y := by
  unfold abWord
  congr 1
  funext k
  simp only [eq]

omit [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] in
/-- Every old endpoint read to make an AB piece belongs to the A or B
site where the corresponding demand matrix is placed. -/
theorem thick_placement (layout : Bool) (p : Site V Tag L × Fin d) (a : ThickAt P p) :
    P.placement layout (sourcePosition a.val) = p.1 ∧
      P.placement layout (sourcePosition (P.actual a.val)) = (P.siteGraph.target p).1 := by
  have hs := a.property.2.1
  have ht := a.property.2.2
  simp only [PackingData.placement, hs, ht, ite_true]
  exact ⟨congrArg Prod.fst a.property.1, congrArg (fun q => (P.siteGraph.target q).1) a.property.1⟩

private theorem thick_words_eq (hQ : 0 < Q) (p : Site V Tag L × Fin d) (x y : OldWords w)
    (h : ∀ i : Fin Q, abWord P code w hQ p i x = abWord P code w hQ p i y) :
    ∀ a : ThickAt P p, x a.val = y a.val := by
  intro a
  apply finFunctionFinEquiv.symm.injective
  funext k
  let pos := oldBit P code w p ⟨a,k⟩
  obtain ⟨⟨i,j⟩,hij⟩ := (SlotEnergy.pieceIndex _ _ hQ).surjective pos
  have hfield := congrFun (finFunctionFinEquiv.injective (h i)) j
  let read (z : Σ a : ThickAt P p, Fin (w a.val)) (o : OldWords w) : Fin 2 :=
    finFunctionFinEquiv.symm (o z.1.val) z.2
  let position := (SlotEnergy.pieceIndex (thickWidth P w p) Q hQ) ⟨i,j⟩
  change read ((oldBit P code w p).symm position) x = read ((oldBit P code w p).symm position) y at hfield
  have hpos : (oldBit P code w p).symm position = ⟨a,k⟩ :=
    (congrArg (oldBit P code w p).symm hij).trans ((oldBit P code w p).symm_apply_apply _)
  rw [hpos] at hfield
  exact hfield

/-- CD is read starting at the C endpoint, reversing the old source/target
ordering when the old source is thick. -/
def cdWord (m : P.Motif) (x y : OldWords w) : Fin (2^w m.val) :=
  if P.thick (sourcePosition m.val) then y m.val else x m.val

omit [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] in
private theorem cdWord_eq_iff (m : P.Motif) (x y : OldWords w) :
    cdWord P w m x y = cdWord P w m y x ↔ x m.val = y m.val := by
  by_cases h : P.thick (sourcePosition m.val) <;> simp [cdWord, h, eq_comm]

private theorem all_indexed {A B : Type*} (num : A ≃ B) (ok : B → Prop)
    (h : ∀ m, ok (num m)) (p : B) : ok p := by
  obtain ⟨m,rfl⟩ := num.surjective p
  exact h m

set_option maxHeartbeats 600000 in
/-- The actual old wire tensor is the product of independent two-demand
wirings. Thus the CD fields and all AB pieces both have their prescribed
old half-wire values, with no free assignments introduced by the split. -/
theorem shrink_demands_entry {K : Type*} [CommSemiring K] (hQ : 0 < Q)
    (num : P.Motif ≃ (Site V Tag L × Fin d) × Fin Q) (x y : OldWords w) :
    (if x = y then (1:K) else 0) = ∏ m : P.Motif,
      if abWord P code w hQ (num m).1 (num m).2 x = abWord P code w hQ (num m).1 (num m).2 y ∧
          cdWord P w m x y = cdWord P w m y x then 1 else 0 := by
  by_cases h : x = y
  · subst y; simp
  · let valid (m : P.Motif) := abWord P code w hQ (num m).1 (num m).2 x =
        abWord P code w hQ (num m).1 (num m).2 y ∧ cdWord P w m x y = cdWord P w m y x
    have bad : ¬∀ m, valid m := by
      intro allok
      apply h
      funext e
      by_cases both : P.thick (sourcePosition e) ∧ P.thick (sourcePosition (P.actual e))
      · apply thick_words_eq P code w hQ e.1 x y _ ⟨e,rfl,both⟩
        intro i
        exact all_indexed num (fun u => abWord P code w hQ u.1 u.2 x = abWord P code w hQ u.1 u.2 y)
          (fun m => (allok m).1) (e.1,i)
      · exact (cdWord_eq_iff P w ⟨e,both⟩ x y).mp (allok ⟨e,both⟩).2
    obtain ⟨m,hm⟩ := not_forall.mp bad
    rw [ite_eq_right h]
    exact (Finset.prod_eq_zero (Finset.mem_univ m) (ite_eq_right hm)).symm

/-- The two actual demand widths, in AB, CD order. -/
def demandWidth (num : P.Motif ≃ (Site V Tag L × Fin d) × Fin Q) (m : P.Motif) : Fin 2 → ℕ :=
  ![SlotEnergy.piece (thickWidth P w (num m).1) Q (num m).2, w m.val]

/-- An endpoint reads the packed AB slice or its own CD field. -/
def demandEnd (hQ : 0 < Q) (num : P.Motif ≃ (Site V Tag L × Fin d) × Fin Q)
    (m : P.Motif) (x y : OldWords w) (side : Bool) (i : Fin 2) : Fin (2^demandWidth P w num m i) :=
  Fin.cases (motive := fun e => Fin (2^demandWidth P w num m e))
    (if side then abWord P code w hQ (num m).1 (num m).2 y else abWord P code w hQ (num m).1 (num m).2 x)
    (Fin.cases (if side then cdWord P w m y x else cdWord P w m x y) (fun j => j.elim0)) i

/-- Port-level form, applicable to the two demanded edges AB and CD of
the six-party motif. The party numbers do not affect the wire checks. -/
theorem shrink_demands_wiring {K : Type*} [CommSemiring K] (D : LinearAlgebra.SpectralBooks.PortGraph (Fin 6) (Fin 2))
    (hQ : 0 < Q) (num : P.Motif ≃ (Site V Tag L × Fin d) × Fin Q) (x y : OldWords w) :
    (if x = y then (1:K) else 0) = ∏ m : P.Motif,
      D.wiring (fun e => Fin (2^demandWidth P w num m e))
        (fun _ p => demandEnd P code w hQ num m x y p.1.2 p.1.1) := by
  rw [shrink_demands_entry P code w hQ num x y]
  apply Finset.prod_congr rfl
  intro m _
  unfold LinearAlgebra.SpectralBooks.PortGraph.wiring
  congr 1
  apply propext
  constructor
  · rintro ⟨hab,hcd⟩ e
    fin_cases e
    · exact hab
    · exact hcd
  · intro h
    exact ⟨h 0,h 1⟩

/-- Site at which the half-word of AB or CD is used after a layout. -/
def demandSite (layout : Bool) (m : P.Motif) (side : Bool) : Fin 2 → Site V Tag L :=
  ![if side then P.roleB m else P.roleA m,
    if side then P.roleD layout m else P.placement layout (P.C m)]

/-- Reading a demand half-word is local in the actual layout. Its value
is invariant under arbitrary changes to the old half-words at other sites. -/
theorem demandEnd_local (hQ : 0 < Q) (num : P.Motif ≃ (Site V Tag L × Fin d) × Fin Q)
    (bundled : ∀ m, (num m).1 = P.bundle m) (layout : Bool) (m : P.Motif) (side : Bool) (e : Fin 2)
    (x y x' y' : OldWords w)
    (hout : ∀ a, P.placement layout (sourcePosition a) = demandSite P layout m side e → x a = x' a)
    (hin : ∀ a, P.placement layout (sourcePosition (P.actual a)) = demandSite P layout m side e →
      y a = y' a) :
    demandEnd P code w hQ num m x y side e = demandEnd P code w hQ num m x' y' side e := by
  fin_cases e
  · cases side
    · apply abWord_congr
      intro a
      apply hout
      exact (thick_placement P layout _ a).1.trans (congrArg Prod.fst (bundled m))
    · apply abWord_congr
      intro a
      apply hin
      exact (thick_placement P layout _ a).2.trans (congrArg (fun q => (P.siteGraph.target q).1) (bundled m))
  · change (if side then cdWord P w m y x else cdWord P w m x y) =
      (if side then cdWord P w m y' x' else cdWord P w m x' y')
    by_cases thick : P.thick (sourcePosition m.val)
    · cases side
      · simpa [demandEnd, cdWord, demandSite, PackingData.C, thick] using
          (hin m.val (by simp [demandSite, PackingData.C, thick]))
      · simpa [demandEnd, cdWord, demandSite, PackingData.roleD, PackingData.D, thick] using
          (hout m.val (by simp [demandSite, PackingData.roleD, PackingData.D, thick]))
    · cases side
      · simpa [demandEnd, cdWord, demandSite, PackingData.C, thick] using
          (hout m.val (by simp [demandSite, PackingData.C, thick]))
      · simpa [demandEnd, cdWord, demandSite, PackingData.roleD, PackingData.D, thick] using
          (hin m.val (by simp [demandSite, PackingData.roleD, PackingData.D, thick]))

end
end ThreeFlat.Diagonal.CompressorPacking

end OAI
