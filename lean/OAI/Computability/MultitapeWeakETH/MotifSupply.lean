import OAI.Computability.MultitapeWeakETH.MotifPorts

/-! # Compiling the selector and synchronization phase of a local motif map -/

namespace OAI.Computability.MultitapeWeakETH.MotifFields

open IntegerMultiplication Code VPVNP StackInterpreter MotifSelector
open scoped Classical
noncomputable section

def bank {I A : Type} [Fintype I] (f : I → A) : List A := List.ofFn fun i => f ((Fintype.equivFin I).symm i)

def fetch {I A : Type} [Fintype I] (d : A) (i : I) (xs : List A) : A := Iter.pick d (xs,tally ((Fintype.equivFin I) i).val)

theorem fetch_poly {I A : Type} [Fintype I] [Codec A] (d : A) (i : I) : Poly (fetch d i) :=
  (Poly.identity.pair (Code.Poly.const _)).compose (Iter.facile d).poly

theorem fetch_bank {I A : Type} [Fintype I] (d : A) (i : I) (f : I → A) : fetch d i (bank f) = f i := by
  unfold fetch bank
  rw [Iter.entry,Equiv.symm_apply_apply]

abbrev SupplyInput := List (Bits.Word × Tally) × Tally

variable {J E : Type} [DecidableEq J] [Fintype E] (G : Supply J E) (j : J)

def supplyInput {a u : ℕ} (v : E → ℕ) (x : Half G (fun e => Fin (v e+u*a) → Bool) j) : SupplyInput :=
  (bank (fun p : Port G j => (List.ofFn (endpoint G j x p),tally (v (edge G j p)))),tally u)

def columnTags (a : ℕ) (p : Port G j) (q : SupplyInput) :=
  tags a (fetch ([],[]) p q.1,q.2)

theorem columnTags_poly (a : ℕ) (p : Port G j) : Poly (columnTags G j a p) :=
  ((Easy.fst.poly.compose (fetch_poly ([],[]) p)).pair Easy.snd.poly).compose (tags_poly a)

theorem columnTags_eq {a u : ℕ} (v : E → ℕ) (x : Half G (fun e => Fin (v e+u*a) → Bool) j) (p : Port G j) :
    columnTags G j a p (supplyInput G j v x) = List.ofFn fun i =>
      Label.mk (endpoint G j (mapHalf G (fun _ => MotifEntry.readTag) x) p i) := by
  simp only [columnTags,supplyInput,fetch_bank,tags_eq]
  cases p <;> rfl

variable (a : ℕ) {S : Type} [Fintype S] (table : List S) (code : S ↪ Word a)

def synchronized (q : SupplyInput) : Bool :=
  decide (∀ p : Port G j, columnTags G j a p q = columnTags G j a (anchorPort G j) q)

theorem synchronized_poly : Poly (synchronized G j a) := by
  have eqs (p : Port G j) := ((columnTags_poly G j a p).pair (columnTags_poly G j a (anchorPort G j))).compose (listEq_poly _)
  convert all_poly _ eqs using 1
  funext q
  apply Bool.eq_iff_iff.mpr
  simp [synchronized]

def selectors (q : SupplyInput) : Option (List (Label S)) :=
  bif synchronized G j a q then decodeTags table code (columnTags G j a (anchorPort G j) q) else none

theorem selectors_poly : Poly (selectors G j a table code) :=
  Poly.choose (synchronized_poly G j a) ((columnTags_poly G j a (anchorPort G j)).compose (decodeTags_poly table code)) (Code.Poly.const _)

omit [Fintype S] in
theorem selectors_eq {u : ℕ} (v : E → ℕ) (x : Half G (fun e => Fin (v e+u*a) → Bool) j) :
    let t := mapHalf G (fun _ => MotifEntry.readTag) x
    selectors G j a table code (supplyInput G j v x) =
      if MotifEntry.consistent G j t then (MotifEntry.selectors? table code (MotifEntry.anchor G j t)).map
        (fun seq => List.ofFn fun i => Label.mk (seq i)) else none := by
  intro t
  have check : synchronized G j a (supplyInput G j v x) = MotifEntry.consistent G j t := by
    apply Bool.eq_iff_iff.mpr
    simp only [synchronized,decide_eq_true_eq,columnTags_eq]
    exact (consistent_iff G j t).symm
  simp only [selectors,check,columnTags_eq,endpoint_anchor,decodeTags_eq]
  cases MotifEntry.consistent G j t <;> rfl

end
end OAI.Computability.MultitapeWeakETH.MotifFields
