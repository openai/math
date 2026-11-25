import OAI.ThreeFlat.Diagonal.HistoryPortCost
import OAI.ThreeFlat.Diagonal.HistoryWork

namespace OAI
/-! # Additive per-ancestor charges for compiling selected cells -/

namespace ThreeFlat.Diagonal.HistoryContraction

open scoped BigOperators Classical

namespace Tree
variable {F : Type*} {p : ℕ}

/-- Intrinsic resource count before pricing repeated copies by depth. -/
def resources (T : Tree F p) := Stage.treeWork T + T.footprint.pins

@[simp] theorem resources_atom (N : BitNetwork F p) : resources (.atom N)=N.internal+N.cells+1 := rfl

/-- One separate absolute coefficient covers all fixed leaf decoders, command
setup and pin-map arithmetic. The depth term alone pays for repeated copies. -/
theorem native_cost (T : Tree F p) (h setup maps : ℕ) :
    T.scheduledWork h setup+maps*T.footprint.pins ≤ (10025+1016*h+setup+maps)*T.resources := by
  let c := 10025+1016*h+setup
  have first : T.scheduledWork h setup ≤ c*T.resources := by
    unfold scheduledWork c resources Stage.treeWork
    exact Nat.mul_le_mul_left _ (by omega)
  have sec : maps*T.footprint.pins ≤ maps*T.resources := Nat.mul_le_mul_left _ (by unfold resources; omega)
  rw [Nat.add_mul]
  exact Nat.add_le_add first sec

end Tree

namespace Stage

variable {F Pins : Type*} [CommSemiring F] {S : Shape} {R : Rewrite S F} {t : Fin R.count}
    {V : Form S Pins} {W : Form (R.target t) Pins}

/-- The new stage's resource contribution and the address maps from old cells
are presented separately so that their two width taxes can be charged at
the corresponding source sites. -/
def freshResources (A : Stage R t V W) (v : (R.target t).Site) :=
  1+A.hidden v+A.rootWidth v+(A.root v).resources

theorem resources_assemble (A : Stage R t V W) (N : Forest F V) (v : (R.target t).Site) :
    (A.assemble N v).resources = A.freshResources v+
      ∑ i, ((N (A.child v i).val).resources+V.width (A.child v i).val) := by
  simp only [Tree.resources,work_assemble,pinWords_assemble,freshResources,overhead,Finset.sum_add_distrib]
  omega

/-- The node's newly charged amount `local` and its child-bank charges are
exactly the numerical data propagated by the compact chronological scan. -/
def charge (A : Stage R t V W) (localCost : (R.target t).Site→ℕ) (prev : S.Site→ℕ)
    (v : (R.target t).Site) := localCost v+∑ i, prev (A.child v i).val

/-- Each ascent adds the two fixed boundary tax factors to the multiplier.
In particular, large external pins can be attributed to their true trace
leaf and carried upwards in `prev` without another global per-bit scan. -/
theorem resources_le_charge (A : Stage R t V W) (N : Forest F V) (localCost : (R.target t).Site→ℕ)
    (prev : S.Site→ℕ) (level widthTax freshTax : ℕ) (v : (R.target t).Site)
    (old : ∀ u, (N u).resources ≤ (level+1)*prev u)
    (width : ∀ u, V.width u ≤ widthTax*prev u)
    (fresh : A.freshResources v ≤ localCost v+freshTax*∑ i,prev (A.child v i).val) :
    (A.assemble N v).resources ≤ (level+widthTax+freshTax+1)*charge A localCost prev v := by
  rw [resources_assemble, Finset.sum_add_distrib]
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin (A.count v)) _ => Nat.add_le_add (old (A.child v i).val) (width (A.child v i).val))
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at sum
  let z := ∑ i, prev (A.child v i).val
  have factor : (level+widthTax+freshTax+1)*z=(level+1)*z+widthTax*z+freshTax*z := by ring
  have keep : localCost v ≤ (level+widthTax+freshTax+1)*localCost v := by
    exact (Nat.one_mul _).symm.le.trans (Nat.mul_le_mul_right _ (by omega))
  unfold charge
  rw [Nat.mul_add]
  change _ ≤ _ + (level+widthTax+freshTax+1)*z
  rw [factor]
  change _ ≤ localCost v+freshTax*z at fresh
  change _ ≤ (level+1)*z+widthTax*z at sum
  omega

end Stage
end ThreeFlat.Diagonal.HistoryContraction

end OAI
