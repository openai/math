import OAI.Computability.BorderVNP.CubeTeamOwnedRun
import OAI.Computability.BorderVNP.CubeTeamOwnedDiagonalDispatch
import OAI.Computability.BorderVNP.CubeScatterPaddingBanksPast

/-! # Physical input of the complete owned-group traversal -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open Physical Physical.Owned Scatter Padding.Banks TeamRowSources Tally
open RoutingISA RoutingISA.Owned RoutingISA.OwnedStages VPVNP.BurstRAM

variable {w n blocks b h K s : ℕ} {l : TeamRowPrepare.Layout}

/-- The decoded inputs, address bounds and delivered buffers at the entrance of
the evaluator. The resident buffers are needed only for strict views owned by the team. -/
structure PhysicalSetup (A : Data n l.d blocks b h K s) (owner : Fin l.d → ℕ)
    (power base stop actual claimed : ℕ) (rows : Sym2 (Fin l.d) → Fin (n+1) → ℕ)
    (pub : Arg → Word w) (m : Memory w) : Prop where
  seed : Seed A l power pub m
  allocation : Allocation A l power base stop w
  fits : l.Fits w
  fields : l.Fields (readings m)
  directory : readings m (l.frame+78) = base
  owners : ∀ g : Fin l.d, readings m (l.ownerBase+g.val) = owner g
  capacity : base+3*vertexPrefix l (wordOwner owner) n blocks (l.d*l.d) ≤ stop
  image : CheckImage (rowLayout A l power) (source l power n) n actual claimed rows m
  authentic : passesLengths b s A.select (A.axis,rows)
  checker : LocalRow.Space (rowLayout A l power) w n b h K s (readings pub 0) actual claimed
  labelsFit : l.d^(n+1) ≤ 2^w
  packetFit : packetTrials n l.d blocks*(h*s) < 2^w
  capFit : declarationCap n l.d blocks b h s < 2^w
  afterScratch : LocalRow.head (rowLayout A l power) n b h K s+8+h ≤ A.singleBase
  checkSafe : ∀ x ∈ source l power n, LocalRow.Protected n h actual (LocalRow.head (rowLayout A l power) n b h K s) x
  selectorWords : ∀ p : Symbols l.d, ∀ high : Bool, owner (oriented p high).1 = l.teamID →
    Resident (Set.Ico l.viewBase (l.viewBase+l.stride*(l.d*l.d))) m
      (l.view (key (oriented p high))) (commonSelectors A.select A.axis p)
  crossingWords : ∀ p : Symbols l.d, ∀ high : Bool, owner (oriented p high).1 = l.teamID →
    Resident (Set.Ico l.viewBase (l.viewBase+l.stride*(l.d*l.d))) m
      (l.view (key (oriented p high))+(commonSelectors A.select A.axis p).length)
      (commonCrossings b A.axis p A.select A.supply (fun z => A.value z.1.val z.2))

variable {A : Data n l.d blocks b h K s} {owner : Fin l.d → ℕ} {power base stop actual claimed : ℕ}
variable {rows : Sym2 (Fin l.d) → Fin (n+1) → ℕ} {pub : Arg → Word w} {m mu : Memory w}

private theorem secondary {j : ℕ} (hj : j < 13) : l.header+j ∈ source l power n :=
  Or.inr (Or.inl (Or.inl (Or.inr ⟨Nat.le_add_right ..,Nat.add_lt_add_left hj _⟩)))

/-- Each preparation reads the same physical inventory even after earlier scatter and checker stores. -/
theorem source_inventory (fields : l.Fields (readings m)) (directory : readings m (l.frame+78) = base)
    (owners : ∀ g : Fin l.d, readings m (l.ownerBase+g.val) = owner g)
    (same : ∀ a ∈ source l power n, mu a = m a) :
    l.Fields (readings mu) ∧ readings mu (l.frame+78) = base ∧
      ∀ g < l.d, readings mu (l.ownerBase+g) = wordOwner owner g := by
  have fr (j : ℕ) (hj : j < 112) : readings mu (l.frame+j) = readings m (l.frame+j) :=
    congrArg Fin.val (same _ (primary hj))
  have hd (j : ℕ) (hj : j < 13) : readings mu (l.header+j) = readings m (l.header+j) :=
    congrArg Fin.val (same _ (secondary hj))
  refine ⟨⟨(fr _ (by decide)).trans fields.team,(fr _ (by decide)).trans fields.symbols,
    (fr _ (by decide)).trans fields.declaration,(fr _ (by decide)).trans fields.owners,
    (fr _ (by decide)).trans fields.views,(fr _ (by decide)).trans fields.spacing,
    (hd _ (by decide)).trans fields.axis,(hd _ (by decide)).trans fields.selectors⟩,
    (fr _ (by decide)).trans directory,?_⟩
  intro g hg
  have mem : l.ownerBase+g ∈ source l power n := Or.inl (Or.inr ⟨Nat.le_add_right ..,Nat.add_lt_add_left hg _⟩)
  rw [wordOwner,dite_eq_left hg]
  exact (show readings mu (l.ownerBase+g) = readings m (l.ownerBase+g) from congrArg Fin.val (same _ mem)).trans
    (owners ⟨g,hg⟩)

/-- Inventory for the evaluator after the shared payload has been decoded. -/
theorem PhysicalSetup.inventory (P : PhysicalSetup A owner power base stop actual claimed rows pub m)
    (same : ∀ a ∈ source l power n, mu a = m a) :
    l.Fields (readings mu) ∧ readings mu (l.frame+78) = base ∧
      ∀ g < l.d, readings mu (l.ownerBase+g) = wordOwner owner g :=
  source_inventory P.fields P.directory P.owners same

/-- No prefix of the chronological traversal requires more vertex records than its completed run. -/
theorem vertexPrefix_mono (l : TeamRowPrepare.Layout) (owner : ℕ → ℕ) (n blocks : ℕ) :
    Monotone (vertexPrefix l owner n blocks) := by
  apply monotone_nat_of_le_succ
  intro q
  simp only [vertexPrefix,Finset.sum_range_succ]
  exact Nat.le_add_right ..

/-- The directory has room for the entire current strict view, including its last triple. -/
theorem strict_prefix_room (capacity : base+3*vertexPrefix l (wordOwner owner) n blocks (l.d*l.d) ≤ stop)
    (p : Symbols l.d) (high : Bool) (owned : owner (oriented p high).1 = l.teamID) :
    let q := key (oriented p high)
    base+3*vertexPrefix l (wordOwner owner) n blocks q+(2*blocks*(l.d.choose 2)^n)*(3*2^n) ≤ stop := by
  intro q
  have hq : q < l.d*l.d := (finProdFinEquiv (oriented p high)).isLt
  have digits := key_digits (oriented p high)
  have ine : (oriented p high).1.val ≠ (oriented p high).2.val := by
    cases high <;> simp only [oriented,Bool.false_eq_true,ite_false,ite_true,Prod.fst_swap,Prod.snd_swap]
    · exact fun h => p.property.ne (Fin.ext h)
    · exact fun h => p.property.ne' (Fin.ext h)
  have ok : wordOwner owner (q/l.d) = l.teamID := by
    rw [digits.1]
    simpa only [wordOwner,dite_eq_left (oriented p high).1.isLt] using owned
  have distinct : q/l.d ≠ q%l.d := by rw [digits.1,digits.2]; exact ine
  have bound := Nat.add_le_add_left (Nat.mul_le_mul_left 3
    (vertexPrefix_mono l (wordOwner owner) n blocks hq)) base
  have leq := bound.trans capacity
  rw [show vertexPrefix l (wordOwner owner) n blocks (q+1) =
    vertexPrefix l (wordOwner owner) n blocks q+strictVertices n l.d blocks by
      simp [vertexPrefix,Finset.sum_range_succ,ok,distinct]] at leq
  simpa only [strictVertices,Nat.mul_add,Nat.mul_assoc,Nat.add_assoc,Nat.mul_comm,Nat.mul_left_comm] using leq

/-- Directory room at a strict row of an authentic physical assignment. -/
theorem PhysicalSetup.strictRoom (P : PhysicalSetup A owner power base stop actual claimed rows pub m)
    (p : Symbols l.d) (high : Bool) (owned : owner (oriented p high).1 = l.teamID) :
    let q := key (oriented p high)
    base+3*vertexPrefix l (wordOwner owner) n blocks q+(2*blocks*(l.d.choose 2)^n)*(3*2^n) ≤ stop :=
  strict_prefix_room P.capacity p high owned

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
