import OAI.ThreeFlat.Diagonal.MotifCountCheck
import OAI.ThreeFlat.Diagonal.MotifOrderedCells

namespace OAI
/-! # Native-indexed LUT and counter streams for checking a histogram selector

Each copy checks that its header is admissible and sets exactly the mask bit
for its letter. All symbols then count their masks in parallel using a stable
compactor. The external header can include all incident selector words, so
one bounded LUT also checks port agreement.
-/

namespace ThreeFlat.Diagonal.MotifSelectorChecks

open MotifOuterTerms Routing.StableCompaction TraceCircuit
open scoped BigOperators Classical

variable {F : Type*} [CommRing F] {r h b p : ℕ}

def checks (good : (Fin b → Bool) → Prop) (letter : (Fin b → Bool) → Fin h)
    (z : Fin b → Bool) (mask : Fin h → Bool) := good z ∧ ∀ a, mask a = decide (letter z = a)

noncomputable def checkLut (good : (Fin b → Bool) → Prop) (letter : (Fin b → Bool) → Fin h)
    (xs : Fin (b+h) → Bool) : F :=
  if checks good letter (fun j => xs (j.castAdd h)) (fun a => xs (Fin.natAdd b a)) then 1 else 0

def localWire (i : Fin r) : Fin (b+h) → BitSource (r*h) (r*b) :=
  Fin.append (fun j => .pin (finProdFinEquiv (i,j))) (fun a => .hidden (finProdFinEquiv (i,a)))

def countWire (target : Histogram (Fin h) r) (a : Fin h) : Fin (r+(r+r)) → BitSource (r*h) p :=
  Fin.append (fun i => .hidden (finProdFinEquiv (i,a)))
    (Fin.append (fun _ => .constant true) (fun i => .constant (unary (target.val a).val i)))

structure Component (F : Type*) (h p : ℕ) where
  width : ℕ
  net : BitNetwork F width
  wire : Fin width → BitSource h p

noncomputable def components (good : (Fin b → Bool) → Prop) (letter : (Fin b → Bool) → Fin h)
    (C : BitNetwork F (r+(r+r))) (target : Histogram (Fin h) r) : Fin (r+h) → Component F (r*h) (r*b) :=
  Fin.append (fun i => ⟨_,ConstantKernelLUT.network (checkLut good letter),localWire i⟩)
    (fun a => ⟨_,C,countWire target a⟩)

private theorem component_left (good : (Fin b → Bool) → Prop) (letter : (Fin b → Bool) → Fin h)
    (C : BitNetwork F (r+(r+r))) (target : Histogram (Fin h) r) (i : Fin r) :
    components good letter C target (i.castAdd h) =
      ⟨_,ConstantKernelLUT.network (checkLut good letter),localWire i⟩ :=
  Fin.append_left _ _ i

private theorem component_right (good : (Fin b → Bool) → Prop) (letter : (Fin b → Bool) → Fin h)
    (C : BitNetwork F (r+(r+r))) (target : Histogram (Fin h) r) (a : Fin h) :
    components good letter C target (Fin.natAdd r a) = ⟨_,C,countWire target a⟩ :=
  Fin.append_right _ _ a

noncomputable def network (good : (Fin b → Bool) → Prop) (letter : (Fin b → Bool) → Fin h)
    (C : BitNetwork F (r+(r+r))) (target : Histogram (Fin h) r) :=
  BitNetwork.Ordered.glue (fun i => (components good letter C target i).net) (fun i => (components good letter C target i).wire)

/-- Each copy has one header table and each letter has one counter network. -/
theorem network_cells (good : (Fin b → Bool) → Prop) (letter : (Fin b → Bool) → Fin h)
    (C : BitNetwork F (r+(r+r))) (target : Histogram (Fin h) r) :
    (network good letter C target).cells = r*(2^(b+h)*(b+h+1)) + h*C.cells := by
  change (∑ i, (components good letter C target i).net.cells) = _
  rw [Fin.sum_univ_add]
  calc
    _ = (∑ _ : Fin r, 2^(b+h)*(b+h+1)) + ∑ _ : Fin h,C.cells := by
      apply congrArg₂ (·+·)
      · apply Finset.sum_congr rfl
        intro i _
        exact (congrArg (fun c : Component F (r*h) (r*b) => c.net.cells)
          (component_left good letter C target i)).trans (ConstantKernelLUT.network_cells _)
      · exact Finset.sum_congr rfl fun i _ => congrArg
          (fun c : Component F (r*h) (r*b) => c.net.cells) (component_right good letter C target i)
    _ = _ := by simp []

/-- The shared prefix contains one mask bit per copy and letter. -/
theorem network_hidden (good : (Fin b → Bool) → Prop) (letter : (Fin b → Bool) → Fin h)
    (C : BitNetwork F (r+(r+r))) (target : Histogram (Fin h) r) :
    (network good letter C target).internal = r*h + (r*2^(b+h) + h*C.internal) := by
  change r*h + (∑ i, (components good letter C target i).net.internal) = _
  rw [Fin.sum_univ_add]
  apply congrArg (r*h+·)
  calc
    _ = (∑ _ : Fin r, 2^(b+h)) + ∑ _ : Fin h,C.internal := by
      apply congrArg₂ (·+·)
      · apply Finset.sum_congr rfl
        intro i _
        exact (congrArg (fun c : Component F (r*h) (r*b) => c.net.internal)
          (component_left good letter C target i)).trans (ConstantKernelLUT.network_internal _)
      · exact Finset.sum_congr rfl fun i _ => congrArg
          (fun c : Component F (r*h) (r*b) => c.net.internal) (component_right good letter C target i)
    _ = _ := by simp []

private theorem local_at (z : Fin r → Fin b → Bool) (m : Fin r → Fin h → Bool) (i : Fin r) :
    (fun j => (localWire i j).read (blocks r h m) (blocks r b z)) = Fin.append (z i) (m i) := by
  funext k
  refine Fin.addCases (fun _ => ?_) (fun _ => ?_) k <;> simp [localWire,BitSource.read]

private theorem count_at (target : Histogram (Fin h) r) (z : Fin r → Fin b → Bool)
    (m : Fin r → Fin h → Bool) (a : Fin h) :
    (fun j => (countWire target a j).read (blocks r h m) (blocks r b z)) =
      Fin.append (fun i => m i a) (Fin.append (fun _ => true) (unary (target.val a).val)) := by
  funext k
  refine Fin.addCases (fun _ => ?_) (fun q => ?_) k
  · simp [countWire,BitSource.read]
  · refine Fin.addCases (fun _ => ?_) (fun _ => ?_) q <;> simp [-Fin.natAdd_eq_addNat,countWire,BitSource.read]

/-- The read-only header predicates can inspect every bounded port selector
in a copy as well as its old digit. Histograms are checked intrinsically. -/
theorem eval (good : (Fin b → Bool) → Prop) (letter : (Fin b → Bool) → Fin h)
    (C : BitNetwork F (r+(r+r))) (target : Histogram (Fin h) r)
    (hC : ∀ M X Y, C.eval (Fin.append M (Fin.append X Y)) = if Y = compact M X then 1 else 0)
    (z : Fin r → Fin b → Bool) :
    (network good letter C target).eval (blocks r b z) =
      if (∀ i, good (z i)) ∧ target = histogram (fun i => letter (z i)) then 1 else 0 := by
  classical
  rw [network,BitNetwork.Ordered.glue_eval,← (blocks r h).sum_comp]
  let expected (i : Fin r) (a : Fin h) := symbolMask (fun j => letter (z j)) a i
  have body (m : Fin r → Fin h → Bool) :
      (∏ i, ((components good letter C target i).net).eval (fun j =>
        ((components good letter C target i).wire j).read (blocks r h m) (blocks r b z))) =
      (∏ i, if checks good letter (z i) (m i) then (1:F) else 0) *
      ∏ a, C.eval (Fin.append (fun i => m i a) (Fin.append (fun _ => true) (unary (target.val a).val))) := by
    let value (c : Component F (r*h) (r*b)) :=
      c.net.eval (fun j => (c.wire j).read (blocks r h m) (blocks r b z))
    change (∏ i,value (components good letter C target i)) = _
    rw [Fin.prod_univ_add]
    apply congrArg₂ (·*·)
    · apply Finset.prod_congr rfl
      intro i _
      refine (congrArg value (component_left good letter C target i)).trans ?_
      change (ConstantKernelLUT.network (checkLut good letter)).eval
        (fun j => (localWire i j).read (blocks r h m) (blocks r b z)) = _
      rw [local_at,ConstantKernelLUT.network_eval]
      simp [checkLut,-Fin.natAdd_eq_addNat]
    · apply Finset.prod_congr rfl
      intro i _
      refine (congrArg value (component_right good letter C target i)).trans ?_
      exact congrArg C.eval (count_at target z m i)
  simp only [body]
  rw [Fintype.sum_eq_single expected]
  · simp only [expected,histogram_check _ hC]
    by_cases all : ∀ i, good (z i)
    · simp [all,checks,symbolMask]
    · obtain ⟨i,hi⟩ := not_forall.mp all
      have bad : ¬checks good letter (z i) (expected i) := fun g => hi g.1
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right bad),zero_mul,ite_eq_right (fun h => all h.1)]
  · intro m ne
    have bad : ¬∀ i, checks good letter (z i) (m i) := by
      intro ok
      exact ne (funext fun i => funext fun a => (ok i).2 a)
    obtain ⟨i,hi⟩ := not_forall.mp bad
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi),zero_mul]

end ThreeFlat.Diagonal.MotifSelectorChecks

end OAI
