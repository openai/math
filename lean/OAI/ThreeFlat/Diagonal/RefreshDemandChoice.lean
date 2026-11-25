import OAI.ThreeFlat.Diagonal.RefreshDemandRows

namespace OAI
/-! # Direct physical selection of the canonical refresh tile and its copy count -/

namespace ThreeFlat.Diagonal.RefreshDemandRows

open Computability.VPVNP.Compression RAM RAM.PhysicalPinsExpr RAM.MotifRows MotifIntegerChoice RefreshTies CompressorPacking.Native
open scoped Classical BigOperators
noncomputable section

variable {n k : ℕ} {E : Type} [Fintype E]

/-- Evaluate the fixed grid directly on its incoming and outgoing demand reads.
The finite list of coordinates is fixed together with the graph degree. -/
def scoreFields (b : E → Formula n) (d : E → ℕ) : Formula n :=
  let coords := (Finset.univ : Finset E).toList
  let bad := plus (.lit 1) (totals (coords.map b))
  biggest (coords.map fun e => required bad (b e) (d e))

def chooseFields (b : E → Formula n) (d : Fin (k+1) → E → ℕ) : Formula n × Formula n :=
  let row := fun j : Fin (k+1) => (scoreFields b (d j), Formula.lit j.val)
  ((List.finRange k).map (fun i => row i.succ)).foldl better (row 0)

def tileNumber (b : E → ℕ) (d : Fin (k+1) → E → ℕ) : Fin (k+1) :=
  best (score b d) 0 ((List.finRange k).map Fin.succ)

section
variable (u : ℕ) (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin n → ℕ)
local notation "V" => Formula.natural u data mem vs

private theorem coords_sum (b : E → Formula n) :
    V (totals ((Finset.univ : Finset E).toList.map b)) = ∑ e, V (b e) := by
  rw [totals_value,List.map_map]
  simpa only [Function.comp_def] using
    (Finset.sum_map_toList (Finset.univ : Finset E) (V ∘ b))

theorem scoreFields_value (b : E → Formula n) (d : E → ℕ) :
    V (scoreFields b d) = score (fun e => V (b e)) (fun _ : Unit => d) () := by
  let s := fun e => V (b e)
  have hbad : V (plus (.lit 1) (totals ((Finset.univ : Finset E).toList.map b))) = sentinel s := by
    change 1 + _ = 1 + _
    rw [coords_sum]
  apply Nat.le_antisymm
  · apply (biggest_le ..).mpr
    intro x hx
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp hx
    rw [required_value,hbad]
    exact Finset.le_sup (f := fun i => need (sentinel s) (s i) (d i)) (Finset.mem_univ e)
  · apply Finset.sup_le
    intro e _
    have h := (biggest_le u data mem vs _ _).mp (le_refl (V (scoreFields b d))) _
      (List.mem_map.mpr ⟨e,by simp,rfl⟩)
    rw [required_value,hbad] at h
    exact h

private theorem fold_choose (l : List (Formula n × Formula n)) (z : Formula n × Formula n) :
    evalPair u data mem vs (l.foldl better z) =
      best Prod.fst (evalPair u data mem vs z) (l.map (evalPair u data mem vs)) := by
  induction l generalizing z with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldl_cons,List.map_cons,best,ih]
    by_cases h : V j.1 < V z.1 <;>
      simp [better,evalPair,Formula.natural,natTest,h]

private theorem best_map {A B : Type} (f : A → B) (v : B → ℕ) (z : A) (l : List A) :
    best v (f z) (l.map f) = f (best (v ∘ f) z l) := by
  induction l generalizing z with
  | nil => rfl
  | cons j l ih =>
    simp only [List.map_cons,best,Function.comp_apply]
    split <;> apply ih

theorem chooseFields_value (b : E → Formula n) (d : Fin (k+1) → E → ℕ) :
    let s := fun e => V (b e)
    let j := tileNumber s d
    evalPair u data mem vs (chooseFields b d) = (score s d j,j.val) := by
  dsimp only
  let s := fun e => V (b e)
  let f := fun j : Fin (k+1) => (score s d j,j.val)
  have base (j : Fin (k+1)) :
      evalPair u data mem vs (scoreFields b (d j), .lit j.val) = f j := by
    exact Prod.ext (scoreFields_value u data mem vs b (d j)) rfl
  rw [chooseFields,fold_choose,List.map_map,base]
  change best Prod.fst (f 0) ((List.finRange k).map _) = _
  calc
    _ = best Prod.fst (f 0) (((List.finRange k).map Fin.succ).map f) := by
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact base i.succ
    _ = _ := best_map f Prod.fst 0 _

end

variable {a t v : ℕ}

def refreshChoice (C : Columns (Formula n)) (remaining block : Formula n)
    (d : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ) :=
  chooseFields (fun e => demand (mPort a) C remaining block e.1 e.2.1.val e.2.2.val) d

/-- Both native outputs refer to the very same canonically selected spectral
tile used by the history contraction. -/
theorem refreshChoice_value (G : Computability.VPVNP.Compression.LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))
    (u : ℕ) (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin n → ℕ)
    (C : Columns (Formula n)) (remaining block : Formula n) (z : Block v t)
    (w : Address' v a t → ℕ) (stored : Stored G (C.map (Formula.natural u data mem vs)) mem w)
    (hr : remaining.natural u data mem vs = 2^t) (hb : block.natural u data mem vs = blockId z)
    (d : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ) :
    let s := fun e => w (addr (arrival G (tagOrdinal a).symm) z e)
    let j := tileNumber s d
    evalPair u data mem vs (refreshChoice C remaining block d) = (score s d j,j.val) := by
  have h (e : Bool × Fin (mPort a) × Fin (mPort a)) : (demand (mPort a) C remaining block e.1 e.2.1.val e.2.2.val).natural u data mem vs =
      w (addr (arrival G (tagOrdinal a).symm) z e) := by
    rw [demand_value,hr,hb,demand_read G stored]
  simpa only [refreshChoice,funext h] using chooseFields_value u data mem vs
    (fun e => demand (mPort a) C remaining block e.1 e.2.1.val e.2.2.val) d

end
end ThreeFlat.Diagonal.RefreshDemandRows

end OAI
