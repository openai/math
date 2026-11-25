import OAI.ThreeFlat.Diagonal.TraceCircuitArray

namespace OAI
/-! # Padding row verifiers to uniform widths

Extra hidden gate slots are each forced to zero once. Extra cells beyond
these forced bits are unit factors. The construction applies in every
characteristic, including characteristic two.
-/

namespace ThreeFlat.Diagonal.TraceCircuit

variable {F : Type*} {p n c : ℕ}

def Cell.lift (a : Cell F n p) (b : ℕ) : Cell F (n+b) p :=
  ⟨fun j => match a.source j with
   | .constant v => .constant v
   | .pin j => .pin j
   | .hidden j => .hidden (j.castAdd b), a.table⟩

private theorem lift_eval (z : Cell F n p) (pin : Fin p → Bool) (ws : Fin n → Bool)
    {b : ℕ} (bs : Fin b → Bool) :
    (z.lift b).eval pin (Fin.append ws bs) = z.eval pin ws := by
  unfold Cell.eval
  apply congrArg z.table
  funext j
  cases h : z.source j <;> simp [Cell.lift, h, BitSource.read]

private def forceFalse [Zero F] [One F] (i : Fin n) : Cell F n p :=
  ⟨![.hidden i,.constant false,.constant false],fun v => if v 0 then 0 else 1⟩

private def unitCell [One F] : Cell F n p := ⟨fun _ => .constant false, fun _ => 1⟩

def networkCells (N : BitNetwork F p) (i : Fin N.cells) : Cell F N.internal p := ⟨N.source i,N.table i⟩

/-- Add a specified number of forced-zero hidden bits and then a specified
number of constant cells. The original gate and cell prefixes keep their
exact numerical addresses. -/
def addPadding [Zero F] [One F] (N : BitNetwork F p) (extraBits extraCells : ℕ) : BitNetwork F p :=
  let cells : Fin ((N.cells+extraBits)+extraCells) → Cell F (N.internal+extraBits) p :=
    Fin.addCases (Fin.addCases (fun i => (networkCells N i).lift extraBits)
      (fun i => forceFalse (Fin.natAdd N.internal i))) (fun _ => unitCell)
  ⟨N.internal+extraBits, (N.cells+extraBits)+extraCells, fun i => (cells i).source, fun i => (cells i).table⟩

theorem addPadding_weight [CommSemiring F] (N : BitNetwork F p) (extraBits extraCells : ℕ)
    (pin : Fin p → Bool) (ws : Fin N.internal → Bool) (bs : Fin extraBits → Bool) :
    (addPadding N extraBits extraCells).weight pin (Fin.append ws bs) =
      if bs = fun _ => false then N.weight pin ws else 0 := by
  classical
  let cells : Fin ((N.cells+extraBits)+extraCells) → Cell F (N.internal+extraBits) p :=
    Fin.addCases (Fin.addCases (fun i => (networkCells N i).lift extraBits)
      (fun i => forceFalse (Fin.natAdd N.internal i))) (fun _ => unitCell)
  change (∏ i, (cells i).eval pin (Fin.append ws bs)) = _
  rw [Fin.prod_univ_add, Fin.prod_univ_add]
  simp only [cells, Fin.addCases_left, Fin.addCases_right, lift_eval]
  by_cases hb : bs = fun _ => false
  · subst bs
    simp [forceFalse, unitCell, Cell.eval, BitSource.read, networkCells, BitNetwork.weight, BitNetwork.factor]
  · have he : ∃ i, bs i = true := by
      by_contra! hn
      exact hb (funext fun i => Bool.eq_false_iff.mpr (hn i))
    obtain ⟨i,hi⟩ := he
    have hprod : (∏ j, (forceFalse (F:=F) (Fin.natAdd N.internal j)).eval pin (Fin.append ws bs)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [forceFalse, Cell.eval, BitSource.read, hi]
    rw [hprod]
    simp [hb]

@[simp] theorem addPadding_eval [CommSemiring F] (N : BitNetwork F p) (extraBits extraCells : ℕ)
    (pin : Fin p → Bool) : (addPadding N extraBits extraCells).eval pin = N.eval pin := by
  classical
  let g := (addPadding N extraBits extraCells).weight pin
  change (∑ x : Fin (N.internal+extraBits) → Bool, g x) = _
  rw [← (Fin.appendEquiv (α := Bool) N.internal extraBits).sum_comp g, Fintype.sum_prod_type]
  simp [g, Fin.appendEquiv, addPadding_weight, BitNetwork.eval]

/-- A fixed row shape can be used for a finite family of nonuniform gate
counts. Every additional hidden bit consumes a forced cell. -/
def paddedCells [Zero F] [One F] (N : BitNetwork F p) {n c : ℕ}
    (hn : N.internal ≤ n) (hc : N.cells + (n-N.internal) ≤ c) : Fin c → Cell F n p :=
  let b := n-N.internal
  let a := c-(N.cells+b)
  let gate := addPadding N b a
  have hbits : gate.internal = n := by change N.internal + (n-N.internal) = n; omega
  have hcells : gate.cells = c := by change (N.cells+b) + (c-(N.cells+b)) = c; dsimp [b]; omega
  hbits ▸ hcells ▸ networkCells gate

private theorem reindex_eval [CommSemiring F] (N : BitNetwork F p) {n c : ℕ}
    (hb : N.internal = n) (hs : N.cells = c) (pin : Fin p → Bool) :
    (∑ ws : Fin n → Bool, ∏ i : Fin c,
      (((hb ▸ hs ▸ networkCells N) : Fin c → Cell F n p) i).eval pin ws) = N.eval pin := by
  subst n c
  rfl

theorem paddedCells_sum [CommSemiring F] (N : BitNetwork F p) {n c : ℕ}
    (hn : N.internal ≤ n) (hc : N.cells + (n-N.internal) ≤ c) (pin : Fin p → Bool) :
    (∑ ws : Fin n → Bool, ∏ i, (paddedCells N hn hc i).eval pin ws) = N.eval pin := by
  let b := n-N.internal
  let a := c-(N.cells+b)
  have hb : (addPadding N b a).internal = n := by change N.internal + b = n; dsimp [b]; omega
  have hs : (addPadding N b a).cells = c := by change N.cells+b+a=c; dsimp [a,b]; omega
  exact (reindex_eval (addPadding N b a) hb hs pin).trans (addPadding_eval N b a pin)

end ThreeFlat.Diagonal.TraceCircuit

end OAI
