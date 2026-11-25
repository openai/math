import OAI.ThreeFlat.Diagonal.HistogramPartyNetwork
import OAI.ThreeFlat.Diagonal.HistogramBitAddresses

namespace OAI
/-! # Actual data and selector pointers of one local histogram tensor -/

namespace ThreeFlat.Diagonal.HistogramTileNetwork

noncomputable section

open LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector MotifOuterTerms MotifBinaryPacking MotifOrderedCells TraceCircuit
open scoped BigOperators Classical


variable {J E S H : Type*} [Fintype J] [Nonempty J] [Fintype E] [Fintype S]
  [Fintype H] [DecidableEq H] [Nonempty H] {k e n d r h p : ℕ}

private def rectangle {X : Type*} {a b : ℕ} (f : Fin a → Fin b → X) (i : Fin (a*b)) : X :=
  (Function.uncurry f) (finProdFinEquiv.symm i)

private theorem rectangle_at {X : Type*} {a b : ℕ} (f : Fin a → Fin b → X) (i : Fin a) (j : Fin b) :
    rectangle f (finProdFinEquiv (i,j)) = f i j := by rw [rectangle,Equiv.symm_apply_apply]; rfl

private def varying {X : Type*} {a : ℕ} {lengths : Fin a → ℕ} (f : ∀ i, Fin (lengths i) → X)
    (z : Fin (∑ i, lengths i)) : X := (fun q : (i : Fin a) × Fin (lengths i) => f q.1 q.2) (finSigmaFinEquiv.symm z)

private theorem varying_at {X : Type*} {a : ℕ} {lengths : Fin a → ℕ} (f : ∀ i, Fin (lengths i) → X) (i : Fin a) (j : Fin (lengths i)) :
    varying f (finSigmaFinEquiv ⟨i,j⟩) = f i j := congrArg (fun q : (i : Fin a) × Fin (lengths i) => f q.1 q.2) (finSigmaFinEquiv.symm_apply_apply ⟨i,j⟩)

variable (D : PortGraph J E) (G : Supply J S) (j : J) (base w : E → ℕ)
  (B : Header (D.Port j) H (fun a => base a.1.1) k n)
  (portsAt : Fin e ≃ (ports G).Port j) (sw : H → S → ℕ) (v : Histogram H r)

private theorem field_lt {a b c : ℕ} (i : Fin a) (t : Fin b) : c+(b*i.val+t.val) < c+b*a := by
  have hi := Nat.mul_le_mul_left b i.isLt
  rw [Nat.mul_succ] at hi
  have := t.isLt
  omega

variable (old : (a : D.Port j) → Fin (w a.1.1) → BitSource h p)
    (fresh : (a : (ports G).Port j) → Fin (histWidth sw v a.1.1+r*k) → BitSource h p)

private def symbolPtr (a : (ports G).Port j) (i : Fin r) (t : Fin k) :=
  fresh a ⟨_,by simpa only [Nat.mul_comm k r] using field_lt (c:=histWidth sw v a.1.1) i t⟩

private def dataPtr (i : Fin r) (u : Fin n) (b : Fin (base (B.ports u).1.1)) : BitSource h p :=
  let l := base (B.ports u).1.1*i.val+b.val
  if ok : l < w (B.ports u).1.1 then old _ ⟨l,ok⟩ else .constant false

private def resultPtr (u : Fin e) (z : Fin (r*d)) : BitSource h p :=
  if ok : z.val < histWidth sw v (portsAt u).1.1 then fresh _ ⟨z.val,ok.trans_le (Nat.le_add_right _ _)⟩ else .constant false

/-- The flattened public pin map. Each pointer uses only source-port
selection, constant strides, or the finite port's prefix width. -/
def partyPointer : Fin (r*(e*k) + (r*B.arity + e*(r*d))) → BitSource h p :=
  let sel := symbolPtr G j sw v fresh
  let tileHead (i : Fin r) := Fin.append (sel (anchorPort G j) i) (varying (dataPtr D j base w B old i))
  Fin.append (rectangle fun i => rectangle (fun u => sel (portsAt u) i))
    (Fin.append (rectangle tileHead) (rectangle (resultPtr G j portsAt sw v fresh)))

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] [Nonempty H] in
/-- The four physical row classes of a selected local gather. All address
lookups preserve the actual source at each bit, including noncontiguous old wires. -/
theorem partyPointer_select (i : Fin r) (u : Fin e) (t : Fin k) :
    partyPointer D G j base w B portsAt sw v old fresh (d:=d)
      ((finProdFinEquiv (i,finProdFinEquiv (u,t))).castAdd _) =
    fresh (portsAt u) ⟨histWidth sw v (portsAt u).1.1+(k*i.val+t.val),
      by simpa only [Nat.mul_comm k r] using field_lt (c:=histWidth sw v (portsAt u).1.1) i t⟩ := by
  simp only [partyPointer,Fin.append_left,rectangle_at,symbolPtr]

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] [Nonempty H] in
theorem partyPointer_head (i : Fin r) (t : Fin k) :
    partyPointer D G j base w B portsAt sw v old fresh (d:=d)
      (Fin.natAdd _ ((finProdFinEquiv (i,t.castAdd (∑ u, base (B.ports u).1.1))).castAdd _)) =
    fresh (anchorPort G j) ⟨histWidth sw v (anchorPort G j).1.1+(k*i.val+t.val),
      by simpa only [Nat.mul_comm k r] using field_lt (c:=histWidth sw v (anchorPort G j).1.1) i t⟩ := by
  dsimp only [partyPointer,Header.arity]
  simp only [Fin.append_right,Fin.append_left,rectangle_at,symbolPtr]

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] [Nonempty H] in
theorem partyPointer_old (i : Fin r) (u : Fin n) (b : Fin (base (B.ports u).1.1)) :
    partyPointer D G j base w B portsAt sw v old fresh (d:=d)
      (Fin.natAdd _ ((finProdFinEquiv (i,Fin.natAdd k (finSigmaFinEquiv ⟨u,b⟩))).castAdd _)) =
    if live : base (B.ports u).1.1*i.val+b.val<w (B.ports u).1.1
    then old (B.ports u) ⟨_,live⟩ else .constant false := by
  dsimp only [partyPointer,Header.arity]
  simp only [Fin.append_right,Fin.append_left,rectangle_at,varying_at,dataPtr]

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] [Nonempty H] in
theorem partyPointer_output (u : Fin e) (z : Fin (r*d)) :
    partyPointer D G j base w B portsAt sw v old fresh (d:=d)
      (Fin.natAdd _ (Fin.natAdd _ (finProdFinEquiv (u,z)))) =
    if live : z.val<histWidth sw v (portsAt u).1.1
    then fresh (portsAt u) ⟨z.val,live.trans_le (Nat.le_add_right _ _)⟩ else .constant false := by
  simp only [partyPointer,Fin.append_right,rectangle_at,resultPtr]

set_option maxHeartbeats 800000 in
omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] [Nonempty H] in
theorem partyPointer_read (hpad : ∀ a, w a ≤ base a*r) (pin : Fin p → Bool) (hidden : Fin h → Bool)
    (x : D.State (fun a => Fin (2^w a)) j)
    (y : (ports G).State (fun a => (Fin r → Fin (2^k)) × Fin (2^histWidth sw v a)) j)
    (hx : ∀ a b, (old a b).read hidden pin = (x a).val.testBit b.val)
    (hy : ∀ a b, (fresh a b).read hidden pin = (SlotRefinement.selectorWord r k _ (y a)).val.testBit b.val) :
    (fun a => (partyPointer D G j base w B portsAt sw v old fresh (d:=d) a).read hidden pin) =
      partyInputs D G j base B portsAt sw v w hpad x y := by
  have symb (a : (ports G).Port j) (i : Fin r) (t : Fin k) :
      (symbolPtr G j sw v fresh a i t).read hidden pin = (word _).symm ((y a).1 i) t := by
    rw [symbolPtr,hy,selector_field,word_bit]
  funext a
  refine Fin.addCases (fun z => ?_) (fun z => ?_) a
  · obtain ⟨⟨i,z⟩,rfl⟩ := finProdFinEquiv.surjective z
    obtain ⟨⟨u,t⟩,rfl⟩ := finProdFinEquiv.surjective z
    simp only [partyPointer,partyInputs,Fin.append_left,rectangle_at,blocks_at,selectorBits,symb]
  · refine Fin.addCases (fun z => ?_) (fun z => ?_) z
    · obtain ⟨⟨i,q⟩,rfl⟩ := finProdFinEquiv.surjective z
      simp only [partyInputs,arguments,Fin.append_right,Fin.append_left,blocks_at,rawHeads]
      refine Fin.addCases (fun t => ?_) (fun bit => ?_) q
      · calc
          _ = (symbolPtr G j sw v fresh (anchorPort G j) i t).read hidden pin :=
            congrArg (BitSource.read hidden pin)
              (partyPointer_head D G j base w B portsAt sw v old fresh (d:=d) i t)
          _ = _ := (symb _ i t).trans (Fin.append_left _ _ t).symm
      · obtain ⟨⟨u,b⟩,rfl⟩ := finSigmaFinEquiv.surjective bit
        calc
          _ = (dataPtr D j base w B old i u b).read hidden pin :=
            congrArg (BitSource.read hidden pin)
              (partyPointer_old D G j base w B portsAt sw v old fresh (d:=d) i u b)
          _ = (word _).symm
              (MotifDemandPadding.digits _ _ _ (hpad _) (x (B.ports u)) i) b := by
            rw [demand_digit]
            by_cases live : base (B.ports u).1.1*i.val+b.val < w (B.ports u).1.1
            · simpa only [dataPtr,dite_eq_left live] using hx (B.ports u) ⟨_,live⟩
            · simp only [dataPtr,dite_eq_right live,BitSource.read]
              exact (Nat.testBit_lt_two_pow ((x (B.ports u)).isLt.trans_le
                (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt live)))).symm
          _ = _ := (B.encodeRaw_payload ((y (anchorPort G j)).1 i)
            (MotifDemandPadding.readSlice D (fun a => MotifDemandPadding.digits
              (w a) (base a) r (hpad a)) i j x) u b).symm
    · obtain ⟨⟨u,z⟩,rfl⟩ := finProdFinEquiv.surjective z
      simp only [partyPointer,partyInputs,arguments,Fin.append_right,rectangle_at,blocks_at,resultPtr,boundaryInput]
      split
      · rename_i ok
        rw [hy]
        exact (selector_payload (y _) ⟨z.val,ok⟩).trans (word_bit _ _).symm
      · rfl

end

end ThreeFlat.Diagonal.HistogramTileNetwork

end OAI
