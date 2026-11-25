import OAI.ThreeFlat.Routing.PackedRows
import OAI.ThreeFlat.Routing.SwitchPins
import OAI.ThreeFlat.BitNetworkGlue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic
import OAI.LinearAlgebra.SpectralBooks.Batcher

namespace OAI
/-! # A trivalent realization of Batcher's bitonic sorter

Sequential stages sum over one packed intermediate array.  Parallel stages and
fixed permutations use direct pin addressing.  The deterministic comparison
relations therefore give each input array precisely one output in every stage.
-/

noncomputable section
open scoped Classical BigOperators
namespace ThreeFlat.Routing.BitonicSchedule

open LinearAlgebra.SpectralBooks.Batcher
open SortNetwork (Payload Records pack)

abbrev Width (k u : ℕ) := Fintype.card (Payload k u)
abbrev PairSize (k u : ℕ) := Width k u + Width k u
private abbrev ArrayV (k u : ℕ) := Wires k (Fin (2^u))

private def key {k u : ℕ} (i : Fin (2^k)) (j : Fin u) := Fintype.equivFin (Payload k u) (i,j)
private def bits {k u : ℕ} (x : ArrayV k u) : Fin (Width k u) → Bool :=
  pack fun i => (addressEquiv u).symm (x i)

@[simp] private theorem bits_key {k u : ℕ} (x : ArrayV k u) (i : Fin (2^k)) (j : Fin u) :
    bits x (key i j) = (addressEquiv u).symm (x i) j := by simp [bits,pack,key]

private def decode {k u : ℕ} (h : Fin (Width k u) → Bool) : ArrayV k u :=
  fun i => addressEquiv u (fun j => h (key i j))

@[simp] private theorem bits_decode {k u : ℕ} (h : Fin (Width k u) → Bool) : bits (decode h) = h := by
  funext n
  obtain ⟨⟨i,j⟩,rfl⟩ := (Fintype.equivFin (Payload k u)).surjective n
  change bits (decode h) (key i j) = _
  rw [bits_key]
  exact congrFun ((addressEquiv u).symm_apply_apply (fun t => h (key i t))) j

@[simp] private theorem decode_bits {k u : ℕ} (x : ArrayV k u) : decode (bits x) = x := by
  funext i
  simp [decode]

private def move {k l u : ℕ} (f : Fin (2^k) → Fin (2^l)) (n : Fin (Width k u)) : Fin (Width l u) :=
  let p := (Fintype.equivFin (Payload k u)).symm n
  key (f p.1) p.2

private theorem bits_move {k l u : ℕ} (f : Fin (2^k) → Fin (2^l)) (x : ArrayV l u) :
    (fun n => bits x (move f n)) = bits (x ∘ f) := by
  funext n
  simp [move, bits, pack, key, Function.uncurry]

private def pull {I : Type*} [Fintype I] {p : ℕ} {sz : I → ℕ} {K : Type*}
    (N : ∀ i, BitNetwork K (sz i)) (f : ∀ i, Fin (sz i) → Fin p) :=
  BitNetwork.glue N (fun i j => (BitSource.pin (f i j) : BitSource 0 p))

private theorem pull_eval {I : Type*} [Fintype I] {p : ℕ} {sz : I → ℕ} {K : Type*} [CommSemiring K]
    (N : ∀ i, BitNetwork K (sz i)) (f : ∀ i, Fin (sz i) → Fin p) (v : Fin p → Bool) :
    (pull N f).eval v = ∏ i, (N i).eval (fun j => v (f i j)) := by
  simp [pull,BitNetwork.glue_eval,BitSource.read]

private def pairMap {a b : ℕ} (f g : Fin a → Fin b) : Fin (a+a) → Fin (b+b) :=
  Fin.append (fun i => (f i).castAdd b) (fun i => Fin.natAdd b (g i))

private theorem pairMap_at {a b : ℕ} (f g : Fin a → Fin b) (x y : Fin b → Bool) :
    (fun j => Fin.append x y (pairMap f g j)) = Fin.append (x ∘ f) (y ∘ g) := by
  funext j
  exact Fin.addCases (fun i => by simp only [pairMap, Fin.append_left, Function.comp_apply])
    (fun i => by simp only [pairMap, Fin.append_right, Function.comp_apply]) j

private def perm {K : Type*} [Zero K] [One K] {k u : ℕ} (f : Fin (2^k) → Fin (2^k)) :
    BitNetwork K (PairSize k u) where
  internal := 0
  cells := Width k u
  source n := ![.pin ((move f n).castAdd _), .pin (Fin.natAdd _ n), .constant false]
  table _ b := if b 1 = b 0 then 1 else 0

private theorem prod_checks {I K : Type*} [Fintype I] [CommSemiring K] (P : I → Prop)
    [DecidablePred P] : (∏ i, (if P i then 1 else 0 : K)) = if ∀ i, P i then 1 else 0 := by
  by_cases h : ∀ i, P i
  · simp [h]
  · obtain ⟨i,hi⟩ := Classical.not_forall.mp h
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

private theorem perm_eval {K : Type*} [CommSemiring K] {k u : ℕ} (f : Fin (2^k) → Fin (2^k))
    (x y : ArrayV k u) : (perm (K := K) f).eval (Fin.append (bits x) (bits y)) =
      if y = x ∘ f then 1 else 0 := by
  change (∑ _ : Fin 0 → Bool, ∏ i : Fin (Width k u), _) = _
  rw [Fintype.sum_unique]
  simp only [BitNetwork.factor, perm, BitSource.read, Matrix.cons_val_one, Matrix.cons_val_zero,
    Fin.append_left, Fin.append_right]
  have e : (∀ n : Fin (Width k u), bits y n = bits x (move f n)) ↔ y = x ∘ f := by
    constructor
    · intro h
      have a : bits y = bits (x ∘ f) := (funext h).trans (bits_move f x)
      simpa using congrArg (decode (k := k) (u := u)) a
    · rintro rfl n
      exact (congrFun (bits_move f x) n).symm
  simp only [prod_checks,e]

private def branch {k : ℕ} : Bool → Fin (2^k) → Fin (2^(k+1))
  | false => low
  | true => high

private def side {α : Type*} (a b : α) : Bool → α
  | false => a
  | true => b

private def parallel {K : Type*} {k u : ℕ} (l r : BitNetwork K (PairSize k u)) :
    BitNetwork K (PairSize (k+1) u) :=
  pull (side l r) (fun b => pairMap (move (branch b)) (move (branch b)))

private def rowPair {k u : ℕ} (i : Fin (2^k)) : Fin (u+u) → Fin (Width (k+1) u) :=
  Fin.append (key (low i)) (key (high i))

private def compareLayer {K : Type*} (k u : ℕ) (C : BitNetwork K ((u+u)+(u+u))) : BitNetwork K (PairSize (k+1) u) :=
  pull (fun _ : Fin (2^k) => C) (fun i => pairMap (rowPair i) (rowPair i))

private theorem rowPair_at {k u : ℕ} (i : Fin (2^k)) (x : ArrayV (k+1) u) :
    bits x ∘ rowPair i = Fin.append ((addressEquiv u).symm (x (low i))) ((addressEquiv u).symm (x (high i))) := by
  funext j
  exact Fin.addCases (fun t => by simp only [rowPair, Fin.append_left, Function.comp_apply, bits_key])
    (fun t => by simp only [rowPair, Fin.append_right, Function.comp_apply, bits_key]) j

private theorem eq_join {k : ℕ} {α : Type*} (y : Wires (k+1) α) (a b : Wires k α) :
    (∀ i, y (low i) = a i ∧ y (high i) = b i) ↔ y = join a b := by
  constructor
  · intro h
    funext j
    rcases low_or_high j with ⟨i,rfl⟩ | ⟨i,rfl⟩
    · simpa using (h i).1
    · simpa using (h i).2
  · rintro rfl i
    simp

/-- Semantic interface of one width-`u` compare-exchange. -/
def ComparatorCorrect {K : Type*} [CommSemiring K] {u : ℕ} (C : BitNetwork K ((u+u)+(u+u))) : Prop :=
  ∀ a b c d : Fin u → Bool, C.eval (Fin.append (Fin.append a b) (Fin.append c d)) =
    if c = (addressEquiv u).symm (min (addressEquiv u a) (addressEquiv u b)) ∧
       d = (addressEquiv u).symm (max (addressEquiv u a) (addressEquiv u b)) then 1 else 0

private theorem compareLayer_eval {K : Type*} [CommSemiring K] {k u : ℕ} (C : BitNetwork K ((u+u)+(u+u))) (hC : ComparatorCorrect C) (x y : ArrayV (k+1) u) :
    (compareLayer k u C).eval (Fin.append (bits x) (bits y)) =
      if y = Network.compareHalves.eval x then 1 else 0 := by
  have ev (a b c d : Fin u → Bool) := hC a b c d
  simp only [compareLayer, pull_eval, pairMap_at, rowPair_at, ev, Equiv.apply_symm_apply, Equiv.apply_eq_iff_eq]
  rw [prod_checks]
  apply ite_congr _ (fun _ => rfl) (fun _ => rfl)
  exact propext (eq_join y _ _)

private def seqWire {p : ℕ} : Bool → Fin (p+p) → BitSource p (p+p)
  | false => Fin.append (fun i => .pin (i.castAdd p)) BitSource.hidden
  | true => Fin.append BitSource.hidden (fun i => .pin (Fin.natAdd p i))

private def seqN {K : Type*} {p : ℕ} (a b : BitNetwork K (p+p)) : BitNetwork K (p+p) :=
  BitNetwork.glue (side a b) seqWire

private theorem seq_read {p : ℕ} (x y h : Fin p → Bool) (t : Bool) :
    (fun j => (seqWire t j).read h (Fin.append x y)) =
      side (Fin.append x h) (Fin.append h y) t := by
  funext j
  cases t <;> exact Fin.addCases (fun i => by simp only [side, seqWire, BitSource.read, Fin.append_left])
    (fun i => by simp only [side, seqWire, BitSource.read, Fin.append_right]) j

private def compile {K : Type*} [Zero K] [One K] {u : ℕ} (C : BitNetwork K ((u+u)+(u+u))) : {k : ℕ} → Network k → BitNetwork K (PairSize k u)
  | _, .nil => perm id
  | _, .reverse => perm Fin.rev
  | _, .compareHalves => compareLayer _ u C
  | _, .parallel a b => parallel (compile C a) (compile C b)
  | _, .seq a b => seqN (compile C a) (compile C b)

private theorem compile_eval {K : Type*} [CommSemiring K] {k u : ℕ} (C : BitNetwork K ((u+u)+(u+u))) (hC : ComparatorCorrect C) (N : Network k) (x y : ArrayV k u) :
    (compile C N).eval (Fin.append (bits x) (bits y)) = if y = N.eval x then 1 else 0 := by
  induction N with
  | nil => exact perm_eval id x y
  | reverse => exact perm_eval Fin.rev x y
  | compareHalves => exact compareLayer_eval C hC x y
  | parallel l r hl hr =>
    simp only [compile,parallel,pull_eval,Fintype.prod_bool,pairMap_at,side,branch]
    change (compile C r).eval (Fin.append (fun n => bits x (move high n)) (fun n => bits y (move high n))) *
      (compile C l).eval (Fin.append (fun n => bits x (move low n)) (fun n => bits y (move low n))) = _
    rw [bits_move, bits_move, bits_move, bits_move, hl, hr]
    have e : y = Network.eval (.parallel l r) x ↔
        y ∘ low = l.eval (x ∘ low) ∧ y ∘ high = r.eval (x ∘ high) := by
      rw [Network.eval, ← eq_join, forall_and]
      simp only [funext_iff,Function.comp_apply]
    by_cases a : y ∘ low = l.eval (x ∘ low) <;> by_cases b : y ∘ high = r.eval (x ∘ high) <;> simp [e,a,b]
  | seq a b ha hb =>
    simp only [compile,seqN,BitNetwork.glue_eval,Fintype.prod_bool,seq_read,side]
    rw [Finset.sum_eq_single_of_mem (bits (a.eval x)) (Finset.mem_univ _)]
    · rw [ha,hb,ite_eq_left rfl,mul_one]; rfl
    · intro h _ hn
      have nz : decode h ≠ a.eval x := fun he => hn (by simpa using congrArg bits he)
      conv_lhs => rw [← bits_decode h]
      rw [ha,ite_eq_right nz,mul_zero]

/-- The unique output rows of the fixed ascending sorter on packed binary words. -/
def sorted {m u : ℕ} (X : Records m u) : Records m u :=
  fun i => (addressEquiv u).symm ((sortNet m).eval (fun j => addressEquiv u (X j)) i)

/-- The first group of packed pins supplies the input; the second supplies the proposed output. -/
def network {K : Type*} [Zero K] [One K] (m u : ℕ) (C : BitNetwork K ((u+u)+(u+u))) : BitNetwork K (PairSize m u) :=
  compile C (sortNet m)

theorem network_eval {K : Type*} [CommSemiring K] (m u : ℕ) (C : BitNetwork K ((u+u)+(u+u))) (hC : ComparatorCorrect C) (X Y : Records m u) :
    (network m u C).eval (Fin.append (pack X) (pack Y)) = if Y = sorted X then 1 else 0 := by
  let x : ArrayV m u := fun i => addressEquiv u (X i)
  let y : ArrayV m u := fun i => addressEquiv u (Y i)
  have hx : bits x = pack X := by simp [bits,x]
  have hy : bits y = pack Y := by simp [bits,y]
  rw [network, ← hx, ← hy, compile_eval C hC]
  have e : y = (sortNet m).eval x ↔ Y = sorted X := by
    constructor
    · intro h
      funext i
      apply (addressEquiv u).injective
      simpa [sorted,y,x] using congrFun h i
    · intro h
      funext i
      change addressEquiv u (Y i) = _
      rw [h]
      exact (addressEquiv u).apply_symm_apply _
  simp only [e]

private def units : {k : ℕ} → Network k → ℕ
  | k, .nil => 2^k
  | k, .reverse => 2^k
  | k+1, .compareHalves => 2^k
  | _, .parallel a b => units a + units b
  | k, .seq a b => units a + units b + 2^k

private theorem compile_cells {K : Type*} [Zero K] [One K] {k u : ℕ} (C : BitNetwork K ((u+u)+(u+u))) (hc : C.cells ≤ 2048*(u+1)) (N : Network k) :
    (compile C N).cells ≤ 2048*(u+1)*units N := by
  induction N with
  | nil | reverse =>
    simp only [compile, perm, units, Width, Payload, Fintype.card_prod, Fintype.card_fin]
    rw [Nat.mul_comm (2^_) u]
    exact Nat.mul_le_mul_right _ (by omega : u ≤ 2048*(u+1))
  | @compareHalves k =>
    simp only [compile, compareLayer, pull, BitNetwork.glue_cells, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, units]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left (2^k) hc
  | parallel a b ha hb =>
    simp only [compile,parallel,pull,BitNetwork.glue_cells,Fintype.sum_bool,side,units]
    simp only [Nat.mul_add] at *
    omega
  | seq a b ha hb =>
    simp only [compile,seqN,BitNetwork.glue_cells,Fintype.sum_bool,side,units]
    simp only [Nat.mul_add] at *
    omega

private theorem compile_internal {K : Type*} [Zero K] [One K] {k u : ℕ}
    (C : BitNetwork K ((u+u)+(u+u))) (hc : C.internal ≤ 2048*(u+1)) (N : Network k) :
    (compile C N).internal ≤ 2048*(u+1)*units N := by
  induction N with
  | nil | reverse => exact Nat.zero_le _
  | @compareHalves k =>
    simp only [compile,compareLayer,pull,BitNetwork.glue_internal,zero_add,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,units]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left (2^k) hc
  | parallel a b ha hb =>
    simp only [compile,parallel,pull,BitNetwork.glue_internal,zero_add,Fintype.sum_bool,side,units]
    simp only [Nat.mul_add] at *
    omega
  | @seq k a b ha hb =>
    have width : Width k u ≤ 2048*(u+1)*2^k := by
      simp only [Width,Payload,Fintype.card_prod,Fintype.card_fin]
      rw [Nat.mul_comm (2^k) u]
      exact Nat.mul_le_mul_right _ (by omega : u ≤ 2048*(u+1))
    simp only [compile,seqN,BitNetwork.glue_internal,Fintype.sum_bool,side,units]
    simp only [Nat.mul_add] at *
    omega

private theorem merge_units (m : ℕ) : units (mergeNet m) ≤ 2^m*(2*m+1) := by
  induction m with
  | zero => simp [mergeNet,units]
  | succ m ih => simp only [mergeNet,units,pow_succ]; nlinarith

private theorem sort_units (m : ℕ) : units (sortNet m) ≤ 2*2^m*(m+1)^2 := by
  induction m with
  | zero => simp [sortNet,units]
  | succ m ih =>
    have hm := merge_units (m+1)
    simp only [sortNet,units,pow_succ] at *
    nlinarith [Nat.zero_le (2^m * m)]

theorem network_cells {K : Type*} [Zero K] [One K] (m u : ℕ) (C : BitNetwork K ((u+u)+(u+u))) (hc : C.cells ≤ 2048*(u+1)) :
    (network m u C).cells ≤ 4096*(u+1)*(2^m)*(m+1)^2 := by
  calc
    _ ≤ 2048*(u+1)*units (sortNet m) := compile_cells C hc _
    _ ≤ 2048*(u+1)*(2*2^m*(m+1)^2) := Nat.mul_le_mul_left _ (sort_units m)
    _ = _ := by ring

theorem network_internal {K : Type*} [Zero K] [One K] (m u : ℕ)
    (C : BitNetwork K ((u+u)+(u+u))) (hc : C.internal ≤ 2048*(u+1)) :
    (network m u C).internal ≤ 4096*(u+1)*(2^m)*(m+1)^2 := by
  calc
    _ ≤ 2048*(u+1)*units (sortNet m) := compile_internal C hc _
    _ ≤ 2048*(u+1)*(2*2^m*(m+1)^2) := Nat.mul_le_mul_left _ (sort_units m)
    _ = _ := by ring

end ThreeFlat.Routing.BitonicSchedule

end
end OAI
