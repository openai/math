import OAI.Hierarchy.TaggedOracleCut
import OAI.Hierarchy.TaggedData
import OAI.Hierarchy.TaggedShorterFields
import OAI.Computability.VPVNP.LiveHeaderBits
import OAI.ThreeFlat.Routing.SortStage
import OAI.ThreeFlat.BitNetwork.PinMap

namespace OAI
/-! # Stable sorting with exposed address-width tagged checks

Each target row guesses its source index once. A lexicographic comparison
of its key and source index enforces stability. All payload slices share that
source index, even when the last slice is padded.
-/
namespace Hierarchy.Tagged.ControlSort

open ThreeFlat
open Routing Routing.SortNetwork
open Computability.VPVNP.RAMSerialization
open scoped Classical BigOperators
noncomputable section

abbrev Hole (m a : ℕ) := Fin a × Fin (pins m m)
abbrev Data (m v : ℕ) := Payload m v ⊕ Payload m v
abbrev Pin (m v a : ℕ) := Data m v ⊕ Hole m a
private abbrev Src (m v : ℕ) := BitSource (Fintype.card (Payload m m)) (Fintype.card (Data m v))

private def label {m v : ℕ} (i : Row m) (j : Fin m) : Src m v :=
  .hidden (Fintype.equivFin _ (i,j))

private def bit {m v : ℕ} (out : Bool) (i : Row m) (j : Fin v) : Src m v :=
  .pin (Fintype.equivFin _ (if out then Sum.inr (i,j) else Sum.inl (i,j)))

private def lane {m v : ℕ} (out : Bool) (u : ℕ) (i : Row m) (j : Fin m) : Src m v :=
  if hj : u*m+j.val < v then bit out i ⟨_,hj⟩ else .constant false

private def feed {m v a : ℕ} (j : Fin (Fintype.card (Hole m a))) : Src m v :=
  let p := (Fintype.equivFin (Hole m a)).symm j
  match (portIndex m m).symm p.2 with
  | .inl (i,b) => lane false p.1.val i b
  | .inr (.inl (i,b)) => label i b
  | .inr (.inr (i,b)) => lane true p.1.val i b

private def compareKey {m v k : ℕ} (key : Fin k → Fin v) (i : Row m) :
    Fin (m+k) → Src m v :=
  Fin.append (label i) (fun j => bit true i (key j))

private def wire {m v k : ℕ} (key : Fin k → Fin v) (e : Edge m) :
    Fin ((m+k)+(m+k)) → Src m v :=
  Fin.append (compareKey key e.1) (compareKey key (next e))

private def raw {m v k : ℕ} (F : Type*) [Zero F] [One F] (a : ℕ) (key : Fin k → Fin v) :
    BitNetwork F (Fintype.card (Data m v ⊕ Fin (Fintype.card (Hole m a)))) :=
  OracleCut.network (fun _ : Edge m => compareBits F (m+k)) (wire key) feed

private def name {m v a : ℕ} : (Data m v ⊕ Fin (Fintype.card (Hole m a))) ≃ Pin m v a :=
  Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin _).symm

/-- The two arrays and all the independent tagged calls are named external ports. -/
def cut {m v k : ℕ} (F : Type*) [Zero F] [One F] (a : ℕ) (key : Fin k → Fin v) :
    BitNetwork F (Fintype.card (Pin m v a)) :=
  (raw (m:=m) F a key).restrictPins (fun j => some (Fintype.equivFin _
    (name (m:=m) (v:=v) (a:=a) ((Fintype.equivFin _).symm j))))

private theorem raw_value {m v k : ℕ} (F : Type*) [CommSemiring F] (a : ℕ) (key : Fin k → Fin v)
    (x : Data m v → Bool) (z : Hole m a → Bool) :
    TypedWiring.value (cut F a key) (Sum.elim x z) =
      TypedWiring.value (raw F a key) (Sum.elim x (z ∘ (Fintype.equivFin _).symm)) := by
  unfold TypedWiring.value cut
  rw [BitNetwork.restrictPins_eval]
  apply congrArg (raw F a key).eval
  funext j
  obtain ⟨p,rfl⟩ := (Fintype.equivFin (Data m v ⊕ Fin (Fintype.card (Hole m a)))).surjective j
  cases p <;> simp [name]


private def guesses (m : ℕ) : (Row m → Row m) ≃ (Fin (Fintype.card (Payload m m)) → Bool) :=
  (((Equiv.refl _).arrowCongr (wordBits m)).trans (Equiv.curry _ _ _).symm).trans
    ((Fintype.equivFin _).arrowCongr (Equiv.refl _))

@[simp] private theorem guesses_at {m : ℕ} (t : Row m → Row m) (i : Row m) (b : Fin m) :
    guesses m t (Fintype.equivFin (Payload m m) (i,b)) = wordBits m (t i) b := by
  simp [guesses, Equiv.curry]

private theorem address_word (m : ℕ) (i : Row m) : addressEquiv m (wordBits m i) = i := by
  apply (addressEquiv m).symm.injective
  rw [Equiv.symm_apply_apply]
  exact funext fun j => (Computability.VPVNP.LiveHeader.testBit_wordBits i j).symm

private def sliceInput {m v : ℕ} (u : ℕ) (x y : Payload m v → Bool) (t : Row m → Row m) :
    Fin (pins m m) → Bool :=
  Sum.elim (fun p => TaggedShorterFields.slice m (Function.curry x p.1) u p.2)
    (Sum.elim (fun p => wordBits m (t p.1) p.2)
      (fun p => TaggedShorterFields.slice m (Function.curry y p.1) u p.2)) ∘ (portIndex m m).symm

private theorem feed_read {m v a : ℕ} (x y : Payload m v → Bool) (t : Row m → Row m)
    (u : Fin a) (j : Fin (pins m m)) :
    ((feed (Fintype.equivFin (Hole m a) (u,j)) : Src m v)).read (guesses m t)
      (Sum.elim x y ∘ (Fintype.equivFin _).symm) = sliceInput u.val x y t j := by
  obtain ⟨p,rfl⟩ := (portIndex m m).surjective j
  rcases p with ⟨i,b⟩ | (⟨i,b⟩ | ⟨i,b⟩)
  · simp only [feed, Equiv.symm_apply_apply, sliceInput, Function.comp_apply, Sum.elim_inl,
      lane, TaggedShorterFields.slice]
    split <;> simp [bit, BitSource.read, Function.curry]
  · simp [feed, label, BitSource.read, sliceInput]
  · simp only [feed, Equiv.symm_apply_apply, sliceInput, Function.comp_apply, Sum.elim_inr,
      lane, TaggedShorterFields.slice]
    split <;> simp [bit, BitSource.read, Function.curry]

private theorem slice_coefficient {F : Type*} [CommSemiring F] {m v a : ℕ}
    (positive : 0 < a) (room : v ≤ a*m) (x y : Payload m v → Bool) (t : Row m → Row m) :
    (∏ u : Fin a, coeff F m m (sliceInput u.val x y t)) =
      if Valid (Function.curry x) t (Function.curry y) then 1 else 0 := by
  let : Nonempty (Fin a) := ⟨⟨0,positive⟩⟩
  let emb : Bits v ↪ (Fin a → Bits m) :=
    ⟨fun z i => TaggedShorterFields.slice m z i.val, fun {z z'} he =>
      (TaggedShorterFields.eq_iff_slices room z z').mp (congrFun he)⟩
  have val := (valid_map_iff emb (Function.curry x) (Function.curry y) t).symm.trans
    (valid_iff_slices (emb ∘ Function.curry x) (emb ∘ Function.curry y) t)
  have hs (u : Fin a) : source (sliceInput u.val x y t) = fun r => emb (Function.curry x r) u := by
    funext r b
    simp [source,sliceInput,emb]; rfl
  have ht (u : Fin a) : target (sliceInput u.val x y t) = fun r => emb (Function.curry y r) u := by
    funext r b
    simp [target,sliceInput,emb]; rfl
  have ha (u : Fin a) : tag (sliceInput u.val x y t) = t := by
    funext r
    simp [tag,sliceInput]
  simp only [coeff,hs,ht,ha,Fintype.prod_boole]
  simp only [Function.comp_apply] at val
  by_cases hg : Valid (Function.curry x) t (Function.curry y)
  · simp [hg,val.mp hg]
  · simp [hg,mt val.mpr hg]

private def keyValue {k v : ℕ} (key : Fin k → Fin v) (x : Bits v) := addressEquiv k (x ∘ key)

private theorem compare_read {m v k : ℕ} (key : Fin k → Fin v) (i : Row m)
    (x y : Payload m v → Bool) (t : Row m → Row m) :
    (fun j => (compareKey key i j).read (guesses m t)
      (Sum.elim x y ∘ (Fintype.equivFin _).symm)) =
      Fin.append (wordBits m (t i)) ((Function.curry y i) ∘ key) := by
  funext j
  cases j using Fin.addCases <;>
    simp [compareKey,label,bit,BitSource.read,Function.curry,-Fin.natAdd_eq_addNat]

private theorem compares {F : Type*} [CommSemiring F] {m v k : ℕ} (key : Fin k → Fin v)
    (x y : Payload m v → Bool) (t : Row m → Row m) :
    (∏ e : Edge m, (compareBits F (m+k)).eval (fun j => (wire key e j).read (guesses m t)
      (Sum.elim x y ∘ (Fintype.equivFin _).symm))) =
      if AdjacentIncreasing (fun i => toLex (keyValue key (Function.curry y i),t i)) then 1 else 0 := by
  simp only [compareBits_eval,wire,Fin.append_left,Fin.append_right,compare_read,
    wordValue_append_lt_iff,address_word,Fintype.prod_boole,← adjacent_edges,keyValue]

private theorem stable_iff {m v k : ℕ} (key : Fin k → Fin v) (x y : Payload m v → Bool)
    (t : Row m → Row m) :
    Valid (Function.curry x) t (Function.curry y) ∧
      AdjacentIncreasing (fun i => toLex (keyValue key (Function.curry y i),t i)) ↔
    t = ⇑(Tuple.sort (keyValue key ∘ Function.curry x)) ∧ sortedPins key x = y := by
  let s := Function.curry x
  let d := Function.curry y
  let σ := Tuple.sort (keyValue key ∘ s)
  have unc : Function.uncurry (s ∘ σ) = sortedPins key x := rfl
  constructor
  · rintro ⟨⟨bij, carried⟩,adj⟩
    let e := Equiv.ofBijective t bij
    have routed : StableRouting (keyValue key) s e.symm t d := by
      refine ⟨⟨e.symm.bijective, fun i => ?_⟩,adj⟩
      have inv : t (e.symm i) = i := e.apply_symm_apply _
      exact Prod.ext inv ((carried _).trans (congrArg s inv))
    obtain ⟨_, ht, hd⟩ := (stableRouting_iff ..).mp routed
    exact ⟨ht,unc.symm.trans (congrArg Function.uncurry hd).symm⟩
  · rintro ⟨rfl, jout⟩
    have out : d = s ∘ σ := by
      exact congrArg Function.curry (jout.symm.trans unc.symm)
    have good := (stableRouting_iff (keyValue key) s σ.symm σ d).mpr ⟨rfl,rfl,out⟩
    exact ⟨⟨σ.bijective,congrFun out⟩,good.2⟩


/-- Plugging the addressed tag kernels enforces the unique stable output,
including ties among arbitrarily many equal keys. -/
theorem contract {F : Type*} [CommSemiring F] {m v k a : ℕ}
    (positive : 0 < a) (room : v ≤ a*m) (key : Fin k → Fin v) (x y : Payload m v → Bool) :
    (∑ z : Hole m a → Bool, TypedWiring.value (cut F a key) (Sum.elim (Sum.elim x y) z) *
        ∏ u : Fin a, coeff F m m (fun j => z (u,j))) =
      if sortedPins key x = y then 1 else 0 := by
  let E := (Fintype.equivFin (Hole m a)).arrowCongr (Equiv.refl Bool)
  let f (z : Fin (Fintype.card (Hole m a)) → Bool) :=
    ∏ u : Fin a, coeff F m m (fun j => z (Fintype.equivFin (Hole m a) (u,j)))
  have repack : (∑ z : Hole m a → Bool, TypedWiring.value (cut F a key) (Sum.elim (Sum.elim x y) z) *
        ∏ u : Fin a, coeff F m m (fun j => z (u,j))) =
      ∑ z, TypedWiring.value (raw F a key) (Sum.elim (Sum.elim x y) z) * f z := by
    apply Fintype.sum_equiv E
    intro z
    rw [raw_value]
    simp [f,E,Equiv.arrowCongr]
  rw [repack,raw,OracleCut.contract,← (guesses m).sum_comp]
  have term (t : Row m → Row m) :
      (∏ e : Edge m, (compareBits F (m+k)).eval (fun j => (wire key e j).read (guesses m t)
        (Sum.elim x y ∘ (Fintype.equivFin _).symm))) *
        f (fun j => (feed (m:=m) (v:=v) (a:=a) j).read (guesses m t) (Sum.elim x y ∘ (Fintype.equivFin _).symm)) =
      if t = ⇑(Tuple.sort (keyValue key ∘ Function.curry x)) ∧ sortedPins key x = y
        then 1 else 0 := by
    rw [compares]
    simp only [f,feed_read,slice_coefficient positive room]
    have hst := stable_iff key x y t
    split_ifs <;> simp_all
  simp_rw [term,ite_and]
  simp

/-- Number of cells, hidden bits, and open ports in the cut. In particular
the coefficient of the number of slices is linear in the address width. -/
theorem size {F : Type*} [Zero F] [One F] {m v k a : ℕ} (key : Fin k → Fin v) :
    (cut (m:=m) F a key).cells + (cut (m:=m) F a key).internal + Fintype.card (Pin m v a) ≤
      2^m * (2*v + m + (m+k+1) + (m+k+2)*176 + 87*a*m) := by
  have card : Fintype.card (Edge m) ≤ 2^m := by
    simpa using Fintype.card_subtype_le (fun i : Row m => i.val+1 < 2^m)
  have holes : Fintype.card (Hole m a) = a*pins m m := by simp [Hole]
  have ports : Fintype.card (Pin m v a) = (2^m*v+2^m*v) + a*pins m m := by
    simp [Pin,Data,Hole,Payload,Fintype.card_sum]
  change (raw (m:=m) F a key).cells + (raw (m:=m) F a key).internal + _ ≤ _
  rw [raw,OracleCut.size]
  simp only [compareBits_cells,compareBits_internal, Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    holes, ports, Payload,Fintype.card_prod,Fintype.card_fin,pins,Nat.cast_id]
  calc
    _ ≤ (2^m)*((m+k+2)*96) + (2^m)*((m+k+1)+(m+k+2)*80) + 2^m*m +
        28*(a*(2^m*m+(2^m*m+2^m*m))) + ((2^m*v+2^m*v)+a*(2^m*m+(2^m*m+2^m*m))) := by gcongr
    _ = _ := by ring

/-- If the row has at most `C*m` bits, `C+1` address-width calls always suffice. -/
theorem bounded_slices {m v C : ℕ} (hv : v ≤ C*m) : 0 < C+1 ∧ v ≤ (C+1)*m :=
  ⟨by omega, hv.trans (Nat.mul_le_mul_right m (Nat.le_succ _))⟩

end
end Hierarchy.Tagged.ControlSort

end OAI
