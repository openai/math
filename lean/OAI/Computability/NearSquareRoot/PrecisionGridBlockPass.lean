import OAI.Computability.NearSquareRoot.PrecisionBlockPhaseRank
import OAI.Computability.NearSquareRoot.PrecisionGridAddressLookup
import OAI.Computability.NearSquareRoot.PrecisionTensorPass

/-! # The tensor phase pass in the physical order of synchronized blocks -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace FixedPoint

open IntegerMultiplication Code BoxFin SynchronizedBlocks PhaseStream ShortFourier

/-- Composing the local rank equivalences reads the synchronized block
tensor on its actual padded tape address. -/
def blockCoefficient {k l : ℕ} {b : List (ℕ × ℕ)} (hb : BoxShape.Valid k l b)
    (hd : 4 ≤ b.length) (phase : ∀ j, BlockAddress (BoxAxis b) j → ℂ)
    (pos : Fin (2^k)) : ℂ :=
  letI := modulus_neZero hb
  ∏ j, phase j (regroup hd (BoxAxis b) ((recordIndex hb).symm pos) j)

/-- A guarded table stores one local phase for each possible padded address
of its block, including all unused cyclic slots. -/
def blockLabelsMatch {α : Type*} {k l : ℕ} {b : List (ℕ × ℕ)} (hb : BoxShape.Valid k l b)
    (v : ∀ j, Fin (blockRadix b j) → α) (ideal : α → ℂ)
    (phase : ∀ j, BlockAddress (BoxAxis b) j → ℂ) : Prop :=
  letI := modulus_neZero hb
  ∀ j a, ideal (v j (blockAddressRank hb j a)) = phase j a

/-- The list of programmed phases is the exact block diagonal in global
array order. This equality fixes the orientation even for nonuniform block
widths and for the extended final block. -/
theorem synchronizedPhase_order {α : Type*} {k l : ℕ} {b : List (ℕ × ℕ)}
    (hb : BoxShape.Valid k l b) (hd : 4 ≤ b.length)
    (v : ∀ j, Fin (blockRadix b j) → α) (ideal : α → ℂ)
    (phase : ∀ j, BlockAddress (BoxAxis b) j → ℂ) (hmatch : blockLabelsMatch hb v ideal phase) :
    List.ofFn (blockCoefficient hb hd phase) =
      (addresses ((List.range (b.length/4)).map (radixTable v))).map (fun xs => (xs.map ideal).prod) := by
  let _ := modulus_neZero hb
  let labels := (addresses ((List.range (b.length/4)).map (radixTable v))).map (fun xs => (xs.map ideal).prod)
  have hlen : labels.length = 2^k := by
    dsimp [labels]
    rw [List.length_map, length_addresses, List.map_map]
    exact (radixTable_count v).trans (prod_blockRadix hb hd)
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using hlen.symm
  intro t ht hu
  let pos : Fin (2^k) := ⟨t, by simpa only [List.length_ofFn] using ht⟩
  let x := (recordIndex hb).symm pos
  let loc j := regroup hd (BoxAxis b) x j
  have hr := recordIndex_blockRank hb hd x
  change (recordIndex hb x).val = CRT.rank (blockRadix b) (fun j => (blockAddressRank hb j (loc j)).val) at hr
  have eq := radixTable_coefficient v ideal (fun j => blockAddressRank hb j (loc j))
  rw [← hr, show recordIndex hb x = pos from Equiv.apply_symm_apply ..] at eq
  change labels[t]? = some _ at eq
  rw [List.getElem?_eq_getElem hu, Option.some.injEq] at eq
  simp only [List.getElem_ofFn]
  change (∏ j, phase j (loc j)) = labels[t]
  rw [eq]
  apply Finset.prod_congr rfl
  exact fun j _ => (hmatch j (loc j)).symm

/-- Applying the block diagonal by the prefix multiplier is a single uniform
tape program. Its resource bounds and local error refer to the data array
in the original physical order. -/
theorem synchronizedPhasePass {I α : Type} (k l : I → ℕ) (b : I → List (ℕ × ℕ))
    (hb : ∀ i, BoxShape.Valid (k i) (l i) (b i)) (hd : ∀ i, 4 ≤ (b i).length)
    (v : ∀ i j, Fin (blockRadix (b i) j) → α) (ideal : I → α → ℂ)
    (phase : ∀ i j, BlockAddress (BoxAxis (b i)) j → ℂ)
    (hmatch : ∀ i, blockLabelsMatch (hb i) (v i) (ideal i) (phase i))
    (store : (i : I) → α → Record (guardedK (k i)))
    (hunit : ∀ i j q, ‖ideal i (v i j q)‖ = 1)
    (herr : ∀ i j q, ‖value _ (store i (v i j q)) - ideal i (v i j q)‖ ≤
      1 / (2 : ℝ)^(70 * guardedK (k i)))
    (x : (i : I) → Fin (2^k i) → Record (k i)) (hk : ∀ i, 1 ≤ k i)
    (hx : ∀ i, ‖recordArray (x i)‖ ≤ (2 : ℝ)^(13*k i)) :
    ∃ (out : (i : I) → Fin (2^k i) → Record (k i))
      (hu : ∀ i z, ‖blockCoefficient (hb i) (hd i) (phase i) z‖ = 1),
      Space.BoundedTask (fun i => (2^k i+1)*GridTask.recordCost (k i))
        (fun i => (2^k i+1)*(k i+1))
        (tensorPassQuery k (fun i => (b i).length/4) (fun i => radixTable (v i)) store x)
        (fun i => send (List.ofFn fun z => Dusk.mark (out i z))) ∧
      ∀ i, ‖recordArray (out i) -
        phaseLayerIsometry (blockCoefficient (hb i) (hd i) (phase i)) (hu i) (recordArray (x i))‖ ≤
          1 / (2 : ℝ)^(50*k i) := by
  have row_mem {i : I} {t : ℕ} (ht : t < (b i).length/4) {a : α} (ha : a ∈ radixTable (v i) t) :
      ∃ j q, v i j q = a := by
    obtain ⟨j,r⟩ := radixTable_row (v i) ht
    exact ⟨j, List.mem_ofFn.mp (r ▸ ha)⟩
  obtain ⟨out, generated, unit, order, program, accurate⟩ :=
    tensorPass k (fun i => (b i).length/4) (fun i => radixTable (v i)) store x ideal hk
      (fun i => by have H := (hb i).axisCount; have := Nat.div_le_self (k i) (l i); omega)
      (fun i j hj => by
        obtain ⟨a,eqn⟩ := radixTable_row (v i) hj
        rw [eqn, List.length_ofFn]
        exact (blockRadix_bounds (hb i) a).1)
      (fun i => (radixTable_count _).trans (prod_blockRadix (hb i) (hd i)))
      (fun i _ ht _ ha => by obtain ⟨j,q,rfl⟩ := row_mem ht ha; exact hunit i j q)
      (fun i _ ht _ ha => by obtain ⟨j,q,rfl⟩ := row_mem ht ha; exact herr i j q) hx
  have ident : generated = fun i => blockCoefficient (hb i) (hd i) (phase i) := by
    funext i
    apply List.ofFn_injective
    exact (order i).trans (synchronizedPhase_order (hb i) (hd i) _ _ _ (hmatch i)).symm
  subst generated
  exact ⟨out,unit,program,accurate⟩

end FixedPoint

end

end NearSquareRoot
end Computability
end OAI
