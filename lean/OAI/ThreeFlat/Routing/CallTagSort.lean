import OAI.ThreeFlat.Routing.BitonicSortNetwork
import OAI.LinearAlgebra.SpectralBooks.MultisetCircuit

namespace OAI
/-! # An ordinary tagged switch for short control words

On each side a bitonic sorter reads pairs of destination address and payload.
Both propose the same hidden sorted array. Its uniqueness gives the ordinary
tagged-switch tensor even in positive characteristic.
-/

namespace ThreeFlat.Routing.CallTagSort

open scoped Classical BigOperators
open SortNetwork (Records Payload pack)
open LinearAlgebra.SpectralBooks.Batcher
noncomputable section

private theorem sorted_iff {n w : ℕ} (X Y : Records n w) :
    BitonicSort.sorted X = BitonicSort.sorted Y ↔
    ∃ e : Equiv.Perm (Fin (2^n)), ∀ i, X i = Y (e i) := by
  let x i := addressEquiv w (X i)
  let y i := addressEquiv w (Y i)
  have eq : BitonicSort.sorted X = BitonicSort.sorted Y ↔ (sortNet n).eval x = (sortNet n).eval y := by
    constructor
    · intro h
      funext i
      simpa only [BitonicSort.sorted,BitonicSchedule.sorted,Equiv.apply_symm_apply,x,y] using
        congrArg (addressEquiv w) (congrFun h i)
    · intro h
      funext i
      exact congrArg (addressEquiv w).symm (congrFun h i)
  rw [eq]
  constructor
  · intro h
    obtain ⟨l, hl⟩ := (sortNet n).exists_eval_eq_comp_perm x
    obtain ⟨r, hr⟩ := (sortNet n).exists_eval_eq_comp_perm y
    rw [hl, hr] at h
    refine ⟨l.symm.trans r, fun i => (addressEquiv w).injective ?_⟩
    simpa only [Function.comp_apply,Equiv.apply_symm_apply,Equiv.trans_apply,x,y] using congrFun h (l.symm i)
  · rintro ⟨e,he⟩
    apply (sortNet_eq_iff_perm _ _).mpr
    have h : x = y ∘ e := funext fun i => congrArg (addressEquiv w) (he i)
    rw [h]
    exact e.ofFn_comp_perm y

private def row {n u : ℕ} (a : Fin (2^n)) (word : Fin u → Bool) : Fin (n+u) → Bool :=
  Fin.append ((addressEquiv n).symm a) word

private theorem row_inj {n u : ℕ} {a b : Fin (2^n)} {x y : Fin u → Bool} :
    row a x = row b y ↔ a = b ∧ x = y := by
  constructor
  · intro h
    refine ⟨(addressEquiv n).symm.injective (funext fun i => ?_), funext fun j => ?_⟩
    · simpa [row] using congrFun h (Fin.castAdd u i)
    · simpa [row] using congrFun h (Fin.natAdd n j)
  · rintro ⟨rfl,rfl⟩
    rfl

private theorem same_iff_routed {n u : ℕ} (tag : Fin (2^n) → Fin (2^n)) (src dst : Records n u) :
    BitonicSort.sorted (fun i => row (tag i) (src i)) = BitonicSort.sorted (fun i => row i (dst i)) ↔
      Routed tag src dst := by
  rw [sorted_iff]
  constructor
  · rintro ⟨e,he⟩
    have eq : tag = ⇑e := funext fun i => (row_inj.mp (he i)).1
    rw [eq]
    exact ⟨e.bijective, fun i => (row_inj.mp (he i)).2.symm⟩
  · rintro ⟨bij,good⟩
    exact ⟨Equiv.ofBijective tag bij, fun i => row_inj.mpr ⟨rfl,(good i).symm⟩⟩

private abbrev M (n u : ℕ) := Fintype.card (Payload n (n+u))
private abbrev Src (n u : ℕ) := BitSource (M n u) (Fintype.card (SwitchPin n u))

private def rowWire (n u : ℕ) (out : Bool) (a : Fin (2^n)) : Fin (n+u) → Src n u :=
  Fin.append (fun j => if out then .constant ((addressEquiv n).symm a j)
    else .pin (Fintype.equivFin _ (SwitchPin.tag a j)))
    (fun j => .pin (Fintype.equivFin _ (.inr (out,a,j) : SwitchPin n u)))

private def wire (n u : ℕ) (out : Bool) : Fin (M n u + M n u) → Src n u :=
  Fin.append (fun i => let a := (Fintype.equivFin (Payload n (n+u))).symm i
                       rowWire n u out a.1 a.2) BitSource.hidden

/-- Both sorters read their own external data and compare against common internal bits. -/
def network (F : Type*) [Zero F] [One F] (n u : ℕ) :
    BitNetwork F (Fintype.card (SwitchPin n u)) :=
  BitNetwork.glue (fun _ : Bool => BitonicSort.network F n (n+u)) (wire n u)

private def unpack {n w : ℕ} (bits : Fin (Fintype.card (Payload n w)) → Bool) : Records n w :=
  fun i j => bits (Fintype.equivFin _ (i,j))

private theorem packed_unpacked {n w : ℕ} (bits : Fin (Fintype.card (Payload n w)) → Bool) :
    pack (unpack bits) = bits := by
  funext i
  simp [pack,unpack,Function.uncurry]

private theorem unpack_packed {n w : ℕ} (X : Records n w) : unpack (pack X) = X := by
  funext i j
  simp [pack,unpack]

private def inputRows {n u : ℕ} (pin : SwitchPin n u → Bool) (out : Bool) : Records n (n+u) :=
  fun i => row (if out then i else addressEquiv n (fun j => pin (SwitchPin.tag i j)))
    (fun j => pin (.inr (out,i,j)))

private theorem wire_read {n u : ℕ} (pin : SwitchPin n u → Bool) (out : Bool) (h : Fin (M n u) → Bool) :
    (fun j => (wire n u out j).read h (pin ∘ (Fintype.equivFin _).symm)) =
      Fin.append (pack (inputRows pin out)) (pack (unpack h)) := by
  rw [packed_unpacked]
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · obtain ⟨⟨a,k⟩, rfl⟩ := (Fintype.equivFin (Payload n (n+u))).surjective i
    simp only [wire, Fin.append_left, Equiv.symm_apply_apply, pack, Function.uncurry]
    refine Fin.addCases (fun v => ?_) (fun v => ?_) k
    · cases out <;> simp [rowWire, inputRows, row, BitSource.read]
    · cases out <;> simp [rowWire, inputRows, row, BitSource.read]
  · simp only [wire, Fin.append_right,BitSource.read]

theorem correct (F : Type*) [CommSemiring F] (n u : ℕ) : RealizesTaggedSwitch (network F n u) := by
  intro pin
  rw [network,BitNetwork.glue_eval]
  simp_rw [wire_read,BitonicSort.network_eval]
  let X := BitonicSort.sorted (inputRows pin false)
  let Y := BitonicSort.sorted (inputRows pin true)
  have p : ∀ h : Fin (M n u) → Bool, unpack h = X ↔ h = pack X := by
    intro h
    constructor
    · intro eq
      exact (packed_unpacked h).symm.trans (congrArg pack eq)
    · rintro rfl
      exact unpack_packed _
  have test : X = Y ↔ Routed (fun i => addressEquiv n (fun j => pin (SwitchPin.tag i j)))
      (fun i j => pin (SwitchPin.input i j)) (fun i j => pin (SwitchPin.output i j)) := by
    exact (same_iff_routed (fun i => addressEquiv n (fun j => pin (SwitchPin.tag i j)))
        (fun i j => pin (SwitchPin.input i j)) (fun i j => pin (SwitchPin.output i j)))
  rw [Finset.sum_eq_single_of_mem (pack X) (Finset.mem_univ _)]
  · rw [Fintype.prod_bool]
    change (if unpack (pack X) = Y then _ else _) * (if unpack (pack X) = X then _ else _) = _
    simp only [unpack_packed,ite_true,mul_one,taggedSwitch,test]
  · intro h _ hn
    exact Finset.prod_eq_zero (Finset.mem_univ false) (ite_eq_right fun he => hn ((p h).mp he))

theorem cells (F : Type*) [Zero F] [One F] (n u : ℕ) :
    (network F n u).cells ≤ 8192*(n+u+1)*(2^n)*(n+1)^2 := by
  simp only [network,BitNetwork.glue_cells,Finset.sum_const,Finset.card_univ,Fintype.card_bool,nsmul_eq_mul]
  have hc := BitonicSort.network_cells F n (n+u)
  nlinarith only [hc]

theorem internal (F : Type*) [Zero F] [One F] (n u : ℕ) :
    (network F n u).internal ≤ 8193*(n+u+1)*(2^n)*(n+1)^2 := by
  simp only [network,BitNetwork.glue_internal,Finset.sum_const,Finset.card_univ,Fintype.card_bool,nsmul_eq_mul]
  have hc := BitonicSort.network_internal F n (n+u)
  have h : 2^n*(n+u) ≤ (n+u+1)*(2^n)*(n+1)^2 := by
    calc
      _ ≤ (n+u+1)*(2^n) := (Nat.mul_comm _ _).le.trans (Nat.mul_le_mul_right (2^n) (Nat.le_succ _))
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by positivity)
  simp only [M,Payload,Fintype.card_prod,Fintype.card_fin]
  nlinarith only [hc,h]

end
end ThreeFlat.Routing.CallTagSort

end OAI
