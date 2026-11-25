import OAI.Computability.NearSquareRoot.SynchronizedBatchDecode
import OAI.Computability.NearSquareRoot.SynchronizedBatchRoutingProgram

/-! # Numeric rows for the decoded outward and return block permutations -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord

open IntegerMultiplication.Code SynchronizedBorrowing AxisWord
noncomputable section

variable {m : ℕ} (a c k : Fin m → ℕ) [∀ i, NeZero (a i)]
  (spectator : ∀ i, Spectators a c i ≃ Fin (Fintype.card (Spectators a c i)))
  (har : ∀ i, a i ≤ 2 ^ k i) (hborrow : ∀ i, 2 * 2 ^ k i ≤ 8 * a i)
  (he : Even (Fintype.card (Address a c)))

/-- Numerical tables supplied to the routing scan. -/
def routeTables (i : Fin m) (b : Fin 15) :=
  RoutingTable.bothTables (RoutingTable.prepareHeader
    (RoutingTable.dimensions (fiberCount a c i) (a i) (c i) (2 ^ k i) b))

theorem preparedHeader (i : Fin m) (b : Fin 15) :
    let E := RoutedWalsh.endpoints dilationAddress (batchEmbedding a c k spectator har hborrow i b)
      (blockRank a c spectator i) (pairLabels a c k i b)
    RoutingTable.prepareHeader (RoutingTable.dimensions (fiberCount a c i) (a i) (c i) (2 ^ k i) b) =
      RoutingTable.header (Fintype.card (Address a c)) (RoutingTable.activePairs E) := by
  rw [RoutingTable.prepareHeader_correct (hborrow i) (har i) b]
  unfold RoutingTable.header
  congr 1
  · rw [axisRank_card a c spectator i]
  · simp only [RoutingTable.activePairs, List.map_ofFn]
    apply congrArg List.ofFn
    funext q
    obtain ⟨⟨j,v⟩, rfl⟩ := finProdFinEquiv.surjective q
    apply Prod.ext <;> simp [RoutingTable.encodeAddress, RoutingTable.batchEndpoints_val,
      endpoints_apply]

/-- Packed position in the completed table, with the side as the low bit. -/
def interleave {n : ℕ} (hn : Even n) : Fin 2 × Fin (n/2) ≃ Fin n :=
  (Equiv.prodComm ..).trans (finProdFinEquiv.trans (finCongr (by obtain ⟨t, ht⟩ := hn; omega)))

/-- Both prepared lists, including every idle address and the serialization order. -/
theorem routeTables_eq (i : Fin m) (b : Fin 15) :
    let addr (x : Fin (Fintype.card (Address a c))) := (blockRank a c spectator i)
      ((completeMatching a c k spectator har hborrow he i b) ((interleave he).symm x))
    routeTables a c k i b = (List.ofFn (fun x => (tally x.val,tally (addr x).val)),
      List.ofFn (fun x => (tally (addr x).val,tally x.val))) := by
  let E := RoutedWalsh.endpoints dilationAddress (batchEmbedding a c k spectator har hborrow i b)
    (blockRank a c spectator i) (pairLabels a c k i b)
  let ps := RoutingTable.activePairs E
  have hp := RoutingTable.activePairs_nodup E
  have H (x : Fin (Fintype.card (Address a c))) :
      (blockRank a c spectator i) ((completeMatching a c k spectator har hborrow he i b) ((interleave he).symm x)) =
        RoutingTable.routing ps hp x := by
    unfold completeMatching RoutedWalsh.routeMatching
    rw [Equiv.trans_apply, Equiv.apply_symm_apply]
    change RoutingTable.routing ps hp (interleave he ((interleave he).symm x)) = _
    rw [Equiv.apply_symm_apply]
  dsimp only
  simp_rw [H]
  rw [routeTables, preparedHeader a c k spectator har hborrow i b]
  exact RoutingTable.bothTables_correct ps hp

/-- The prepared numbered table and its inverse record the actual decoded
matching. Row number is the completed pair label followed by the chosen bit. -/
theorem routeTables_rows (i : Fin m) (b : Fin 15) (u : Fin 2) (s : Fin (Fintype.card (Address a c)/2)) :
    let number := tally (2*s.val + u.val)
    let address := tally ((blockRank a c spectator i) ((completeMatching a c k spectator har hborrow he i b) (u,s))).val
    (number,address) ∈ (routeTables a c k i b).1 ∧ (address,number) ∈ (routeTables a c k i b).2 := by
  let n := Fintype.card (Address a c)
  let E := RoutedWalsh.endpoints dilationAddress (batchEmbedding a c k spectator har hborrow i b)
    (blockRank a c spectator i) (pairLabels a c k i b)
  let pairs := RoutingTable.activePairs E
  have hn := RoutingTable.activePairs_nodup E
  let q : Fin n := ⟨2*s.val+u.val, by obtain ⟨r,h⟩ := he; have := s.isLt; have := u.isLt; dsimp [n]; omega⟩
  have hm : (blockRank a c spectator i) ((completeMatching a c k spectator har hborrow he i b) (u,s)) =
      RoutingTable.routing pairs hn q := by
    unfold completeMatching RoutedWalsh.routeMatching
    rw [Equiv.trans_apply, Equiv.apply_symm_apply]
    apply congrArg (RoutingTable.routing pairs hn)
    apply Fin.ext
    change u.val + 2 * s.val = 2 * s.val + u.val
    omega
  unfold routeTables
  rw [preparedHeader a c k spectator har hborrow i b, RoutingTable.bothTables_correct _ hn, hm]
  exact ⟨List.mem_ofFn.mpr ⟨q,rfl⟩, List.mem_ofFn.mpr ⟨q,rfl⟩⟩

end
end ShortFourier.BatchWord

end NearSquareRoot
end Computability
end OAI
