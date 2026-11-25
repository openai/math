import OAI.ThreeFlat.Diagonal.GuardedTransfer
import OAI.ThreeFlat.Diagonal.SharedHistoryRegister
import OAI.ThreeFlat.Diagonal.MotifBinaryPacking

namespace OAI
/-! # Summing one shared physical choice gives the initial contraction plus identity -/

namespace ThreeFlat.Diagonal.GuardedTransfer

open HistoryContraction
open scoped BigOperators Classical
noncomputable section
variable {F U X I : Type*} [CommSemiring F] [Fintype U] [Fintype X] [DecidableEq X]
variable [Fintype I] [DecidableEq I] {S : Shape} (P : Plan F S) (bits : P.History → ℕ)

/-- Pack the final edge assignment as a single consecutively addressed tuple of bits. -/
def boundaryBits {B : Type} [Fintype B] {label : B → Type} {n : ℕ} (order : Fin n ≃ B)
    (width : Fin n → ℕ) (word : ∀ i, label (order i) ≃ Fin (2^width i)) :
    (Fin (∑ i,width i) → Bool) ≃ (∀ b, label b) :=
  (MotifBinaryPacking.flatten width).symm.trans ((Equiv.piCongrRight fun i =>
    (MotifBinaryPacking.word (width i)).trans (word i).symm).trans (Equiv.piCongrLeft _ order))

variable (decode : ∀ h, (Fin (bits h) → Bool) ≃ (P.finish h).Boundary)

/-- Product of all sites, grouped according to their actual owner, equals the initial trace
contraction when summed over the shared terminal records. -/
theorem grouped_cells (u : S.Factors F) (group : ∀ h, (P.finish h).Site → I) :
    (∑ v : Plan.Terminal P bits, ∏ i : I, ∏ j : {j // group v.1 j = i},
      P.cells v.1 u j ((P.finish v.1).graph.atVertex (decode v.1 v.2) j)) = S.contract u := by
  rw [P.contract_eq_cells u, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro h _
  rw [← (decode h).sum_comp]
  apply Finset.sum_congr rfl
  intro v _
  let value (j : (P.finish h).Site) := P.cells h u j ((P.finish h).graph.atVertex (decode h v) j)
  let fiber := Equiv.sigmaFiberEquiv (group h)
  exact (Fintype.prod_sigma (fun t => value (fiber t))).symm.trans (fiber.prod_comp value)

/-- Physical opening, group transitions and closing have the identity-plus-trace entry.
Each group transfer is expressed on the actual fiber of the endpoint partition belonging to
this shared history. -/
theorem switched_contraction (outer : X ↪ U) (live : X × Option (Plan.Terminal P bits) → U)
    (first last : Matrix U U F) (is : List I) (middle : I → Matrix U U F) (nd : is.Nodup) (all : ∀ j,j∈is)
    (Y : Plan.Terminal P bits → I → Type*) [∀ v i, Fintype (Y v i)] [∀ v i, DecidableEq (Y v i)]
    (index : ∀ v, X ≃ (∀ i,Y v i)) (K : ∀ v i, Matrix (Y v i) (Y v i) F)
    (op : Tracks outer live first (openHistory (H := Option (Plan.Terminal P bits))))
    (groups : ∀ i∈is, Tracks live live (middle i) (Matrix.blockDiagonal (fun v : Option (Plan.Terminal P bits) =>
      v.elim (1 : Matrix X X F) (fun h => (chunkKernel (K h) {i}).submatrix (index h) (index h)))))
    (cl : Tracks live outer last (openHistory (H := Option (Plan.Terminal P bits))).transpose)
    (u : X → X → S.Factors F) (group : ∀ h, (P.finish h).Site → I)
    (cellValues : ∀ v i x y, K v i (index v x i) (index v y i) = ∏ j : {j // group v.1 j=i},
      P.cells v.1 (u x y) j ((P.finish v.1).graph.atVertex (decode v.1 v.2) j)) (x y : X) :
    (first*(is.map middle).prod*last) (outer x) (outer y) = (1 : Matrix X X F) x y + S.contract (u x y) := by
  have sim := (op.comp (tracks_list live is middle _ groups)).comp cl
  change ((first*(is.map middle).prod*last).submatrix outer outer) x y = _
  rw [sim.restrict]
  calc
    _ = (1 : Matrix X X F) x y + ∑ v, ∏ i, K v i (index v x i) (index v y i) := by
      convert! switched_reindexed_scan index K is nd all x y using 1;
        congr! 12
    _ = _ := by
      apply congrArg ((1 : Matrix X X F) x y + ·)
      simp_rw [cellValues]
      exact grouped_cells P bits decode (u x y) group


end
end ThreeFlat.Diagonal.GuardedTransfer

end OAI
