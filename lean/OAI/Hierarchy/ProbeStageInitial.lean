import OAI.Hierarchy.ProbeStageRowNative
import OAI.Hierarchy.ProbePermutationRoute
import OAI.Hierarchy.ProbeStageAddress

namespace OAI
/-! # Reading the input permutation and constructing the first matching -/

namespace Hierarchy.ProbeStage.Native
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing

/-- The input permutation occupies the first n private words. Two native
passes place the singleton group and identity source position beside it. -/
def rootPasses (h : ℕ) := columns (2^h) (2^h) [.lit 0,.row]
def initialOutput (h : ℕ) : Bank := ⟨0,h⟩
def initialGroup (h : ℕ) : Bank := ⟨2^h,h⟩
def initialInput (h : ℕ) : Bank := ⟨2*2^h,h⟩

theorem root_exec (h d copies : ℕ) (π : Equiv.Perm (Fin (2^h)))
    (m : Memory (wordBits h d copies)) (input : ∀ r : Fin (2^h), m r.val=((π r).val : Word _)) :
    let ps := rootPasses h
    let after := result ps m
    (program (wordBits h d copies) ps).Exec m after (clock ps) ∧
      clock ps ≤ 12+16*2^h ∧
      Resident (initialGroup h) after (fun _ : Fin (2^h) => 0) ∧
      Resident (initialInput h) after (fun r : Fin (2^h) => ((permutationTiles π).input r).val) ∧
      Resident (initialOutput h) after (fun r : Fin (2^h) => ((permutationTiles π).output r).val) := by
  let n := 2^h
  have extentLe : n≤extent h d :=
    Nat.pow_le_pow_right (by decide) (by unfold roomBits;omega)
  have z : 3*n≤heapEnd h d copies := by
    have start := phase_in_heap (h:=h) (d:=d) (copies:=copies) (Nat.zero_le (rounds d))
    simp only [phase,Nat.zero_mul,Nat.add_zero] at start
    exact (Nat.mul_le_mul_left 3 extentLe).trans start
  have room := z.trans_lt (heap_room h d copies)
  have small : n≤2^wordBits h d copies := by omega
  have reads : ∀ e∈([.lit 0,.row] : List Expr),e.Fits (wordBits h d copies) n := by
    simp [Expr.Fits]
  have main : (program (wordBits h d copies) (rootPasses h)).Exec m (result (rootPasses h) m)
      (clock (rootPasses h)) := columns_exec ([.lit 0,.row] : List Expr) m
    (columns_safe (n:=n) (base:=n) _ le_rfl reads (by simp only [List.length_cons,List.length_nil];omega))
  refine ⟨main,?_,?_,?_,?_⟩
  · have charges := columns_clock n n 2 ([.lit 0,.row] : List Expr) (by simp [Expr.work])
    exact charges.trans_eq (by simp only [List.length_cons,List.length_nil];dsimp only [n];ring)
  · apply Resident.of_cells _ _ _ le_rfl small
    intro r
    simpa [initialGroup,rootPasses,Expr.eval] using
      (columns_read (n:=n) (base:=n) _ m le_rfl reads 0 (by decide) r)
  · apply Resident.of_cells _ _ _ le_rfl small
    intro r
    simpa [initialInput,rootPasses,Expr.eval,two_mul,permutationTiles,n,id] using
      (columns_read (n:=n) (base:=n) _ m le_rfl reads 1 (by decide) r)
  · apply Resident.of_cells _ _ _ le_rfl small
    intro r
    have prior := result_below (rootPasses h) m r.val (fun pass hp =>
      r.isLt.trans_le (columns_below ([.lit 0,.row] : List Expr) pass hp))
    simpa [initialOutput,permutationTiles] using prior.trans (input r)

end Hierarchy.ProbeStage.Native

end OAI
