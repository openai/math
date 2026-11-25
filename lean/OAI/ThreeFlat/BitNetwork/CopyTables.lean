import OAI.ThreeFlat.BitNetwork.CopyGraph
import OAI.ThreeFlat.CopyChain
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Local tensors on the trivalent copy graph -/

namespace ThreeFlat.BitNetwork

open Computability.BorderVNP.Crossing
open scoped BigOperators Classical
noncomputable section

variable {F : Type*} {p : ℕ} (N : BitNetwork F p)

/-- The socket at offset `j` in the address chain. -/
def socketAt (s : N.Source) (j : Fin (N.arity s)) : N.Socket :=
  ((N.socketOrder s).symm j).val

@[simp] theorem address_socketAt (s : N.Source) (j : Fin (N.arity s)) :
    N.address (N.socketAt s j) = s := ((N.socketOrder s).symm j).property

def socketOffset (u : N.Socket) : Fin (N.arity (N.address u)) :=
  N.socketOrder _ ⟨u, rfl⟩

@[simp] theorem socketAt_offset (u : N.Socket) :
    N.socketAt (N.address u) (N.socketOffset u) = u := by
  simp [socketAt, socketOffset]

private def socketEquiv : N.Socket ≃ (Σ s, Fin (N.arity s)) :=
  (Equiv.sigmaFiberEquiv N.address).symm.trans (Equiv.sigmaCongrRight N.socketOrder)

private theorem socketKey_at (s : N.Source) (j : Fin (N.arity s)) :
    (⟨N.address (N.socketAt s j), N.socketOffset (N.socketAt s j)⟩ : Σ t, Fin (N.arity t)) =
      ⟨s,j⟩ :=
  N.socketEquiv.apply_symm_apply ⟨s,j⟩

theorem copySrc_socketAt (s : N.Source) (j : Fin (N.arity s)) :
    N.copySrc (.inr (N.socketAt s j)) = .inr ⟨s, j.succ.castSucc⟩ := by
  exact congrArg (fun e : Σ t, Fin (N.arity t) =>
    (Sum.inr ⟨e.1,e.2.succ.castSucc⟩ : N.CopySite)) (N.socketKey_at s j)

abbrev LocalEdges (v : N.CopySite) :=
  {e : N.CopyEdge // N.copySrc e = v ∨ N.copyDst e = v} → Fin 1 → Bool

abbrev LocalPins (v : N.CopySite) :=
  {j : Fin p // (Sum.inr ⟨BitSource.pin j, 0⟩ : N.CopySite) = v} → Fin 1 → Bool

abbrev TableAt (v : N.CopySite) := N.LocalEdges v → N.LocalPins v → F

private def copyRoot [Zero F] [One F] (s : N.Source) :
    N.TableAt (.inr ⟨s, 0⟩) := by
  intro wire pins
  let root := wire ⟨.inl ⟨s, 0⟩, Or.inl rfl⟩ 0
  cases s with
  | hidden i => exact 1
  | pin i => exact CopyChain.ind F (root = pins ⟨i, rfl⟩ 0)
  | constant b => exact CopyChain.ind F (root = b)

private def copyMiddle [Zero F] [One F] (s : N.Source) (j : Fin (N.arity s)) :
    N.TableAt (.inr ⟨s, j.castSucc.succ⟩) := fun wire _ =>
  CopyChain.copy F
    (wire ⟨.inl ⟨s, j.castSucc⟩, Or.inr rfl⟩ 0)
    (wire ⟨.inl ⟨s, j.succ⟩, Or.inl rfl⟩ 0)
    (wire ⟨.inr (N.socketAt s j), Or.inl (N.copySrc_socketAt s j)⟩ 0)

def copyTable [Zero F] [One F] : N.copyGraph.Tables F
  | .inl i => fun wire _ => N.table i fun j => wire ⟨.inr (i,j), Or.inr rfl⟩ (0 : Fin 1)
  | .inr ⟨s, k⟩ => Fin.cases (motive := fun k => N.TableAt (.inr ⟨s, k⟩)) (N.copyRoot s)
      (Fin.lastCases (motive := fun j => N.TableAt (.inr ⟨s, j.succ⟩)) (fun _ _ => 1)
        (N.copyMiddle s)) k

/-- An explicit assignment to every trunk and spoke of the original tensor graph. -/
def copyAssignment (y : CopyChain.Trunks N.arity) (z : CopyChain.Spokes N.arity) :
    N.copyGraph.Assignment
  | .inl ⟨s, j⟩ => fun _ => y s j
  | .inr u => fun _ => z (N.address u) (N.socketOffset u)

def spokeWeight [CommMonoid F] (z : CopyChain.Spokes N.arity) : F :=
  ∏ i : Fin N.cells, N.table i fun j => z (N.address (i,j)) (N.socketOffset (i,j))

@[simp] theorem spokeWeight_canonical [CommMonoid F] (h : Fin N.internal → Bool)
    (pins : Fin p → Bool) :
    N.spokeWeight (CopyChain.spokes N.arity (BitSource.read h pins)) = N.weight pins h := rfl

private theorem assigned_socket (y : CopyChain.Trunks N.arity) (z : CopyChain.Spokes N.arity)
    (s : N.Source) (j : Fin (N.arity s)) :
    N.copyAssignment y z (.inr (N.socketAt s j)) (0 : Fin 1) = z s j := by
  exact congrArg (fun e : Σ t, Fin (N.arity t) => z e.1 e.2) (N.socketKey_at s j)

/-- Edge assignments are exactly the independent arrays of trunk and spoke bits. -/
def copyAssignmentEquiv :
    CopyChain.Trunks N.arity × CopyChain.Spokes N.arity ≃ N.copyGraph.Assignment where
  toFun b := N.copyAssignment b.1 b.2
  invFun a := (fun s i => a (.inl ⟨s,i⟩) (0 : Fin 1), fun s i => a (.inr (N.socketAt s i)) (0 : Fin 1))
  left_inv := by
    rintro ⟨y,z⟩
    apply Prod.ext
    · rfl
    · funext s i
      exact N.assigned_socket y z s i
  right_inv := by
    intro a
    funext e j
    change Fin 1 at j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    cases hj
    obtain ⟨s,i⟩ | u := e
    · rfl
    · exact congrArg (fun w : N.Socket => a (.inr w) (0 : Fin 1)) (N.socketAt_offset u)

private theorem read_root [CommSemiring F] (pins : Fin p → Bool)
    (y : CopyChain.Trunks N.arity) (z : CopyChain.Spokes N.arity) (s : N.Source) :
    N.copyGraph.read N.copyTable (N.copyAssignment y z) (fun q _ => pins q) (.inr ⟨s,0⟩) =
      CopyChain.ind F (CopyChain.Boundary pins s (y s 0)) := by
  cases s with
  | hidden i => simp [Network.read, copyTable, copyRoot, CopyChain.Boundary, CopyChain.ind]
  | pin i => rfl
  | constant b => rfl

private theorem read_middle [CommSemiring F] (pins : Fin p → Bool)
    (y : CopyChain.Trunks N.arity) (z : CopyChain.Spokes N.arity)
    (s : N.Source) (j : Fin (N.arity s)) :
    N.copyGraph.read N.copyTable (N.copyAssignment y z) (fun q _ => pins q)
      (.inr ⟨s,j.castSucc.succ⟩) =
      CopyChain.copy F (y s j.castSucc) (y s j.succ) (z s j) := by
  simp only [Network.read, copyTable, Fin.cases_succ, Fin.lastCases_castSucc, copyMiddle]
  rw [N.assigned_socket]
  rfl

private theorem read_terminal [CommSemiring F] (pins : Fin p → Bool)
    (y : CopyChain.Trunks N.arity) (z : CopyChain.Spokes N.arity) (s : N.Source) :
    N.copyGraph.read N.copyTable (N.copyAssignment y z) (fun q _ => pins q)
      (.inr ⟨s,(Fin.last (N.arity s)).succ⟩) = 1 := by
  simp only [Network.read, copyTable, Fin.cases_succ, Fin.lastCases_last]

private theorem source_product [CommSemiring F] (pins : Fin p → Bool)
    (y : CopyChain.Trunks N.arity) (z : CopyChain.Spokes N.arity) (s : N.Source) :
    (∏ i, N.copyGraph.read N.copyTable (N.copyAssignment y z) (fun q _ => pins q)
      (.inr ⟨s,i⟩)) =
      CopyChain.ind F (CopyChain.Boundary pins s (y s 0)) * CopyChain.links (y s) (z s) := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc, read_root, read_terminal, mul_one]
  simp only [read_middle, CopyChain.links]

/-- The true trivalent tensor graph and the addressed table array have the same contraction. -/
theorem copyGraph_value [CommSemiring F] (pins : Fin p → Bool) :
    N.copyGraph.value N.copyTable (fun q _ => pins q) = N.eval pins := by
  classical
  unfold Network.value
  rw [← N.copyAssignmentEquiv.sum_comp, Fintype.sum_prod_type]
  change (∑ y, ∑ z, ∏ v : N.CopySite, N.copyGraph.read N.copyTable
    (N.copyAssignment y z) (fun q _ => pins q) v) = _
  calc
    _ = ∑ y : CopyChain.Trunks N.arity, ∑ z : CopyChain.Spokes N.arity, N.spokeWeight z *
        ∏ s, CopyChain.ind F (CopyChain.Boundary pins s (y s 0)) *
          CopyChain.links (y s) (z s) := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro z _
      let f : N.CopySite → F := N.copyGraph.read N.copyTable (N.copyAssignment y z) (fun q _ => pins q)
      change (∏ v : Fin N.cells ⊕ (Σ s, Fin (N.arity s + 2)), f v) = _
      rw [Fintype.prod_sum_type, Fintype.prod_sigma]
      exact congrArg (fun t => N.spokeWeight z * t)
        (Finset.prod_congr rfl (fun s _ => N.source_product pins y z s))
    _ = _ := by
      simp_rw [mul_comm (N.spokeWeight _) _]
      simpa only [eval, spokeWeight_canonical] using
        CopyChain.sum_network N.arity pins (fun _ z => N.spokeWeight z)

end
end ThreeFlat.BitNetwork

end OAI
