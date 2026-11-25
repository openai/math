import OAI.LinearAlgebra.SpectralBooks.GridPin.GridPinGeometry
import OAI.LinearAlgebra.SpectralBooks.PortGraph.RootedMap

/-! # Sphericity of the rectangular grid

The numbered rotation gives a distinct face for each elementary square and one
further face touching a unary endpoint. These already reach the upper bound on
Euler characteristic for a connected rotation system.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace GridPin

open PortGraph Equiv Equiv.Perm HyperbolicObstruction.PictureSwitch

variable {m n : ℕ}

def rooted (m n : ℕ) : RootedMap (Vertex (m+1) (n+1)) (Edge (m+1) (n+1)) :=
  ⟨graph _ _, cell 0 0, numbering _ _, degree_bound, connected _ _⟩

private theorem turn_cell (i : Fin m) (j : Fin n) (r : Fin 4) :
    (numbering m n).turn (dart (cell i j) r) = dart (cell i j) (finRotate 4 r) := by
  let v := cell i j
  let p := ports v r
  have h := (numbering m n).turn_port p
  change (numbering m n).turn p.val = _
  rw [h]
  change (((ports v) _) : (graph m n).Port v).val = _
  dsimp [Numbering.successor, numbering, p]
  simp only [Equiv.symm_apply_apply]
  apply congrArg (fun k : Fin 4 => dart (cell i j) k)
  apply Fin.ext
  exact rotate_cast (port_card v).symm r
where
  rotate_cast {a b : ℕ} (e : a = b) (i : Fin a) :
      (finRotate b (Fin.cast e i)).val = (finRotate a i).val := by subst b; rfl

private abbrev face (m n : ℕ) := (rooted m n).num.rotation.picture.face

/-- The four outgoing darts of the unit square, starting at its top left and
going down the left side. -/
private def boundary (i : Fin m) (j : Fin n) : Fin 4 → Edge (m+1) (n+1) × Bool :=
  ![dart (cell i.castSucc j.castSucc) 3, dart (cell i.succ j.castSucc) 2,
    dart (cell i.succ j.succ) 1, dart (cell i.castSucc j.succ) 0]

private theorem face_boundary (i : Fin m) (j : Fin n) (r : Fin 4) :
    face m n (boundary i j r) = boundary i j (finRotate 4 r) := by
  fin_cases r
  · exact turn_cell i.succ j.castSucc 1
  · exact turn_cell i.succ j.succ 0
  · exact turn_cell i.castSucc j.succ 3
  · exact turn_cell i.castSucc j.castSucc 2

private theorem square_closed (i : Fin m) (j : Fin n) (x : Edge (m+1) (n+1) × Bool)
    (h : (face m n).SameCycle (boundary i j 0) x) : ∃ r, boundary i j r = x := by
  obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction k with
  | zero => exact ⟨0,rfl⟩
  | succ k ih =>
    obtain ⟨r,hr⟩ := ih
    exact ⟨finRotate 4 r, by rw [← face_boundary, hr, pow_succ', mul_apply]⟩

private def outside (m n : ℕ) : Edge (m+1) (n+1) × Bool := (hor 0 0, false)

private theorem outside_ne (i : Fin m) (j : Fin n) (r : Fin 4) :
    boundary i j r ≠ outside m n := by
  fin_cases r <;> simp [boundary, dart, outside, hor, ver]

private theorem square_injective (i : Fin m) (j : Fin n) (i' : Fin m) (j' : Fin n) (r : Fin 4)
    (h : boundary i j r = boundary i' j' 0) : (i,j) = (i',j') := by
  fin_cases r <;> simp [boundary, dart, hor, ver] at h
  exact Prod.ext h.2 h.1

private def rep (m n : ℕ) : Option (Fin m × Fin n) → Edge (m+1) (n+1) × Bool
  | none => outside m n
  | some (i,j) => boundary i j 0

private theorem faces_lower (m n : ℕ) : (m*n+1 : ℕ) ≤ Nat.card (Quotient (SameCycle.setoid (face m n))) := by
  let f (a : Option (Fin m × Fin n)) := Quotient.mk (SameCycle.setoid (face m n)) (rep m n a)
  have hinj : Function.Injective f := by
    intro a b h
    have hcycle := Quotient.exact h
    rcases a with _ | ⟨i,j⟩ <;> rcases b with _ | ⟨i',j'⟩
    · rfl
    · obtain ⟨r,hr⟩ := square_closed i' j' _ (Equiv.Perm.SameCycle.symm hcycle)
      exact (outside_ne _ _ _ hr).elim
    · obtain ⟨r,hr⟩ := square_closed i j _ hcycle
      exact (outside_ne _ _ _ hr).elim
    · obtain ⟨r,hr⟩ := square_closed i j _ hcycle
      exact congrArg some (square_injective _ _ _ _ _ hr)
  simpa using Nat.card_le_card_of_injective f hinj

theorem spherical (m n : ℕ) : (rooted m n).Spherical := by
  let ρ := (rooted m n).num.rotation
  have conn := PlanarPatch.underlying_connected_of_connectedFrom _ _ (connected m n)
  have comp : Nat.card (Quotient ρ.picture.components) = 1 :=
    ρ.picture_component_card conn
  have vert := ρ.picture_vertex_count (Rotation.nonempty_ports_of_connected conn)
  have low := faces_lower m n
  change ρ.picture.GenusZero
  apply le_antisymm ρ.picture.euler_le
  rw [comp, PictureMap.euler, vert, vertex_count, cycles_eq_card_classes,
    Fintype.card_prod, Fintype.card_bool, edge_count]
  push_cast
  have hh : ((m:ℤ)*n+1) ≤ Nat.card (Quotient (SameCycle.setoid (face m n))) := by exact_mod_cast low
  change (m:ℤ)*n+1 ≤ Nat.card (Quotient (SameCycle.setoid ρ.picture.face)) at hh
  change (m:ℤ)*n+1 ≤ Nat.card (VertexClasses ρ.picture.face) at hh
  ring_nf at hh ⊢
  omega

end GridPin

end

end SpectralBooks
end LinearAlgebra
end OAI
