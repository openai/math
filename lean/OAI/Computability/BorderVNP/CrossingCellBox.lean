import OAI.Computability.BorderVNP.CrossingCellWord
import OAI.Computability.BorderVNP.CrossingProfileValue
import OAI.Computability.BorderVNP.CellSparseSemantics

/-!
# Reading one-copy gadget entries from a repeated private box

At a bank site of the physical profile, the tables read one row per
occurrence. A fixed directory lists the rows once, in little-endian
order. Repetitions of a box need only its starting address, stride and
copy count. The selected position is reported even when its scalar is zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.CellBox

open CellSparse
open scoped Classical BigOperators
variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}

/-- All individual input lanes of one local table at a given site. -/
abbrev Lane (N : Network D P bits) (v : N.Site) :=
  (Σ e : {e : N.Edge // N.src e = v ∨ N.dst e = v}, Fin (N.width e.val)) ⊕
  (Σ u : {u : P // N.attach u = v}, Fin (bits u.val))

/-- Recover the two port arguments of a site from its individual lanes. -/
def localRow {Y : Type*} (N : Network D P bits) (id : N.Tables Y) (v : N.Site)
    (bit : Lane N v → Bool) : Y :=
  id v (fun e k => bit (.inl ⟨e,k⟩)) (fun u k => bit (.inr ⟨u,k⟩))

/-- The fixed little-endian row directory for one site. -/
noncomputable def rows {d : ℕ} (N : Network D P bits) (id : N.Tables ℕ) (v : N.Site)
    (order : Lane N v ≃ Fin d) : List ℕ :=
  List.ofFn fun k : Fin (2^d) =>
    localRow N id v fun l => finTwoEquiv (finFunctionFinEquiv.symm k (order l))

/-- A single sparse gadget factor. The row table and relative bit addresses are
independent of the number of times this one-copy box is invoked. -/
noncomputable def factor {d : ℕ} (N : Network D P bits) (id : N.Tables ℕ) (v : N.Site)
    (order : Lane N v ≃ Fin d) (addr : Fin d → ℕ) : Factor :=
  .gadget (List.ofFn addr) (rows N id v order)

omit [Fintype P] in
/-- The sparse reader records exactly the position selected by the actual
local table when the advertised addresses hold its lane values. -/
theorem observe_factor {d : ℕ} (N : Network D P bits) (id : N.Tables ℕ) (v : N.Site)
    (order : Lane N v ≃ Fin d) (addr : Fin d → ℕ) (bank : ℕ → Bool) (offset copy : ℕ) :
    (factor N id v order addr).observe bank offset copy =
      some (false, some (localRow N id v fun l => bank (offset + addr (order l)))) := by
  let f (i : Fin d) := finTwoEquiv.symm (bank (offset + addr i))
  let r : Fin (2 ^ d) := finFunctionFinEquiv f
  have hword : word bank ((List.ofFn addr).map (offset + ·)) = r.val := by
    rw [List.map_ofFn]
    exact word_ofFn _ _
  have he : (rows N id v order)[r.val]? =
      some (localRow N id v fun l => bank (offset + addr (order l))) := by
    rw [List.getElem?_eq_getElem (by simp [rows])]
    simp only [rows, List.getElem_ofFn, Fin.eta, r, Equiv.symm_apply_apply, f, Equiv.apply_symm_apply]
  simp only [factor, Factor.observe, hword, he, Option.map_some]

/-- The lanes used by a bank site are read at its own copy ordinal from the
actual bank cable and the forced terminal feeders. -/
def bankLanes {A j : ℕ} (N : Fin A → Network D P bits)
    (place : P → EuclideanSpace ℝ (Fin D)) (hball : ∀ u, ‖place u‖ ≤ 1) (p : Fin A → ℕ)
    (y : (Profile.network N place hball j p).Assignment) (a : Fin A) (v : (N a).Site)
    (i : Fin (p a)) : Lane (N a) v → Bool
  | .inl ⟨e,k⟩ => Profile.blocks (y (.inr (.inr ⟨a,e.val⟩))) i k
  | .inr ⟨u,k⟩ => Profile.blocks (y (.inr (.inl (a,u.val)))) i k

/-- Repacking a site's lane values uses one consecutive word per occurrence. -/
def packedBank {d copies : ℕ} (b : Fin copies → Fin d → Bool) (k : ℕ) : Bool :=
  if h : k < copies * d then
    let ix := finProdFinEquiv.symm (⟨k,h⟩ : Fin (copies*d))
    b ix.1 ix.2
  else false

/-- The canonical repeated box layout has the advertised stride. -/
theorem packedBank_read {d copies : ℕ} (b : Fin copies → Fin d → Bool)
    (i : Fin copies) (l : Fin d) : packedBank b (i.val*d+l.val) = b i l := by
  have h : i.val*d+l.val = (finProdFinEquiv (i,l)).val := by
    simp [Nat.add_comm, Nat.mul_comm]
  rw [h]
  simp only [packedBank, (finProdFinEquiv (i,l)).isLt, dite_true, Fin.eta, Equiv.symm_apply_apply]

/-- Reading each actual bank row by the same one-copy sparse box reports its
gadget ID. The table is fixed before the copy multiplicity or wire values. -/
theorem observe_bank {A j d : ℕ} (N : Fin A → Network D P bits)
    (place : P → EuclideanSpace ℝ (Fin D)) (hball : ∀ u, ‖place u‖ ≤ 1)
    (p : Fin A → ℕ) (y : (Profile.network N place hball j p).Assignment)
    (a : Fin A) (v : (N a).Site) (order : Lane (N a) v ≃ Fin d)
    (id : (N a).Tables ℕ) (i : Fin (p a)) :
    let lanes := bankLanes N place hball p y a v
    let bank := packedBank (fun l k => lanes l (order.symm k))
    (factor (N a) id v order Fin.val).observe bank (i.val*d) i.val =
      some (false, some (localRow (N a) id v (lanes i))) := by
  dsimp only
  rw [observe_factor]
  simp only [packedBank_read, Equiv.symm_apply_apply]

end Crossing.CellBox

end BorderVNP
end Computability
end OAI
