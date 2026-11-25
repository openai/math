import OAI.Hierarchy.TaggedWideChronologicalOrder
import OAI.Hierarchy.TaggedWireRoleIndices

namespace OAI
/-! # Physical original RAM rows underlying each dated graph -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRows
open WireTelescope AdaptiveProbe ProtocolRAM.Calendar.CatalogueRows RoleProgram
open scoped Classical
variable {h W k attempts n : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
  (depth : ℕ) (mark : ReportSockets.Marks h W k attempts) (b : Board)
  (order : Fin b.coreRows ≃ Edges S h (2^W) k)
  (size : attempts*(ProtocolRAM.PurchaseFrozen.count h (2^W) k*ProtocolRAM.PurchaseFrozen.paths h S.degree depth)=b.boughtRows)
local notation "edges" => b.ordinal S π depth mark order size
local notation "Orig" => Old h W k b.rows
local notation "Ix" => Fin (Fintype.card Orig)

def embed : Source S π depth mark ↪ Orig :=
  (edges).sumMap (Function.Embedding.refl _)

variable (rows : Fin n ≃ Source S π depth mark)

def raw : Fin n ↪ Ix :=
  (rows.toEmbedding.trans (embed S π depth mark b order size)).trans SettledMatrix.Layout.numbered.symm.toEmbedding

theorem numbered_raw (i : Fin n) :
    SettledMatrix.Layout.numbered ((raw S π depth mark b order size rows) i)=embed S π depth mark b order size (rows i) :=
  SettledMatrix.Layout.numbered.apply_symm_apply _

/-- Every absent original RAM row is a vacant paid row, since both complete stock families
are present in the mathematical chronological state, even when their current widths vanish. -/
theorem blank {r : Ix} (vacant : r∉Set.range (raw S π depth mark b order size rows)) :
    ∃e : Fin b.rows,SettledMatrix.Layout.numbered r=Sum.inl e ∧ e∉Set.range edges := by
  have notIn (x : Source S π depth mark) (hit : embed S π depth mark b order size x=SettledMatrix.Layout.numbered r) : False := by
    apply vacant
    refine ⟨rows.symm x,SettledMatrix.Layout.numbered.injective ?_⟩
    rw [numbered_raw,rows.apply_symm_apply,hit]
  cases old : SettledMatrix.Layout.numbered r with
  | inl e=>
    refine ⟨e,rfl,?_⟩
    rintro ⟨a,eqn⟩
    apply notIn (.inl a)
    rw [old]
    exact congrArg Sum.inl eqn
  | inr x=>
    exact (notIn (.inr x) (by rw [old];rfl)).elim

/-- The scan visits both endpoints of every potential old row; the partial inverse names its
physical old ordinal, leaving each unbought catalogue row genuinely empty. -/
def lookup (r : Ix) : Option (Fin n) :=
  Function.extend (raw S π depth mark b order size rows) some (fun _=>none) r

theorem lookup_live (i : Fin n) :
    lookup S π depth mark b order size rows (raw S π depth mark b order size rows i)=some i :=
  (raw S π depth mark b order size rows).injective.extend_apply _ _ i

theorem lookup_found {r : Ix} {i : Fin n} (hit : lookup S π depth mark b order size rows r=some i) :
    raw S π depth mark b order size rows i=r := by
  by_cases inside : r∈Set.range (raw S π depth mark b order size rows)
  · obtain ⟨j,rfl⟩ := inside
    rw [lookup_live] at hit
    exact congrArg _ (Option.some.inj hit).symm
  · rw [lookup,Function.extend_apply' _ _ _ inside] at hit
    contradiction

theorem lookup_dormant {r : Ix} (vacant : lookup S π depth mark b order size rows r=none) :
    ∃e : Fin b.rows,SettledMatrix.Layout.numbered r=Sum.inl e ∧ e∉Set.range edges := by
  apply blank S π depth mark b order size rows
  rintro ⟨j,rfl⟩
  rw [lookup_live] at vacant
  contradiction

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRows

end
end OAI
