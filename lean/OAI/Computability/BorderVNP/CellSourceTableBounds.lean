import OAI.Computability.BorderVNP.FiniteCellCopiesContraction
import OAI.Computability.BorderVNP.CrossingCellBoxRecords
import OAI.Computability.BorderVNP.CellPacketFields

/-! # Fixed local table sizes of the actual finite-field and crossing boxes

The high-degree polynomial used to print an individual factor is applied to
its local tuple. The degree-three input sites have at most eight entries, and
the paid crossing bank uses the fixed lane dimension of its chosen template.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldDirectory

open Crossing CellSparse
open scoped Classical

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable {F : Type*} [Fintype F]

/-- The finite-field row reader emitted by a degree-three original site has
at most eight key wires and eight actual stored scalar IDs. -/
theorem factor_tableBound (table : N.Tables F) (s : N.Site) (h : Fintype.card (Lane N s) ≤ 3) :
    (factor N table s).TableBound 8 := by
  obtain ⟨ha,hr⟩ := literal_size N table s h
  exact ⟨ha.trans (by decide),hr⟩

/-- The actual scalar fields of a finite-field leaf lie in the fixed one-copy
wire and field enumerations. -/
theorem factor_fields (table : N.Tables F) (s : N.Site) {U : ℕ}
    (h : Fintype.card (Lane N s) ≤ 3) (h₈ : 8 ≤ U)
    (hw : Fintype.card (Wire N) ≤ U) (hf : Fintype.card F ≤ U) :
    Packet.FactorFields (factor N table s) U := by
  obtain ⟨ha,hr⟩ := literal_size N table s h
  refine ⟨⟨⟨ha.trans (by omega),hr.trans h₈⟩,?_⟩,?_⟩
  · intro i hi
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
    exact ((wireNumber N (wire N s ((Fintype.equivFin (Lane N s)).symm j))).isLt.le).trans hw
  · intro i hi
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
    exact ((Fintype.equivFin F (row N table s j.val)).isLt.le).trans hf

namespace Copies

/-- Every stored factor in the actual bottom-bundle packet is a degree-three
input-site table. Multiplicity and stride do not affect this assertion. -/
theorem stored_tableBound (sites : List N.Site) (table : N.Tables F) (copies w : ℕ)
    (h : ∀ s ∈ sites, Fintype.card (Lane N s) ≤ 3) :
    ∀ fs ∈ (directory N sites table copies w).boxes, ∀ f ∈ fs, f.TableBound 8 := by
  intro fs hs f hf
  change fs ∈ [sites.map (factor N table)] at hs
  rw [List.mem_singleton] at hs
  subst fs
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hf
  exact factor_tableBound N table s (h s hs)

/-- A concrete upper bound for every scalar in the encoded finite-field
bottom-bundle packet, including all report-bit addresses. -/
noncomputable def rawLimit (sites : List N.Site) (copies w privateWires : ℕ) (F : Type*) [Fintype F] :=
  privateWires + sites.length + copies + Fintype.card (Wire N) + Fintype.card F + w +
    width N copies + Fintype.card F*w + 8

/-- The actual sparse packet meets the raw field bound, with the complete
original data stored once even for an empty or zero-copy bundle. -/
theorem rawFields (sites : List N.Site) (table : N.Tables F) (copies w privateWires : ℕ)
    (h : ∀ s ∈ sites, Fintype.card (Lane N s) ≤ 3) :
    Packet.RawFields (directory N sites table copies w) privateWires (rawLimit N sites copies w privateWires F) := by
  let U := rawLimit N sites copies w privateWires F
  have h₈ : 8 ≤ U := by dsimp [U,rawLimit]; omega
  have hw : Fintype.card (Wire N) ≤ U := by dsimp [U,rawLimit]; omega
  have hf : Fintype.card F ≤ U := by dsimp [U,rawLimit]; omega
  refine ⟨by dsimp [rawLimit]; omega, ?_, ?_, ?_, ?_⟩
  · simp only [directory,List.length_cons,List.length_nil,List.length_ofFn]
    exact ⟨by omega,by omega,hf⟩
  · intro fs hs
    change fs ∈ [sites.map (factor N table)] at hs
    rw [List.mem_singleton] at hs
    subst fs
    refine ⟨by simp only [List.length_map]; dsimp [rawLimit]; omega,?_⟩
    intro f hmem
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hmem
    exact factor_fields N table s (h s hs) h₈ hw hf
  · intro r hr
    change r ∈ [.box 0 0 copies (Fintype.card (Wire N))] at hr
    rw [List.mem_singleton] at hr
    subst r
    exact ⟨trivial,Nat.zero_le _,Nat.zero_le _,by dsimp [rawLimit]; omega,hw⟩
  · intro bs hb
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hb
    refine ⟨by simp only [List.length_ofFn]; dsimp [rawLimit]; omega,?_⟩
    intro j hj
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hj
    have ht := claimAddress_lt N copies w v i
    dsimp [rawLimit]
    omega

end Copies
end FieldDirectory

namespace Crossing.CellBox

open CellSparse

variable {D d : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}

omit [Fintype P] in
/-- A fixed paid crossing template uses at most the larger of its lane count
and its complete one-copy table of binary entries. -/
theorem factor_tableBound (N : Network D P bits) (id : N.Tables ℕ) (v : N.Site)
    (order : Lane N v ≃ Fin d) (addr : Fin d → ℕ) :
    (factor N id v order addr).TableBound (max d (2^d)) := by
  simp only [factor,Factor.TableBound,rows,List.length_ofFn]
  exact ⟨le_max_left ..,le_max_right ..⟩

omit [Fintype P] in
/-- The sparse crossing bank stores exactly one fixed-arity private factor. -/
theorem bank_stored_tableBound {A : ℕ} (N : Fin A → Network D P bits) (p : Fin A → ℕ)
    (a : Fin A) (v : (N a).Site) (order : Lane (N a) v ≃ Fin d) (id : ∀ t, (N t).Tables ℕ) :
    ∀ fs ∈ (bankDirectory N p a v order id).boxes, ∀ f ∈ fs, f.TableBound (max d (2^d)) := by
  intro fs hfs f hf
  simp only [bankDirectory,directory,List.mem_singleton] at hfs
  subst fs
  rw [List.mem_singleton] at hf
  subst f
  exact factor_tableBound _ _ _ _ _

end Crossing.CellBox

end BorderVNP
end Computability
end OAI
