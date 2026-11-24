import OAI.Computability.VPVNP.CompressorRecordIncidenceLayout
import OAI.Computability.VPVNP.CompressorRecordRefreshPhases

/-!
# Reading the common incidence directory at a degree refresh

The external pass obtains its gathered width directly from the site's outgoing width column.
The outgoing base mate and the packed old displacement are the two base inputs of the bundle
pass. Both are already present in a represented cursor, shrink or refresh state.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.IncidenceDirectory

open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh PortRefresh

variable {bits a g : ℕ} (X : State a (a+g)) (T : IncidenceDirectory bits) (m : Memory bits)

private theorem base_parts (b : X.Base × Fin (2^a)) :
    (baseOrder X b).val / 2^a = (X.baseIndex b.1).val ∧ (baseOrder X b).val % 2^a = b.2.val := by
  rw [baseOrder_val]
  refine ⟨?_,Nat.mul_add_mod_of_lt b.2.isLt⟩
  rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos a), Nat.div_eq_of_lt b.2.isLt, Nat.add_zero]

/-- Read a natural width directly from the directory's actual width column. -/
theorem Represents.refresh_widths (rep : T.Represents X m) (q : Fin 4 → BurstRAM.Word bits)
    (old : q 2 = T.width) (room : ∀ b, (∑ j, bundleWidths (bitWordFinEquiv a) (splitWidths X) b j) < 2^bits) :
    RefreshGather.HasOldWidths X (baseOrder X) q m := by
  intro b l
  let parts := splitBitWord a g l
  let s := ((b.1,parts.2),b.2)
  let j := bitWordFinEquiv a parts.1
  have width : bundleWidths (bitWordFinEquiv a) (splitWidths X) s j = X.width (b,l) := by
    change X.width ((b.1,b.2),(splitBitWord a g).symm ((bitWordFinEquiv a).symm j,parts.2)) = _
    simp [j,parts]
  have bound := (Finset.single_le_sum (s := Finset.univ) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ j) (f := bundleWidths (bitWordFinEquiv a) (splitWidths X) s)).trans_lt (room s)
  rw [width] at bound
  simp only [old, (base_parts X b).1, (base_parts X b).2]
  change (m (T.width + actualPort X ((b.1,l),b.2)).val).val = _
  rw [rep.width]
  exact Nat.mod_eq_of_lt bound

/-- The directory's outgoing base mate and old displacement supply the bundle initializer. -/
theorem Represents.refresh_base (rep : T.Represents X m) (q : Fin 8 → BurstRAM.Word bits)
    (lanes : (q 0).val = 2^g) (mate : q 1 = T.baseOut) (disp : q 5 = T.shift)
    (room : Fintype.card X.Base * 2^a ≤ 2^bits) (wide : 2^(a+g) ≤ 2^bits) :
    BundleDirectory.BaseTables (splitSlots X) (baseOrder X) q m := by
  apply BundleDirectory.BaseTables.ofOld (baseOrder X) q X.slots m lanes
  · intro b
    change (m (q 1 + CursorRAM.encode bits (baseOrder X b).val).val).val = _
    rw [mate, ← basePort_number, rep.baseOut, basePort_number]
    exact Nat.mod_eq_of_lt ((baseOrder X _).isLt.trans_le room)
  · intro b
    change (m (q 5 + CursorRAM.encode bits (baseOrder X b).val).val).val = _
    rw [disp, ← basePort_number, rep.shift]
    exact Nat.mod_eq_of_lt ((bitWordFinEquiv (a+g) _).isLt.trans_le wide)

/-- From an arbitrary represented old state, the native external construction produces
all refreshed bundle targets, widths and both endpoint segment tables in shared memory. -/
theorem Represents.external_execution (rep : T.Represents X m) (p : Fin 8 → BurstRAM.Word bits)
    (lanes : BurstRAM.Word bits) (degree : (p 0).val = 2^a) (residual : lanes.val = 2^g)
    (regions : RefreshRAM.Regions p (Fintype.card X.Base * 2^a * 2^g * 2^a))
    (dirLayout : BundleDirectory.Layout (directoryWords p lanes T.baseOut T.shift)
      (Fintype.card X.Base * 2^a) (2^g))
    (wireApart : RefreshGather.SourcesDisjoint (gatherWords p lanes T.width) (Fintype.card X.Base * 2^a * 2^g * 2^a))
    (baseApart : baseOutsideGather X (baseOrder X) p T.baseOut T.shift)
    (room : ∀ b, (∑ j, bundleWidths (bitWordFinEquiv a) (splitWidths X) b j) < 2^bits) :
    ExternalExecution X (baseOrder X) p lanes T.width T.baseOut T.shift m regions.fits := by
  have ha := Nat.two_pow_pos a
  have hg := Nat.two_pow_pos g
  let V := Fintype.card X.Base
  have hv : 0 < V := Fintype.card_pos
  have bound : V * 2^a * 2^g ≤ 2^bits := (Nat.le_mul_of_pos_right _ ha).trans regions.fits
  have hbase := (Nat.le_mul_of_pos_right (V * 2^a) hg).trans bound
  have hlanes : 2^(a+g) ≤ 2^bits := by
    rw [pow_add, Nat.mul_assoc] at *
    exact (Nat.le_mul_of_pos_left _ hv).trans bound
  apply external_phases X (baseOrder X) p lanes T.width T.baseOut T.shift degree residual regions dirLayout m
    (rep.refresh_widths X T m _ rfl room) _ wireApart baseApart room
  exact rep.refresh_base X T m _ residual rfl rfl hbase hlanes

end CompressorRecords.IncidenceDirectory

end VPVNP
end Computability
end OAI
