import OAI.Computability.VPVNP.CompressorSlotOwnerDecode
import OAI.Computability.VPVNP.CompressorSlotOwners

/-!
# The physical endpoint owner stream for a selected layout

A dense original arc record stores the selected layout's three packed sites and
its CD indicator. With these input records and the four subdivision counts, the
native genuine and dummy workers compute the exact owner of every absolute
field in the shrinking directory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotOwners

open Compression Compression.PackingData Compression.SurvivingSlots Slots SlotSchedule BurstRAM

variable {V H Tag L : Type*} {d c N J nL pad w : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c) (subdiv : Fin 4 → ℕ)
variable (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (lanes : L ≃ Fin nL)

/-- Column offsets of the three site words in the old arc record. -/
def roleOffset : PackedRole → ℕ
  | .a => 0
  | .b => 1
  | .d => 2

private theorem role_lt (r : PackedRole) : roleOffset r < 3 := by cases r <;> decide

/-- The layout parameters and physical input columns for the genuine worker.
Every original arc has a CD indicator. Its site words are used only on CD arcs. -/
structure GenuineTables (layout : Bool) (p : Fin 8 → Word w) (m : Memory w) : Prop where
  laneCount : (p 0).val = nL
  subdivCount : (p 1).val = ∑ t, subdiv t
  baseCount : (p 2).val = oldBaseArcCount N J d c
  realCount : (p 6).val = (N*(J*nL))*2
  arcFits : (p 3).val + 4 * (oldBaseArcCount N J d c * nL) ≤ 2^w
  rolesFit : (p 4).val + 8 ≤ 2^w
  subdivFits : (p 5).val + 4 ≤ 2^w
  role : ∀ (t : Fin 4) (s : Fin 2),
    (m ((p 4).val + (2*t.val+s.val))).val = roleOffset (endRole layout (decide (s=1)) t)
  count : ∀ (t : Fin 4), (m ((p 5).val+t.val)).val = subdiv t
  cd : ∀ a : Arc V H Tag L d c,
    (m ((p 3).val + 4*(oldArcIndex P vertices tags lanes a).val + 3)).val = if isCD P a then 1 else 0
  packed : ∀ (a : P.Motif) (r : PackedRole),
    (m ((p 3).val + 4*(oldArcIndex P vertices tags lanes a.val).val + roleOffset r)).val =
      (siteIndex vertices tags lanes (P.survivingRole layout r a)).val

private theorem wordOwner_at {E : Type*} {A B : ℕ} (D : Directory E A B) (j : Fin A) (u : Word w) (h : u.val = j.val) :
    D.wordOwner u = Fin.ofNat _ (D.destination j).val := by
  have hj : u.val < A := h ▸ j.isLt
  simp only [Directory.wordOwner, encodedPlacement, dite_eq_left hj, Equiv.refl_symm,
    Equiv.refl_apply]
  rw [show (⟨u.val,hj⟩ : Fin A) = j from Fin.ext h]

/-- Every genuine worker output equals the directory word at this absolute ID,
including IDs whose subdivision is too large or whose old arc is thick–thick. -/
theorem genuine_directory (layout : Bool) (p : Fin 8 → Word w) (m : Memory w)
    (tables : GenuineTables P subdiv vertices tags lanes layout p m) (i : Word w)
    (hi : i.val < (keyCount N J d c subdiv * nL)*2) :
    genuineOwner p m i = (slotDirectory P subdiv vertices tags lanes layout (pad := pad)).wordOwner i := by
  let a : Fin (keyCount N J d c subdiv * nL) := ⟨i.val/2, by omega⟩
  let s : Fin 2 := ⟨i.val%2, by omega⟩
  let field := finProdFinEquiv (a.castAdd ((N*(J*nL))*pad),s)
  have hfield : field.val = i.val := by change i.val%2+2*(i.val/2)=i.val; omega
  let x := genuineDigits subdiv a
  let old := digitArc P subdiv vertices tags lanes x
  let t := x.1.1.1
  let j := x.1.2.val
  let f := natDigits (p 0).val (p 1).val (p 2).val i.val
  let id := (oldArcIndex P vertices tags lanes old).val
  let role := endRole layout (decide (s=1)) t
  have ht : f.edgeType = t.val := by
    dsimp only [f,natDigits]; rw [tables.laneCount, tables.subdivCount, tables.baseCount]; rfl
  have hj : f.subdivision = j := by
    dsimp only [f,natDigits]; rw [tables.laneCount, tables.subdivCount]; rfl
  have hid : f.oldArc = id := by
    dsimp only [f,natDigits]; rw [tables.laneCount, tables.subdivCount, tables.baseCount]
    exact (digitArc_index P subdiv vertices tags lanes x).symm
  have hs : f.side = s.val := rfl
  have hrole := tables.role t s
  have hc := tables.cd old
  have hinput : GenuineInput p m i := by
    have hold : id < oldBaseArcCount N J d c * nL := (oldArcIndex P vertices tags lanes old).isLt
    have htype : t.val < 4 := t.isLt
    have hside : s.val < 2 := s.isLt
    have hf := tables.arcFits
    have hr := tables.rolesFit
    have hsd := tables.subdivFits
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [tables.subdivCount]; have := x.1.2.isLt; omega
    · change (p 3).val + 4*f.oldArc + 3 < 2^w; rw [hid]; omega
    · change (p 4).val + (2*f.edgeType+f.side) < 2^w; rw [ht,hs]; omega
    · change (p 5).val + f.edgeType < 2^w; rw [ht]; omega
    · change (m ((p 4).val+(2*f.edgeType+f.side))).val < 3
      rw [ht,hs,hrole]; exact role_lt _
    · change (m ((p 3).val + 4*f.oldArc+3)).val ≤ 1
      rw [hid,hc]; split <;> decide
  rw [genuineOwner_eq _ _ _ hinput, wordOwner_at _ field i hfield.symm]
  congr 1
  have hdest := directory_genuine_destination P subdiv vertices tags lanes layout (pad := pad) a s
  change (natGenuineOwner p m i.val) = _; rw [hdest]
  change (if (m ((p 3).val+4*f.oldArc+3)).val = 1 ∧ f.subdivision < (m ((p 5).val+f.edgeType)).val
    then 2*(m ((p 3).val+4*f.oldArc + (m ((p 4).val+(2*f.edgeType+f.side))).val)).val + f.side
    else (p 6).val+i.val) = if j < subdiv t then if h : isCD P old then
      2*(siteIndex vertices tags lanes (P.survivingRole layout role ⟨old,h⟩)).val+s.val
    else (N*(J*nL))*2+field.val else (N*(J*nL))*2+field.val
  rw [ht,hj,hid,hs,hrole,hc,tables.count,tables.realCount,hfield]
  by_cases hv : j < subdiv t
  · by_cases hcd : isCD P old
    · rw [ite_eq_left hcd, ite_eq_left ⟨rfl,hv⟩, ite_eq_left hv, dite_eq_left hcd]
      exact congrArg (fun n => 2*n+s.val) (tables.packed ⟨old,hcd⟩ role)
    · rw [ite_eq_right hcd, ite_eq_right (fun h => Nat.zero_ne_one h.1), ite_eq_left hv, dite_eq_right hcd]
  · rw [ite_eq_right (fun h => hv h.2), ite_eq_right hv]

/-- The dummy site table stores the tag successor with the same vertex and lane. -/
structure DummyTables (pad : ℕ) (p : Fin 3 → Word w) (m : Memory w) : Prop where
  twoFits : 2 < 2^w
  padCount : (p 0).val = pad
  nextFits : (p 1).val + N*(J*nL) ≤ 2^w
  nextSite : ∀ b : Fin (N*(J*nL)), let site := siteIndex vertices tags lanes
    (m ((p 1).val+b.val)).val = (site (dummyEnd tags true (site.symm b))).val

/-- The dummy worker uses a local cursor while its physical directory field
has an offset equal to the whole genuine interval. -/
theorem dummy_directory (layout : Bool) (p : Fin 3 → Word w) (m : Memory w)
    (tables : DummyTables vertices tags lanes pad p m) (i : Word w)
    (hi : i.val < ((N*(J*nL))*pad)*2)
    (fit : RecordCount N J nL d c pad subdiv * 2 ≤ 2^w) :
    dummyOwner p m i = (slotDirectory P subdiv vertices tags lanes layout (pad := pad)).wordOwner
      (Fin.ofNat _ ((keyCount N J d c subdiv * nL)*2+i.val)) := by
  let a : Fin ((N*(J*nL))*pad) := ⟨i.val/2, by omega⟩
  let s : Fin 2 := ⟨i.val%2, by omega⟩
  let field := finProdFinEquiv (a.natAdd (keyCount N J d c subdiv * nL),s)
  let localField := finProdFinEquiv (a,s)
  have hl : localField.val = i.val := by change i.val%2+2*(i.val/2)=i.val; omega
  have hg : field.val = (keyCount N J d c subdiv * nL)*2+i.val := by
    change i.val%2+2*((keyCount N J d c subdiv * nL)+i.val/2) = _; omega
  have hb : (Fin.ofNat (2^w) ((keyCount N J d c subdiv * nL)*2+i.val)).val = field.val := by
    rw [← hg]; exact Nat.mod_eq_of_lt (field.isLt.trans_le fit)
  have hs : a.divNat.val = i.val/2/pad := rfl
  have hf : (p 1).val + i.val/2/(p 0).val < 2^w := by
    rw [tables.padCount, ← hs]; have := a.divNat.isLt; have := tables.nextFits; omega
  rw [dummyOwner_eq _ _ _ tables.twoFits hf, wordOwner_at _ field _ hb]
  congr 1
  rw [directory_dummy_destination P subdiv vertices tags lanes layout a s]
  change (2*(if i.val%2 = 0 then i.val/2/(p 0).val else (m ((p 1).val+i.val/2/(p 0).val)).val)+i.val%2) =
    2*(if s.val=0 then localField.val/2/pad else _) + s.val
  rw [hl, tables.padCount, ← hs, tables.nextSite]

end CompressorRecords.SlotOwners

end VPVNP
end Computability
end OAI
