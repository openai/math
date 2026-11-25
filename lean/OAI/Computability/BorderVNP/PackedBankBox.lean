import OAI.Computability.BorderVNP.PackedBankBoxLayout

/-! # Sparse records for the repeated paid-term tensor

Every junction of a fixed paid term has one private directory entry. The local
public list stages each incident lane with one strided equality and invokes the
directory entry at all occurrences with a single box record. The reported
positions are addresses of the actual table entries of the shortening identity.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.PaidBox

open Crossing Crossing.CellBox CellSparse
open scoped Classical

variable {D m j : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- Canonical enumeration of the distinct local addresses, including zero-valued rows. -/
noncomputable def entryID (t : e.Entry) : Fin (Fintype.card e.Entry) := Fintype.equivFin e.Entry t

/-- Tag an actual table read with its position in the full gadget directory. -/
def ids (position : e.Entry → ℕ) (a : Fin e.count) : (e.net a).Tables ℕ :=
  fun v z x => position ⟨a,v,z,x⟩

variable (position : e.Entry → ℕ) (a : Fin e.count) (v : (e.net a).Site)

/-- The number of one-copy lanes at this site. -/
noncomputable abbrev arity := ∑ r, widths (e.net a) v r

/-- One-copy private factor with a fixed position ID for every possible bit row. -/
noncomputable def tableFactor : Factor :=
  factor (e.net a) (ids e position a) v (laneOrder (e.net a) v) Fin.val

/-- All public rows of one repeated internal site, followed by its one private box invocation. -/
noncomputable def siteDirectory (copies : ℕ) : Directory :=
  let d := arity e a v
  let b := copies*d
  ⟨[[tableFactor e position a v]],
    stageRecords copies b (src (widths (e.net a) v) copies) ++ [.box 0 b copies d], []⟩

/-- A fixed number of records, independently of the histogram count. -/
theorem recordCount (copies : ℕ) :
    (siteDirectory e position a v copies).records.length = arity e a v + 1 := by
  simp [siteDirectory,stageRecords_length]

private theorem records_valid_iff (copies : ℕ) (bank : ℕ → Bool) :
    (∀ r ∈ (siteDirectory e position a v copies).records,
      r.Valid (siteDirectory e position a v copies).boxes bank) ↔
    ∀ r ∈ stageRecords copies (copies*arity e a v) (src (widths (e.net a) v) copies),
      r.Valid (siteDirectory e position a v copies).boxes bank := by
  simp only [siteDirectory,List.mem_append,List.mem_singleton]
  constructor
  · exact fun h r hr => h r (Or.inl hr)
  · intro h r hr
    rcases hr with hr | rfl
    · exact h r hr
    · simp [Record.Valid]

private theorem terminalBound (u : Fin D × Bool) : ‖antipodalPosition u‖ ≤ 1 := by
  obtain ⟨i,b⟩ := u
  cases b <;> simp [antipodalPosition]

/-- Actual incident bits at this site in the physical paid profile's cable assignment. -/
noncomputable def data (p : Fin e.count → ℕ) (y : (e.profile j p).Assignment) :
    Fin (p a) → Fin (arity e a v) → Bool :=
  fun i k => bankLanes e.net antipodalPosition terminalBound p y a v i
    ((laneOrder (e.net a) v).symm k)

/-- The two consecutive regions of the canonical assignment, one cable-major and one copy-major. -/
noncomputable def siteBank (p : Fin e.count → ℕ) (y : (e.profile j p).Assignment) : ℕ → Bool :=
  let w := widths (e.net a) v
  stageBank (copies := p a) (inputBank w (data e a v p y)) (p a*arity e a v) (src w (p a))

/-- The physical incident data have exactly one extension across the two allocated regions. -/
theorem valid_unique (p : Fin e.count → ℕ) (y : (e.profile j p).Assignment) :
    let dir := siteDirectory e position a v (p a)
    let w := widths (e.net a) v
    (∀ r ∈ dir.records, r.Valid dir.boxes (siteBank e a v p y)) ∧
    ∀ bank, (∀ (i : Fin (p a)) (k : Fin (arity e a v)),
        bank ((src w (p a) k).atBit i.val 0) = data e a v p y i k) →
      (∀ r ∈ dir.records, r.Valid dir.boxes bank) →
      ∀ t < (p a*arity e a v) + (p a*arity e a v), bank t = siteBank e a v p y t := by
  dsimp only
  let w := widths (e.net a) v
  let old := inputBank w (data e a v p y)
  let base := p a * arity e a v
  let dir := siteDirectory e position a v (p a)
  have hs := stageBank_valid old base (src w (p a)) (fun i k => src_lt w i k) dir.boxes
  refine ⟨(records_valid_iff e position a v (p a) _).2 hs.2, fun bank hbits hrows => ?_⟩
  apply stageBank_unique old bank base (src w (p a)) (fun i k => src_lt w i k) _ dir.boxes
  · exact (records_valid_iff e position a v (p a) _).1 hrows
  · intro t ht
    obtain ⟨i,k,rfl⟩ := src_cover w ht
    exact (hbits i k).trans (inputBank_read w _ i k).symm

private theorem visits (copies : ℕ) :
    (siteDirectory e position a v copies).occurrences =
      List.ofFn (fun i : Fin copies => (⟨tableFactor e position a v,
        copies * arity e a v + i.val * arity e a v,i.val⟩ : Occurrence)) := by
  simp only [Directory.occurrences, siteDirectory, List.flatMap_append]
  rw [show (stageRecords copies (copies * arity e a v) (src (widths (e.net a) v) copies)).flatMap _ =
      ([] : List Occurrence) from List.flatMap_eq_nil_iff.mpr (fun r hr => by
        obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hr
        rfl)]
  simp only [List.nil_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.getD_cons_zero,
    List.map_cons,List.map_nil]
  rw [← List.map_eq_flatMap]
  apply List.ext_getElem <;> simp

/-- The selected actual table address for one occurrence of the internal site. -/
noncomputable def selectedEntry (p : Fin e.count → ℕ) (y : (e.profile j p).Assignment)
    (i : Fin (p a)) : e.Entry :=
  let lanes := bankLanes e.net antipodalPosition terminalBound p y a v i
  ⟨a,v,(fun u l => lanes (.inl ⟨u,l⟩)),(fun u l => lanes (.inr ⟨u,l⟩))⟩

/-- All observations of the staged directory are exactly the selected shortening-table IDs. -/
theorem observations (p : Fin e.count → ℕ) (y : (e.profile j p).Assignment) :
    (siteDirectory e position a v (p a)).observations (siteBank e a v p y) =
      some (List.ofFn fun i => (false,some (position (selectedEntry e a v p y i)))) := by
  rw [Directory.observations,visits,List.ofFn_eq_map,List.mapM_map,List.ofFn_eq_map]
  let result (i : Fin (p a)) := (false,some (position (selectedEntry e a v p y i)))
  have h (i : Fin (p a)) : (tableFactor e position a v).observe (siteBank e a v p y)
        (p a * arity e a v + i.val * arity e a v) i.val = some (result i) := by
    rw [tableFactor,observe_factor]
    apply congrArg (fun z => some (false,some (localRow (e.net a) (ids e position a) v z)))
    funext l
    change stageBank (copies := p a) _ _ _
      (p a * arity e a v + i.val * arity e a v + ((laneOrder (e.net a) v) l).val) = _
    rw [Nat.add_assoc]
    simp only [stageBank, Nat.not_lt.mpr (Nat.le_add_right _ _), ite_false,
      Nat.add_sub_cancel_left, packedBank_read,inputBank_read,data,Equiv.symm_apply_apply]
  change (List.finRange (p a)).mapM (fun i => (tableFactor e position a v).observe
    (siteBank e a v p y) (p a * arity e a v + i.val * arity e a v) i.val) = some _
  rw [funext h]
  exact List.mapM_pure (m := Option) (f := result)

/-- Evaluating those entry IDs gives the exact field-valued physical junction table. -/
theorem profile_read (p : Fin e.count → ℕ) (y : (e.profile j p).Assignment) (first : Fin D × Bool)
    (x : Ports (fun _ : Fin D × Bool => j*m)) :
    (e.profile j p).read (e.profileTables j p first) y x (.inr (.inr ⟨a,v⟩)) =
      ∏ i : Fin (p a), e.entry (selectedEntry e a v p y i) := rfl

/-- Per-site allocated bit count and privately expanded box visits, with no replication
of one-copy metadata. -/
theorem expandedCount (copies : ℕ) :
    (siteDirectory e position a v copies).occurrences.length +
      ((copies*arity e a v) + (copies*arity e a v)) = copies * (1 + 2*arity e a v) := by
  rw [visits,List.length_ofFn]
  ring

end Packing.PaidBox

end BorderVNP
end Computability
end OAI
