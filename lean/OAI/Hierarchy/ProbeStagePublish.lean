import OAI.Hierarchy.ProbeStageProgram
import OAI.Hierarchy.ProbeStagePrefixMemory

namespace OAI
/-! # Passing the actual inner rows to the next native subdivider -/

namespace Hierarchy.ProbeStage.Native
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section

structure ParentStored {h w : ℕ} (d : ℕ) (π : Equiv.Perm (Fin (2^h))) (j : ℕ) (m : Memory w) : Prop where
  group : Resident (parentAt h d copies j 0) m (fun r => ((history h d π j).encode ((history h d π j).tiles.group r)).val)
  source : Resident (parentAt h d copies j 1) m (fun r => ((history h d π j).tiles.input r).val)
  target : Resident (parentAt h d copies j 2) m (fun r => ((history h d π j).tiles.output r).val)

structure RankStored {h d w : ℕ} (π : Equiv.Perm (Fin (2^h))) (j : Fin (rounds d)) (m : Memory w) : Prop where
  color : Resident (rankAt h d copies j.val 0) m (fun r => ((assigned j π).color r).val)
  source : Resident (rankAt h d copies j.val 1) m (fun r => ((assigned j π).enterRank r).val)
  target : Resident (rankAt h d copies j.val 2) m (fun r => ((assigned j π).exitRank r).val)

def GeometryStored {h d w : ℕ} (j : Fin (rounds d)) (m : Memory w) : Prop :=
  ∀ (c : Fin 8) (i : Fin (extent h d)),m (GeometryCell.address copies (⟨j,c,i⟩ : GeometryCell h d))=
    (GeometryCell.value (⟨j,c,i⟩ : GeometryCell h d) : Word w)

theorem geometryStored_tape (h d w : ℕ) (j : Fin (rounds d)) (m : Memory w) :
    GeometryStored (h:=h) j (inputTape h d w m) := fun c i => inputTape_geometry m ⟨j,c,i⟩

private theorem fixed_read {h d : ℕ} (j : Fin (rounds d)) (m : Memory (wordBits h d copies))
    (store : GeometryStored (h:=h) j m) {n : ℕ} (lim : n≤extent h d) (c : Fin 8) (f : Fin n → ℕ)
    (value : ∀ i : Fin n,GeometryCell.value (⟨j,c,⟨i.val,i.isLt.trans_le lim⟩⟩ : GeometryCell h d)=f i) :
    Resident (geometryAt h d copies j.val c) m f := by
  apply Resident.of_cells _ _ _ lim (lim.trans (extent_word h d copies).le)
  intro i
  exact (store c ⟨i.val,i.isLt.trans_le lim⟩).trans (congrArg (fun v : ℕ => (v:Word (wordBits h d copies))) (value i))

/-- Only actual RAM cells enter these twelve source operands. The six
static tables are read from the immutable geometry area of the initial
tape. -/
theorem split_loaded {h d : ℕ} (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (j : Fin (rounds d))
    (m : Memory (wordBits h d copies)) (geom : GeometryStored (h:=h) j m) (parent : ParentStored d π j.val m)
    (ranks : RankStored π j m) :
    let p := history h d π j.val
    Loaded p.tiles (radix_pos h d) (assigned j π) p.encode
      (operandsAt h d copies j.val) (tablesAt h d copies j.val) m := by
  let p := history h d π j.val
  obtain ⟨count,span⟩ := history_sizes hd π j.isLt.le
  change p.count = _ at count
  change p.shape.span = _ at span
  obtain ⟨_,groups,ports,colors,blocksFit⟩ := room_extents (h:=h) hd j.isLt.le
  have gr : p.count≤extent h d := count.trans_le groups
  have pr : p.shape.span≤extent h d := span.trans_le ports
  have kr : blocks p.shape.span (radix h d)≤extent h d := by rw [show p.shape.span=_ from span];exact blocksFit
  refine ⟨parent.group,parent.source,parent.target,ranks.color,ranks.source,ranks.target,?_,?_,?_,?_,?_,?_⟩
  · apply fixed_read j m geom gr 0;intro i
    simp [GeometryCell.value,tableWords,tableAtIndex,← count,← span,i.isLt]; first | rfl | exact Or.inl rfl
  · apply fixed_read j m geom gr 1;intro i
    simp [GeometryCell.value,tableWords,tableAtIndex,← count,i.isLt]
  · apply fixed_read j m geom pr 2;intro i
    simp [GeometryCell.value,tableWords,tableAtIndex,← span,i.isLt]; first | rfl
  · apply fixed_read j m geom pr 3;intro i
    simp [GeometryCell.value,tableWords,tableAtIndex,← span,i.isLt]; first | rfl
  · apply fixed_read j m geom colors 4;intro i
    simp [GeometryCell.value,tableWords,tableAtIndex,i.isLt]
  · apply fixed_read j m geom kr 5;intro i
    simp [GeometryCell.value,tableWords,tableAtIndex,← span,i.isLt]

/-- The allocator starts from the three earlier row banks, including in
the first round where no ranks have yet been written. -/
theorem endpoint_loaded {h d : ℕ} (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (j : Fin (rounds d))
    (m : Memory (wordBits h d copies)) (geom : GeometryStored (h:=h) j m) (parent : ParentStored d π j.val m) :
    let p := history h d π j.val
    (endpointAt h d copies j.val).Stored p.tiles (radix_pos h d) p.encode m := by
  let p := history h d π j.val
  obtain ⟨count,span⟩ := history_sizes hd π j.isLt.le
  change p.count = _ at count
  change p.shape.span = _ at span
  obtain ⟨_,groups,ports,_,_⟩ := room_extents (h:=h) hd j.isLt.le
  have gr : p.count≤extent h d := count.trans_le groups
  have pr : p.shape.span≤extent h d := span.trans_le ports
  refine ⟨parent.group,parent.source,parent.target,?_,?_,?_,?_⟩
  · apply fixed_read j m geom gr 0;intro i
    simp [GeometryCell.value,tableWords,tableAtIndex,← count,← span,i.isLt]; first | rfl | exact Or.inl rfl
  · apply fixed_read j m geom pr 2;intro i
    simp [GeometryCell.value,tableWords,tableAtIndex,← span,i.isLt]; first | rfl
  · apply fixed_read j m geom pr 6;intro i
    simp [GeometryCell.value,← span,i.isLt]; first | rfl
  · apply fixed_read j m geom pr 7;intro i
    simp [GeometryCell.value,← span,i.isLt]; first | rfl | exact Or.inl rfl

theorem prepare_endpoint_words {h d : ℕ} (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (j : Fin (rounds d))
    (m : Memory (wordBits h d copies)) (geom : GeometryStored (h:=h) j m) (parent : ParentStored d π j.val m) :
    let ps := prepareRows h d j.val
    let p := history h d π j.val
    ∀ (r : Fin (2^h)) (i : Fin 3), result ps m ((blockBank h d copies j.val i).base+r.val)=
      (Endpoints.words p.tiles (radix_pos h d) p.encode r i : Word _) := by
  let p := history h d π j.val
  let x := endpointAt h d copies j.val
  have inside := allocator_end h d copies j.val
  have sep := separate h d copies j.val 14 (stride d copies-9) (by unfold stride;omega)
  change _≤output h d copies j.val at sep
  have end_ := (output_end h d copies j.val).trans_lt
    ((phase_in_heap (Nat.succ_le_of_lt j.isLt)).trans_lt (heap_room h d copies))
  exact (x.emit p.tiles (radix_pos h d) p.encode m (endpoint_loaded hd π j m geom parent)
    le_rfl (endpoint_fits h d copies j.val) (by omega)).2

/-- The compiled nine-field output labels the real routed rows and
supplies all three input banks of depth j+1 on the very same memory. -/
theorem publish {h d : ℕ} (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (j : Fin (rounds d))
    (m : Memory (wordBits h d copies)) (geom : GeometryStored (h:=h) j m)
    (parent : ParentStored d π j.val m) (ranks : RankStored π j m) :
    let ps := writeRows h d j.val
    let after := result ps m
    let p := history h d π j.val
    (program _ ps).Exec m after (clock ps) ∧ ParentStored d π (j.val+1) after ∧
      ∀ (r : Fin (2^h)) (i : Fin 9),after (output h d copies j.val+i.val*2^h+r.val)=
        (rowWords p.tiles (radix_pos h d) (assigned j π) p.encode r i : Word _) := by
  let p := history h d π j.val
  have loaded := split_loaded hd π j m geom parent ranks
  have safe := write_fits (h:=h) j.isLt
  have reader := operands_fit h d copies j.val
  have e := emit p.tiles (radix_pos h d) (assigned j π) p.encode _ _ m loaded safe le_rfl reader
  obtain ⟨g,s,t⟩ := inner_resident p.tiles (radix_pos h d) (assigned j π) p.encode _ _ m
    (h:=h) rfl ((height_extent h d).trans (extent_word h d copies).le) loaded safe le_rfl reader
  exact ⟨e.1,⟨g,s,t⟩,e.2⟩

end
end Hierarchy.ProbeStage.Native

end OAI
