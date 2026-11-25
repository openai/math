import OAI.Computability.MultitapeWeakETH.HistoryPacket
import OAI.Computability.IntegerMultiplication.Code.Chunk
import OAI.Computability.VPVNP.PairRefreshHalfDecoder

/-! # Separating the old child packets from the remaining private choices -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid.ChildScan

open IntegerMultiplication Code VPVNP Compression PairSimulation LocalHistory NodeArguments

/-- Reject a short candidate, then read each child argument at its actual width. -/
def splitPackets (q : List Tally × Bits.Word) : Option (List Bits.Word × Bits.Word) :=
  bif Iter.small (q.2,q.1.flatten) then none else some (Piecework.segment q.1 q.2)

theorem splitPackets_poly : Poly splitPackets := by
  have short := ((Easy.snd (X:=List Tally) (Y:=Bits.Word)).pair (Easy.fst.compose Easy.flatten)).compose Iter.small_easy
  exact Poly.choose short.poly (Code.Poly.const none) (Piecework.easy.compose Easy.some).poly

private theorem segment_input (sizes : List Tally) (bits : Bits.Word) :
    (Piecework.segment sizes bits).1.flatten ++ (Piecework.segment sizes bits).2 = bits := by
  induction sizes generalizing bits with
  | nil => rfl
  | cons s sizes ih =>
    simp only [Piecework.segment,cutLists,List.flatten_cons,List.append_assoc,ih,List.take_append_drop]

private theorem segment_sizes (sizes : List Tally) (bits : Bits.Word) (room : sizes.flatten.length ≤ bits.length) :
    (Piecework.segment sizes bits).1.map (tally ∘ List.length) = sizes := by
  induction sizes generalizing bits with
  | nil => rfl
  | cons s sizes ih =>
    simp only [List.flatten_cons,List.length_append] at room
    have next : sizes.flatten.length ≤ (bits.drop s.length).length := by simp only [List.length_drop]; omega
    simp only [Piecework.segment,cutLists,List.map_cons,Function.comp_apply,List.length_take,
      Nat.min_eq_left (show s.length≤bits.length by omega),recover_tally,ih _ next]

private theorem segment_complete (rows : List Bits.Word) (tail : Bits.Word) :
    Piecework.segment (rows.map (tally ∘ List.length)) (rows.flatten ++ tail) = (rows,tail) := by
  induction rows with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,Piecework.segment,List.flatten_cons,List.append_assoc,Function.comp_apply,
      Piecework.cut_of_length _ x _ (tally_length _),ih]

theorem splitPackets_iff (sizes : List Tally) (bits : Bits.Word) (rows : List Bits.Word) (tail : Bits.Word) :
    splitPackets (sizes,bits) = some (rows,tail) ↔
      rows.map (tally ∘ List.length) = sizes ∧ bits = rows.flatten ++ tail := by
  constructor
  · intro ok
    have room : sizes.flatten.length ≤ bits.length := by
      by_contra! short
      simp only [splitPackets,Iter.small,decide_eq_true short,Bool.cond_true] at ok
      cases ok
    have eq : Piecework.segment sizes bits = (rows,tail) := by
      simpa only [splitPackets,Iter.small,decide_eq_false (Nat.not_lt.mpr room),Bool.cond_false,Option.some.injEq] using ok
    exact ⟨by simpa only [eq] using segment_sizes sizes bits room,by simpa only [eq] using (segment_input sizes bits).symm⟩
  · rintro ⟨rfl,rfl⟩
    have room : (rows.map (tally ∘ List.length)).flatten.length ≤ (rows.flatten ++ tail).length := by
      simp [List.length_flatten,List.map_map,Function.comp_def]
    simp only [splitPackets,Iter.small,decide_eq_false (Nat.not_lt.mpr room),Bool.cond_false,segment_complete]

/-- A correctly sized packet represents a unique independent assignment to the child's
outgoing and incoming half-wires, including both occurrences of a loop. -/
theorem existsUnique_half {a g : ℕ} (X : State a g) (v : X.network.Site) (row : Bits.Word)
    (len : row.length = ∑ d : Bool, ∑ j, X.halfWidth v d j) :
    ∃! h : X.network.Half v, packed X v h = row := by
  let reader := RefreshHalfDecoder.reader X v
  have room : ¬ row.length < RefreshHalfDecoder.width X v := Nat.not_lt.mpr len.ge
  have ok : reader.read row ≠ none := fun hn => room ((RefreshHalfDecoder.none_iff X v row).mp hn)
  obtain ⟨⟨h,tail⟩,read⟩ := Option.ne_none_iff_exists'.mp ok
  have eqn := (RefreshHalfDecoder.read_iff X v row h tail).mp read
  have zero : tail.length = 0 := by
    have total := congrArg List.length eqn
    rw [List.length_append,packed_length,len] at total
    omega
  obtain rfl := List.length_eq_zero_iff.mp zero
  rw [List.append_nil] at eqn
  refine ⟨h,eqn.symm,?_⟩
  intro y hy
  have r := (RefreshHalfDecoder.read_iff X v row y []).mpr (by rw [hy,List.append_nil])
  exact (Prod.mk.inj (Option.some.inj (r.symm.trans read))).1

end OAI.Computability.MultitapeWeakETH.NativeGrid.ChildScan
