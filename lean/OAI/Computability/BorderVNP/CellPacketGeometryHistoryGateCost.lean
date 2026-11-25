import OAI.Computability.BorderVNP.CellPacketGeometryHistoryTemplate
import OAI.Computability.BorderVNP.CellPacketGeometryStoredCost
import OAI.Computability.BorderVNP.CellPacketGeometryVolume

/-! # Charging the complete chronological source and the final bindings

Anchor boxes, frozen rows, final binding rows, and reports are charged at their
actual static counts. Private factor bytes do not enter the gate volume.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History

open CellSparse Packet Packing.Inherited FrozenTape Packing.BankPacket Packing.Word LiveWords SiteWords

variable {a C cap : ℕ} {R B U V E Orig : Type}

private theorem roster_sum (S : Schema R B) (L : Schema U V) (f : Slot a R U → ℕ) :
    (∑ i : Fin (roster a S L).length, f ((roster a S L).get i)) =
      (∑ j : Fin a, f (.inl j)) + f (.inr none) +
      (S.rows.map fun r => f (.inr (some (.inl r)))).sum +
      (L.rows.map fun u => f (.inr (some (.inr u)))).sum := by
  rw [←List.sum_ofFn]
  change (List.ofFn (fun i : Fin (roster a S L).length => f (roster a S L)[i.val])).sum = _
  rw [List.ofFn_getElem_eq_map]
  simp [roster,List.map_map,Function.comp_def,←List.ofFn_eq_map,List.sum_ofFn,Nat.add_assoc]

private theorem format_nodes (S : Schema R B) (L : Schema U V) (sh : ∀ r, (S.tags r).length≤cap)
    (lh : ∀ u, (L.tags u).length≤cap) (v : Slot a R U) :
    ∀ e ∈ tape (format S L sh lh v), e.nodes ≤ 3 := by
  rcases v with j | _ | r | u
  · simp [format,tape,WidthExpr.nodes]
  · simp [format,tape,WidthExpr.nodes]
  · intro e he
    simp only [format,tape,List.mem_cons,List.flatMap_singleton] at he
    rcases he with rfl | he
    · exact (by decide : 1 ≤ 3)
    · exact Stored.placed_fromTags_nodes _ _ _ _ _ he
  · intro e he
    simp only [format,tape,List.mem_cons,List.flatMap_singleton] at he
    rcases he with rfl | he
    · exact (by decide : 1 ≤ 3)
    · exact (Stored.fromTags_nodes _ _ _ he).le.trans (by decide)

/-- Number of immutable tag words of all declared row pieces, in chronological
order. Inactive rows are included because they still occupy source columns. -/
def tagWords (S : Schema R B) := (S.rows.map fun r => (S.tags r).length).sum

private theorem sum_bound {A : Type} (rows : List A) (f g : A → ℕ) (bound : ∀ r, f r ≤ 9*(g r+1)) :
    (rows.map f).sum ≤ 9*((rows.map g).sum+rows.length) := by
  induction rows with
  | nil => simp
  | cons r rows ih => simp only [List.map_cons,List.sum_cons,List.length_cons]; have := bound r; omega

variable (S : Schema R B) (L : Schema U V) (boxes : Fin a → List (Source.Box Orig))
variable (sh : ∀ r, (S.tags r).length≤cap) (lh : ∀ u, (L.tags u).length≤cap)
variable (priv : Fin (C+1) → E) (rep : Fin (C+1) → List (List E))

local notation3 "T" => template S L boxes sh lh priv rep

/-- Number of body scalar columns in the complete history/final roster. A
malformed reserved slot uses at most nine words per input tag plus one tag. -/
theorem recordSlots_bound :
    (T).recordSlots.length ≤ 9*(tagWords S + S.rows.length + tagWords L + L.rows.length) := by
  let cost := fun v : Slot a R U => (tape (format S L sh lh v)).length-1
  have costS (r : R) : cost (.inr (some (.inl r))) ≤ 9*((S.tags r).length+1) := by
    simpa [cost,format,tape,Stored.placed_words_length] using Stored.fromTags_length_le (S.tags r) (pin _ (sh r))
  have costL (u : U) : cost (.inr (some (.inr u))) ≤ 9*((L.tags u).length+1) := by
    simpa [cost,format,tape] using Stored.fromTags_length_le (L.tags u) (pin _ (lh u))
  have hist := sum_bound S.rows (fun r => cost (.inr (some (.inl r)))) _ costS
  have final := sum_bound L.rows (fun u => cost (.inr (some (.inr u)))) _ costL
  have zero (j : Fin a) : cost (.inl j)=0 := rfl
  rw [Template.recordSlots_sum]
  change (∑ i, cost ((roster a S L).get i)) ≤ _
  rw [roster_sum S L cost]
  simp only [zero,Finset.sum_const_zero,show cost (.inr none)=0 from rfl,Nat.zero_add]
  unfold tagWords
  omega

/-- Public source volume in physical input units: original site anchors, both
chronological row tapes, cell report words, and the one-copy box directories. -/
def sourceVolume [Fintype E] :=
  1+a+C+S.rows.length+tagWords S+L.rows.length+tagWords L+Fintype.card E+
    (∑ i, (boxes i).length)+(∑ i, (boxWords (boxes i)).length)+
      ∑ c, (1+((rep c).map fun row => 1+row.length).sum)

private theorem box_sum (m : List (Source.Box Orig) → ℕ) (zero : m []=0) :
    (∑ i, m ((T).boxes i)) = ∑ j, m (boxes j) := by
  let f : Slot a R U → ℕ := fun v => m (v.elim boxes (fun _ => []))
  change (∑ i, f ((roster a S L).get i)) = _
  rw [roster_sum S L f]
  simp [f,zero]

/-- The actual sparse public volume of the template is linear in the source
records, independently of multiplicity values and original opaque factor tables. -/
theorem publicVolume_le_source [Fintype E] :
    (T).publicVolume ≤ 64 * sourceVolume S L boxes rep := by
  let base := fun _ : Fin (roster a S L).length => Fin.last C
  have nodes (z : (T).RowPin) : (tape ((T).format z.1))[z.2].nodes ≤ 3 :=
    format_nodes S L sh lh ((roster a S L).get z.1) _ (List.getElem_mem _)
  have bound := (T).publicVolume_le base 3 nodes
  have boxn := box_sum S L boxes sh lh priv rep List.length rfl
  have boxw := box_sum S L boxes sh lh priv rep (fun xs => (boxWords xs).length) rfl
  rw [boxn,boxw] at bound
  have r := recordSlots_bound S L boxes sh lh priv rep
  have slots : (roster a S L).length = a+1+S.rows.length+L.rows.length := by simp [roster]; omega
  have report (c : Fin (C+1)) : (T).reportWordCount c = 1+((rep c).map fun row => 1+row.length).sum := rfl
  simp only [report] at bound
  unfold sourceVolume
  omega

private theorem public_box_cap (xs : List (Source.Box Orig)) (cap : ℕ)
    (h : ∀ fs, Sum.inl fs ∈ xs → (fieldList factor fs).length ≤ cap) :
    (boxWords xs).length ≤ cap*(xs.filterMap Sum.getLeft?).length := by
  induction xs with
  | nil => simp [boxWords]
  | cons x xs ih =>
    have rest := ih (fun fs hm => h fs (List.mem_cons_of_mem _ hm))
    cases x with
    | inr a =>
      rw [show (Sum.inr a :: xs).filterMap Sum.getLeft? = xs.filterMap Sum.getLeft? from rfl]
      simpa only [boxWords,List.map_cons,List.flatMap_cons,Source.boxPart,Source.Part.publicBuffer,
        List.nil_append] using rest
    | inl fs =>
      have width := h fs List.mem_cons_self
      simpa only [boxWords,List.map_cons,List.flatMap_cons,Source.boxPart,Source.Part.publicBuffer,
        List.length_append,List.filterMap_cons,Sum.getLeft?,List.length_cons,Nat.mul_succ,Nat.add_comm _ cap] using
        Nat.add_le_add width rest

/-- When public one-copy boxes have at most the indicated serialization width,
their volume is bounded by that width times the count of public boxes. Original
opaque sites are absent from this count regardless of their delivered body size. -/
theorem publicBoxes_le (boxes : Fin a → List (Source.Box Orig)) (width : ℕ)
    (h : ∀ j fs, Sum.inl fs ∈ boxes j → (fieldList factor fs).length ≤ width) :
    (∑ j, (boxWords (boxes j)).length) ≤ width*(∑ j, ((boxes j).filterMap Sum.getLeft?).length) := by
  simpa only [Finset.mul_sum] using
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => public_box_cap (boxes j) width (h j))

variable {σ : Type} [Fintype σ] [Fintype E] {k w q : ℕ}

/-- Gate count of the actual ordered assembler with its canonical least padded
sort widths, charged against the physical chronological history volume. -/
theorem frame_size_le_source (up : VPVNP.VerifierNetwork.Frame σ (Base (roster a S L).length k w E (Field cap)))
    (anchors : VPVNP.VerifierNetwork.Frame σ (Fin (roster a S L).length × Fin q))
    (base : Fin (roster a S L).length → Fin (C+1)) (pointer : Orig → (T).Fields)
    (pad : (roster a S L).length < 2^q) (dest H W : ℕ)
    (wk : k≤W) (ww : w≤W) (wq : q≤W) (wp : (T).publicDepth≤W) (wd : (T).chunkDepth≤W)
    (wb : (T).recordDepth≤W) (wh : Nat.clog 2 ((roster a S L).length+(C+1)) ≤ W) :
    ((T).orderedFrame up anchors base pointer pad dest H).size ≤
      up.size+anchors.size+16000000*sourceVolume S L boxes rep*(W+1)^3 := by
  have h := (T).orderedFrame_cubic up anchors base pointer pad dest H W wk ww wq wp wd wb wh
  have cost := Nat.mul_le_mul_right ((W+1)^3) (Nat.mul_le_mul_left 250000 (publicVolume_le_source S L boxes sh lh priv rep))
  rw [← Nat.mul_assoc] at cost
  exact h.trans (Nat.add_le_add_left cost _)

/-- The physical compiled gate table has the same chronological charge, with
the factor of four of the Boolean frame serializer included. -/
theorem table_size_le_source {u : ℕ}
    (up : VPVNP.VerifierNetwork.Frame σ (Base (roster a S L).length k w E (Field cap)))
    (anchors : VPVNP.VerifierNetwork.Frame σ (Fin (roster a S L).length × Fin q))
    (base : Fin (roster a S L).length → Fin (C+1)) (pointer : Orig → (T).Fields)
    (pad : (roster a S L).length < 2^q) (dest H : ℕ) (pins : σ → (Fin u ⊕ Fin 0) ⊕ Bool) (W : ℕ)
    (wk : k≤W) (ww : w≤W) (wq : q≤W) (wp : (T).publicDepth≤W) (wd : (T).chunkDepth≤W)
    (wb : (T).recordDepth≤W) (wh : Nat.clog 2 ((roster a S L).length+(C+1)) ≤ W) :
    ((T).orderedGeometry up anchors base pointer (T).sort_rooms.2.2 pad (T).chunkDepth (T).sort_rooms.1
      dest H pins).size ≤ 4*(up.size+anchors.size)+64000000*sourceVolume S L boxes rep*(W+1)^3 := by
  have h := (T).orderedGeometry_cubic up anchors base pointer pad dest H pins W wk ww wq wp wd wb wh
  have cost := Nat.mul_le_mul_right ((W+1)^3)
    (Nat.mul_le_mul_left 1000000 (publicVolume_le_source S L boxes sh lh priv rep))
  rw [← Nat.mul_assoc] at cost
  exact h.trans (Nat.add_le_add_left cost _)

end CellPacketGeometry.History

end BorderVNP
end Computability
end OAI
