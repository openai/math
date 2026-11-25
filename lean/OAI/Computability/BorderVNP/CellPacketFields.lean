import OAI.Computability.BorderVNP.CellDirectoryWire
import OAI.Computability.BorderVNP.CellDirectoryCompact

/-! # Numerical fields actually sent in a sparse private cell packet

The typed input stores full source data, including histogram values and gadget identifiers
that can disappear when their Boolean tests are compiled.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet

/-- Raw factor data include every gadget ID in the stored local table. -/
def FactorFields (f : Factor) (U : ℕ) : Prop :=
  f.FieldBound U ∧ match f with
    | .gadget _ ids => ∀ id ∈ ids, id ≤ U
    | _ => True

/-- Raw records retain all advertised histogram integers and all four fields of every
box reference, even if the corresponding guard performs only a presence test. -/
def RecordFields (r : Record) (U : ℕ) : Prop :=
  r.GuardBound U ∧ match r with
    | .profile _ _ _ hist _ => ∀ count ∈ hist, count ≤ U
    | .box id base copies stride => id ≤ U ∧ base ≤ U ∧ copies ≤ U ∧ stride ≤ U
    | _ => True

/-- Bounds on scalar values and list prefixes of the *stored* directory. The box
conditions quantify over the entire private directory, including unreferenced tables. -/
structure RawFields (D : Directory) (p U : ℕ) : Prop where
  /-- Initial number of internal wire guesses. -/
  privateWires : p ≤ U
  /-- Length prefixes on the three top-level lists. -/
  lengths : D.boxes.length ≤ U ∧ D.records.length ≤ U ∧ D.reportedCounts.length ≤ U
  /-- Per-box factor count, key addresses, row IDs and original port fields. -/
  boxes : ∀ fs ∈ D.boxes, fs.length ≤ U ∧ ∀ f ∈ fs, FactorFields f U
  /-- Every original public record, including its count and range literals. -/
  records : ∀ r ∈ D.records, RecordFields r U
  /-- Width prefix and addresses of each reported binary word. -/
  reports : ∀ bs ∈ D.reportedCounts, bs.length ≤ U ∧ ∀ b ∈ bs, b ≤ U

private abbrev Small (U : ℕ) (xs : List ℕ) : Prop := ∀ x ∈ xs, x ≤ max 3 U

private theorem small_cons {x U : ℕ} {xs : List ℕ} (hx : x ≤ max 3 U) (h : Small U xs) :
    Small U (x::xs) := by
  intro y hy; rcases List.mem_cons.mp hy with rfl | hy
  · exact hx
  · exact h y hy

private theorem small_append {U : ℕ} {xs ys : List ℕ} (h : Small U xs) (g : Small U ys) :
    Small U (xs++ys) := by
  intro x hx; rcases List.mem_append.mp hx with hx|hx
  · exact h x hx
  · exact g x hx

private theorem small_list {α : Type} {U : ℕ} (f : α → List ℕ) (xs : List α)
    (hlen : xs.length ≤ U) (h : ∀ x ∈ xs, Small U (f x)) : Small U (fieldList f xs) := by
  apply small_cons (hlen.trans (le_max_right ..))
  intro i hi
  obtain ⟨x,hx,hi⟩ := List.mem_flatMap.mp hi
  exact h x hx i hi

private theorem small_vector {xs : List ℕ} {U : ℕ}
    (hl : xs.length ≤ U) (hs : Small U xs) : Small U (vector xs) :=
  small_cons (hl.trans (le_max_right ..)) hs

private theorem port_fields {p : Port} {U : ℕ} (hp : Profile.PortBound U p) : Small U (port p) := by
  rcases hp with ⟨hb,hc,hl⟩
  intro x hx
  simp only [port,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl <;> omega

private theorem factor_fields (f : Factor) {U : ℕ} (h : FactorFields f U) : Small U (factor f) := by
  cases f with
  | truth ws rs | sign ws rs =>
    obtain ⟨⟨⟨hw,hr⟩,hws⟩,_⟩ := h
    apply small_append (small_append (by intro x hx; simp at hx; omega)
      (small_vector hw (fun i hi => (hws i hi).trans (le_max_right ..))))
    apply small_vector (by simpa using hr)
    intro i hi
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hi
    cases b with
    | false => exact (show 0 ≤ max 3 U from Nat.zero_le _)
    | true => exact (show 1 ≤ max 3 U by omega)
  | gadget ws ids =>
    obtain ⟨⟨⟨hw,hr⟩,hws⟩,hids⟩ := h
    exact small_append (small_append (by intro x hx; simp at hx; omega)
      (small_vector hw (fun i hi => (hws i hi).trans (le_max_right ..))))
      (small_vector hr (fun i hi => (hids i hi).trans (le_max_right ..)))
  | unary w p =>
    obtain ⟨⟨_,hw,hp⟩,_⟩ := h
    apply small_append _ (port_fields hp)
    intro x hx; simp at hx; omega

private theorem record_fields (r : Record) {U : ℕ} (h : RecordFields r U) : Small U (record r) := by
  cases r with
  | zero c l p =>
    obtain ⟨⟨hc,hl,hp⟩,_⟩ := h
    exact small_append (by intro x hx; simp at hx; omega) (port_fields hp)
  | equal c l p q =>
    obtain ⟨⟨hc,hl,hp,hq⟩,_⟩ := h
    exact small_append (small_append (by intro x hx; simp at hx; omega) (port_fields hp)) (port_fields hq)
  | box id base c stride =>
    obtain ⟨_,hi,hb,hc,hs⟩ := h
    intro x hx; simp [record] at hx; omega
  | profile c p w hist rs =>
    obtain ⟨⟨hc,hw,hh,hr,hp,hrs⟩,hvalues⟩ := h
    apply small_append (small_append (small_append (small_append ?_ (port_fields hp)) ?_) ?_) ?_
    · intro x hx; simp at hx; omega
    · intro x hx; simp at hx; omega
    · exact small_vector hh (fun i hi => (hvalues i hi).trans (le_max_right ..))
    · apply small_list _ _ hr
      intro rt ht
      obtain ⟨ht,hl,ho,hc⟩ := hrs rt ht
      apply small_append (small_append ?_ (port_fields ho)) (port_fields hc)
      intro x hx; simp at hx; omega

/-- Every transported scalar is bounded by the numeric data scale or the fixed tag 3. -/
theorem words_bounded (D : Directory) (p : ℕ) {U : ℕ} (h : RawFields D p U) :
    ∀ x ∈ words D p, x ≤ max 3 U := by
  apply small_append (small_append (small_append ?_ ?_) ?_) ?_
  · intro x hx; simp at hx; have := h.privateWires; omega
  · apply small_list _ _ h.lengths.1
    intro fs hs
    obtain ⟨hl,hf⟩ := h.boxes fs hs
    exact small_list _ _ hl (fun f hmem => factor_fields f (hf f hmem))
  · exact small_list _ _ h.lengths.2.1 (fun r hr => record_fields r (h.records r hr))
  · apply small_list _ _ h.lengths.2.2
    intro bs hb
    obtain ⟨hl,ha⟩ := h.reports bs hb
    exact small_vector hl (fun x hx => (ha x hx).trans (le_max_right ..))

end CellSparse.Packet

end BorderVNP
end Computability
end OAI
