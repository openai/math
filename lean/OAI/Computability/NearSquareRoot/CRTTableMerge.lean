import OAI.Computability.NearSquareRoot.CRTTableLookup
import OAI.Computability.NearSquareRoot.CRTTableObserved
import OAI.Computability.NearSquareRoot.CRTTableInvalid
import OAI.Computability.NearSquareRoot.CRTTableTags
import OAI.Computability.IntegerMultiplication.Partial

/-! # Identifying generated tables with a CRT merge

On an occupied control address the data passed to the table generator are
the MSF coordinate fields after the two child permutations. This theorem
identifies the entries of its actual output lists with the corresponding
rotation in the full padded CRT machine model.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

open IntegerMultiplication IntegerMultiplication.Code

private def magnitude {m : ℕ} {E : Type} (v : ZMod m ⊕ E) : ℕ :=
  v.elim ZMod.val (fun _ => 0)

private theorem magnitude_lt {m : ℕ} [NeZero m] {E : Type} (v : ZMod m ⊕ E) :
    magnitude v < m := by
  cases v with
  | inl z => exact ZMod.val_lt _
  | inr _ => exact Nat.pos_of_ne_zero (NeZero.ne _)

variable {d : ℕ} (a : Fin d → ℕ) {E : Fin d → Type}

private def axisDescriptor (w : Fin d → ℕ) (j : Fin d) : Descriptor :=
  (tally (w j), tally (a j))

/-- Fixed-width, most-significant-first control field for a valid residue.
The value on the unused summand is irrelevant under the validity hypothesis. -/
private def field (w : Fin d → ℕ) (y : CRT.Address a E) (j : Fin d) :
    ControlAxis × List Bool :=
  (axisDescriptor a w j, (Bits.phrase (w j) (magnitude (y j))).reverse)

private theorem field_value [∀ j, NeZero (a j)] (w : Fin d → ℕ)
    (hw : ∀ j, a j ≤ 2^w j) (y : CRT.Address a E) (j : Fin d) :
    bitValue (field a w y j).2 = magnitude (y j) := by
  simp only [field, endianness, List.reverse_reverse]
  exact Bits.value_phrase ((magnitude_lt (y j)).trans_le (hw j))

/-- The queried bit string concatenates the current left-child coordinate
fields in descending axis order. -/
def mergeQuery (w : Fin d → ℕ) (js rs : List (Fin d)) (y : CRT.Address a E)
    (inverse : Bool) : NodeQuery :=
  (inverse, js.map (axisDescriptor a w), rs.map (axisDescriptor a w),
    ((js.map (field a w y)).reverse.map Prod.snd).flatten)

private theorem contribution_mergeOffset [∀ j, NeZero (a j)]
    (hcop : Pairwise (fun i j => (a i).Coprime (a j))) (base : ℕ)
    (js rs : List (Fin d)) (hpos : ∀ (u : ℕ) (hu : u < (js ++ rs).length),
      (js ++ rs)[u].val = base + u)
    (p : CRT.BlockPerm a E js.toFinset) (q : CRT.BlockPerm a E rs.toFinset)
    (hd : Disjoint js.toFinset rs.toFinset) (x : CRT.Address a E)
    (t : ∀ j, ZMod (a j)) (hx : ∀ j ∈ js.toFinset, x j = Sum.inl (t j))
    (i : Fin rs.length) :
    (contribution (js.map (fun j => tally (t j).val)) ((js ++ rs).map (fun j => tally (a j)))
      (js.length+i.val) js.length : ZMod (a rs[i.val])) =
      CRT.mergeOffset p ((p.parallel q hd).perm x) rs[i.val] := by
  let u : Fin (js ++ rs).length := ⟨js.length+i.val, by simp⟩
  let c := contribution (js.map (fun j => tally (t j).val))
    ((js ++ rs).map (fun j => tally (a j))) (js.length+i.val) js.length
  let claim (v : Fin d) := (c : ZMod (a v)) = CRT.weight a v * (CRT.partialRank a js.toFinset t : ZMod (a v))
  have hc : claim ((js ++ rs)[u.val]) := by
    have h := contribution_eq_partialRank a hcop base js rs hpos t u js.length le_rfl
      (by dsimp [u]; omega) (Nat.pos_of_ne_zero (NeZero.ne _))
    simpa only [List.take_length] using h
  have index : (js ++ rs)[u.val] = rs[i.val] := by simp [u, List.getElem_append_right]
  rw [CRT.mergeOffset_eq p q hd x t hx]
  change claim rs[i.val]
  rwa [index] at hc

/-- The natural coordinate stored at each occupied table address is precisely
the abstract child-merge rotation (or its inverse). Every padding address is
fixed. Only the *left* original child is required to be occupied.

The width inequalities describe a half-full axis. The upper inequality
follows from `axis_half_full` in every valid box. -/
theorem nodeTables_merge [∀ j, NeZero (a j)] (w : Fin d → ℕ)
    (hwidth : ∀ j, a j ≤ 2^w j) (hdense : ∀ j, 2^w j ≤ 2*a j)
    (hcop : Pairwise (fun i j => (a i).Coprime (a j))) (base : ℕ)
    (js rs : List (Fin d)) (hpos : ∀ (u : ℕ) (hu : u < (js ++ rs).length),
      (js ++ rs)[u].val = base + u)
    (p : CRT.BlockPerm a E js.toFinset) (hp : CRT.Computes p)
    (q : CRT.BlockPerm a E rs.toFinset) (hd : Disjoint js.toFinset rs.toFinset)
    (x : CRT.Address a E) (t : ∀ j, ZMod (a j))
    (hx : ∀ j ∈ js.toFinset, x j = Sum.inl (t j)) (inv : Bool) :
    let y := (p.parallel q hd).perm x
    let tables := nodeTables (mergeQuery a w js rs y inv)
    tables.length = rs.length ∧ ∀ i : Fin rs.length,
      let g := rs[i.val]
      let tab := tables[i.val]?.getD []
      let offset := CRT.mergeOffset p y g
      tab.length = 2^(w g) ∧ ∀ j : Fin (2^(w g)),
        (tab[j.val]?.getD []).length =
          if j.val < a g then ((j.val : ZMod (a g)) + (bif inv then -offset else offset)).val
          else j.val := by
  let y := (p.parallel q hd).perm x
  let fs := js.map (field a w y)
  let targets := rs.map (axisDescriptor a w)
  let xs := js.map (fun j => tally (t j).val)
  have view : CRT.Agrees js.toFinset y (p.perm x) := by
    intro j hj
    exact q.outside _ _ (fun hr => Finset.disjoint_left.mp hd hj hr)
  have wfs : ∀ f ∈ fs, f.2.length = f.1.1.length := by
    intro f hf
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hf
    simp [field, axisDescriptor, Bits.phrase_length]
  have vfs : ∀ f ∈ fs, bitValue f.2 < f.1.2.length := by
    intro f hf
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hf
    rw [field_value a w hwidth]
    simpa only [field, axisDescriptor, tally_length] using magnitude_lt (y j)
  have fstfs : fs.map Prod.fst = js.map (axisDescriptor a w) := by
    simp [fs, field, List.map_map]
  have vmap : fs.map (fun f => tally (bitValue f.2)) =
      js.map (fun j => tally (magnitude (y j))) := by
    simp only [fs, List.map_map, Function.comp_def, field_value a w hwidth]
  have obs : Observed (fs.map Prod.fst) targets (fs.map (fun f => tally (bitValue f.2))) xs := by
    rw [fstfs, vmap]
    exact observed_of_computes a hcop base js rs hpos (fun j => tally (w j)) p hp x y t hx view
  have hm : ∀ i : Fin targets.length, 0 < targets[i.val].2.length := by
    intro i
    simp only [targets, List.getElem_map, axisDescriptor, tally_length]
    exact Nat.pos_of_ne_zero (NeZero.ne _)
  have packet : fieldQuery inv fs targets = mergeQuery a w js rs y inv := by
    simp only [fieldQuery, mergeQuery, fstfs, targets, fs]
  obtain ⟨count, entries⟩ := nodeTables_valid inv fs targets xs wfs vfs obs hm
  rw [packet] at count entries
  refine ⟨by simpa [targets] using count, ?_⟩
  intro i
  have e := entries (⟨i.val, by simp [targets]⟩ : Fin targets.length)
  have hpad : (padded (axisDescriptor a w rs[i.val])).length = 2^w rs[i.val] := by
    simp [padded, axisDescriptor, min_eq_left (hdense _)]
  have haxes : localAxes (fs.map Prod.fst) targets = (js ++ rs).map (fun j => tally (a j)) := by
    change ((fs.map Prod.fst ++ targets).map Prod.snd) = _
    rw [fstfs]
    simp [targets, List.map_append, List.map_map, Function.comp_def, axisDescriptor]
  have hlen : fs.length = js.length := by simp [fs]
  have ep : (padded (targets[i.val]'(by simp [targets]))).length = 2^w rs[i.val] := by
    rw [show (targets[i.val]'(by simp [targets])) = axisDescriptor a w rs[i.val] from List.getElem_map _]
    exact hpad
  refine ⟨e.1.trans ep, ?_⟩
  intro j
  have v := e.2 (⟨j.val, by rw [ep]; exact j.isLt⟩ : Fin (padded (targets[i.val]'(by simp [targets]))).length)
  have hδ := contribution_mergeOffset a hcop base js rs hpos p q hd x t hx i
  change (contribution xs _ _ _ : ZMod _) = CRT.mergeOffset p y _ at hδ
  let entry (m c : ℕ) := if j.val < m then
    ((j.val : ZMod m) + (bif inv then -(c : ZMod m) else c)).val else j.val
  change _ = entry (targets[i.val]'(by simp [targets])).2.length
    (contribution xs (localAxes (fs.map Prod.fst) targets) (fs.length + i.val) fs.length) at v
  have hm' : (targets[i.val]'(by simp [targets])).2.length = a rs[i.val] := by
    simp [targets, axisDescriptor]
  rw [hm', hlen, haxes] at v
  dsimp only [entry] at v
  rw [hδ] at v
  exact v

/-- Interpret a padded coordinate in the binary address. Values beyond the
modulus are encoded immediately after the valid residues. -/
def coordinate {m L : ℕ} {V : Type} (pad : V → Fin (L-m)) : ZMod m ⊕ V → ℕ
  | .inl v => v.val
  | .inr v => m + (pad v).val

private theorem coordinate_lt {m L : ℕ} [NeZero m] {V : Type} (pad : V → Fin (L-m))
    (h : m ≤ L) (v : ZMod m ⊕ V) : coordinate pad v < L := by
  cases v with
  | inl v => exact (ZMod.val_lt v).trans_le h
  | inr v =>
    change m + (pad v).val < L
    have := (pad v).isLt
    omega

private def fullField (w : Fin d → ℕ) (pad : ∀ j, E j → Fin (2^w j - a j))
    (y : CRT.Address a E) (j : Fin d) : ControlAxis × List Bool :=
  (axisDescriptor a w j, (Bits.phrase (w j) (coordinate (pad j) (y j))).reverse)

/-- Query string with both occupied and padding coordinates represented by
their actual positions in the padded array. -/
def paddedMergeQuery (w : Fin d → ℕ) (pad : ∀ j, E j → Fin (2^w j - a j))
    (js rs : List (Fin d)) (y : CRT.Address a E) (inverse : Bool) : NodeQuery :=
  fieldQuery inverse (js.map (fullField a w pad y)) (rs.map (axisDescriptor a w))

/-- The compiled tables agree with each arithmetic join at every address,
including invalid controls and padded target coordinates. The two tag
invariants are provided by `CRT.build_preservesTags` for the balanced tree. -/
theorem nodeTables_paddedMerge [∀ j, NeZero (a j)] (w : Fin d → ℕ)
    (pad : ∀ j, E j → Fin (2^w j - a j))
    (hwidth : ∀ j, a j ≤ 2^w j) (hdense : ∀ j, 2^w j ≤ 2*a j)
    (hcop : Pairwise (fun i j => (a i).Coprime (a j))) (base : ℕ)
    (js rs : List (Fin d)) (hpos : ∀ (u : ℕ) (hu : u < (js ++ rs).length),
      (js ++ rs)[u].val = base + u)
    (p : CRT.BlockPerm a E js.toFinset) (hp : CRT.Computes p) (tp : CRT.PreservesTags p)
    (q : CRT.BlockPerm a E rs.toFinset) (tq : CRT.PreservesTags q)
    (hd : Disjoint js.toFinset rs.toFinset) (y : CRT.Address a E) (inv : Bool) :
    let tables := nodeTables (paddedMergeQuery a w pad js rs y inv)
    tables.length = rs.length ∧ ∀ i : Fin rs.length,
      let g := rs[i.val]
      let tab := tables[i.val]?.getD []
      let offset := CRT.mergeOffset p y g
      tab.length = 2^(w g) ∧ ∀ j : Fin (2^(w g)),
        (tab[j.val]?.getD []).length =
          if j.val < a g then ((j.val : ZMod (a g)) + (bif inv then -offset else offset)).val
          else j.val := by
  classical
  by_cases valid : ∀ j ∈ js.toFinset, (y j).isLeft = true
  · let x := (p.parallel q hd).perm.symm y
    let t (j : Fin d) := (x j).elim id (fun _ => 0)
    have hx : ∀ j ∈ js.toFinset, x j = Sum.inl (t j) := by
      intro j hj
      have htag : (x j).isLeft = true := ((tp.parallel tq hd).inverse y j).trans (valid j hj)
      cases h : x j with
      | inl v => simp [t, h]
      | inr v => simp [h] at htag
    have fields : js.map (fullField a w pad y) = js.map (field a w y) := by
      apply List.map_congr_left
      intro j hj
      have htag := valid j (by simpa using hj)
      cases h : y j with
      | inl v => simp [fullField, field, coordinate, magnitude, h]
      | inr v => simp [h] at htag
    have packet : paddedMergeQuery a w pad js rs y inv = mergeQuery a w js rs y inv := by
      rw [paddedMergeQuery, fields]
      simp [fieldQuery, mergeQuery, field, List.map_map, Function.comp_def]
    rw [packet]
    have cert := nodeTables_merge a w hwidth hdense hcop base js rs hpos p hp q hd x t hx inv
    simpa only [x, Equiv.apply_symm_apply] using cert
  · have bad : ∃ j ∈ js.toFinset, (y j).isLeft = false := by
      push Not at valid
      obtain ⟨j,hj,hb⟩ := valid
      exact ⟨j,hj,Bool.eq_false_iff.mpr hb⟩
    let fs := js.map (fullField a w pad y)
    let targets := rs.map (axisDescriptor a w)
    have hwidths : ∀ f ∈ fs, f.2.length = f.1.1.length := by
      intro f hf
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hf
      simp [fullField, axisDescriptor, Bits.phrase_length]
    have invalid : ∃ f ∈ fs, f.1.2.length ≤ bitValue f.2 := by
      obtain ⟨j,hj,htag⟩ := bad
      refine ⟨_, List.mem_map_of_mem (f := fullField a w pad y) (by simpa using hj), ?_⟩
      simp only [fullField, axisDescriptor, tally_length, endianness, List.reverse_reverse,
        Bits.value_phrase (coordinate_lt (pad j) (hwidth j) (y j))]
      cases h : y j with
      | inl v => simp [h] at htag
      | inr v => exact Nat.le_add_right _ _
    have cert := nodeTables_invalid fs targets inv hwidths invalid
    change nodeTables (paddedMergeQuery a w pad js rs y inv) = _ at cert
    dsimp only
    rw [cert]
    refine ⟨by simp [targets], ?_⟩
    intro i
    let g := rs[i.val]
    have ht : (padded (axisDescriptor a w g)).length = 2^w g := by
      simp [padded, axisDescriptor, min_eq_left (hdense _)]
    have table : ((targets.map (fun d => Iter.lineup (padded d)))[i.val]?.getD []) =
        Iter.lineup (padded (axisDescriptor a w g)) := by
      simp [targets, g, i.isLt]
    rw [table]
    refine ⟨by simpa [Iter.lineup] using ht, ?_⟩
    intro j
    have hj : j.val < (padded (axisDescriptor a w g)).length := by rw [ht]; exact j.isLt
    have actual : (((Iter.lineup (padded (axisDescriptor a w g)))[j.val]?.getD [])).length =
        j.val := by simp [Iter.lineup, hj]
    rw [actual, CRT.mergeOffset_zero_of_padding tp y bad]
    by_cases hv : j.val < a g
    · simp [g, hv, ZMod.val_natCast, Nat.mod_eq_of_lt hv]
    · simp [g, hv]

end CRTTable

end NearSquareRoot
end Computability
end OAI
