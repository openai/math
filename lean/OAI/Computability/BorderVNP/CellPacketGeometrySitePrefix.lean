import OAI.Computability.BorderVNP.CellPacketGeometrySiteOrder

/-! # Real record prefix after the public stable site sort

The final key is used only for padding. In particular the last actual site
keeps every record, even when that site denotes an inactive physical cell.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.SiteOrder

open scoped Classical

variable {A : Type*} {sites : ℕ}

/-- Physical sort key, reserving one site strictly beyond all real site names. -/
def rowKey (raw : List (Fin sites × A)) (i : ℕ) : ℕ :=
  if h : i < raw.length then raw[i].1.val else sites

private def placedSite : Option (Fin sites × A) → Fin (sites+1)
  | some z => z.1.castSucc
  | none => Fin.last sites

private theorem placed_key (raw : List (Fin sites × A)) (i : ℕ) :
    (placedSite raw[i]?).val = rowKey raw i := by
  by_cases h : i < raw.length
  · simp [rowKey,h,placedSite]
  · simp [rowKey,h,placedSite]

private theorem padded_list {X : Type*} (raw : List X) {M : ℕ} (fit : raw.length ≤ M) :
    List.ofFn (fun i : Fin M => raw[i.val]?) = raw.map some ++ List.replicate (M-raw.length) none := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi hj
    rw [List.getElem_ofFn]
    by_cases h : i < raw.length
    · simp [List.getElem_append_left (by simpa using h : i < (raw.map some).length),
        List.getElem?_eq_getElem h]
    · simp [List.getElem_append_right (by simpa using Nat.le_of_not_lt h : (raw.map some).length ≤ i),
        List.getElem?_eq_none (by omega : raw.length ≤ i)]

private theorem real_rows (t : Fin sites) (raw : List (Fin sites × A)) (pads : ℕ) :
    (((raw.map some ++ List.replicate pads none).filter (fun x => decide (placedSite x = t.castSucc))).map
      (fun x : Option (Fin sites × A) => x.map Prod.snd)) = (raw.filterMap (fun z => if z.1=t then some z.2 else none)).map some := by
  induction raw with
  | nil => simp [placedSite,Ne.symm (Fin.castSucc_ne_last t)]
  | cons z zs ih =>
    by_cases h : z.1 = t <;> simp_all [placedSite]

private theorem padding_rows (raw : List (Fin sites × A)) (pads : ℕ) :
    (((raw.map some ++ List.replicate pads none).filter (fun x => decide (placedSite x = Fin.last sites))).map
      (fun x : Option (Fin sites × A) => x.map Prod.snd)) = List.replicate pads none := by
  induction raw with
  | nil => simp [placedSite]
  | cons z zs ih =>
    have hz : placedSite (some z) ≠ Fin.last sites := Fin.castSucc_ne_last _
    simpa only [List.map_cons,List.cons_append,List.filter_cons,decide_eq_false hz,
      Bool.false_eq_true,↓reduceIte] using ih

private theorem take_indices {X : Type*} {M k : ℕ} (fit : k ≤ M) (f : Fin M → X) :
    (List.ofFn f).take k = List.ofFn (fun i : Fin k => f (Fin.castLE fit i)) := by
  apply List.ext_getElem
  · simp [fit]
  · intro i hi hj; simp

/-- The real output prefix of a full padded sorting network is the site-major
concatenation of the chronological per-site records. The theorem covers
empty lists, empty sites, and repeated words at the same site. -/
theorem sorted_prefix (raw : List (Fin sites × A)) {M : ℕ} (fit : raw.length ≤ M)
    (π : Equiv.Perm (Fin M)) (sorted : Monotone fun i => 2*rowKey raw (π i).val*M+(π i).val) :
    List.ofFn (fun j : Fin raw.length => raw[(π (Fin.castLE fit j)).val]?.map Prod.snd) =
      ((List.finRange sites).flatMap
        (fun t => raw.filterMap (fun z => if z.1=t then some z.2 else none))).map some := by
  let f := fun i : Fin M => raw[i.val]?
  let proj := fun x : Option (Fin sites × A) => x.map Prod.snd
  let g := fun t : Fin sites => raw.filterMap (fun z => if z.1=t then some z.2 else none)
  have hs : Monotone fun i => 2*(placedSite (f (π i))).val*M+(π i).val := by
    simpa only [f,placed_key] using sorted
  have full := congrArg (List.map proj) (sorted_payloads placedSite f π hs)
  have expanded : List.ofFn (fun i : Fin M => proj (f (π i))) =
      ((List.finRange sites).flatMap g).map some ++ List.replicate (M-raw.length) none := by
    simpa only [f,proj,List.map_ofFn,Function.comp_def,padded_list raw fit,
      List.finRange_succ_last,List.flatMap_append,List.flatMap_map,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.map_append,List.map_flatMap,real_rows,padding_rows,g] using full
  have hlen := congrArg List.length expanded
  simp only [List.length_ofFn,List.length_append,List.length_replicate] at hlen
  have hsize : (((List.finRange sites).flatMap g).map some).length = raw.length := by omega
  rw [← take_indices fit (fun i : Fin M => proj (f (π i))),expanded]
  change (((List.finRange sites).flatMap g).map some ++ _).take raw.length = _
  rw [← hsize,List.take_append_of_le_length (le_refl _),List.take_length]

/-- Exactly the original number of real payloads is emitted by the stable sort. -/
theorem sorted_prefix_length (raw : List (Fin sites × A)) {M : ℕ} (fit : raw.length ≤ M)
    (π : Equiv.Perm (Fin M)) (sorted : Monotone fun i => 2*rowKey raw (π i).val*M+(π i).val) :
    ((List.finRange sites).flatMap
      (fun t => raw.filterMap (fun z => if z.1=t then some z.2 else none))).length = raw.length := by
  have eq := congrArg List.length (sorted_prefix raw fit π sorted)
  simpa only [List.length_ofFn,List.length_map] using eq.symm

/-- The row at every real output slot names an actual input row. Its payload
is precisely the word fetched at this ordinal of the site-major stream. -/
theorem sorted_prefix_get (raw : List (Fin sites × A)) {M : ℕ} (fit : raw.length ≤ M)
    (π : Equiv.Perm (Fin M)) (sorted : Monotone fun i => 2*rowKey raw (π i).val*M+(π i).val)
    (j : Fin raw.length) :
    let out := (List.finRange sites).flatMap (fun t => raw.filterMap (fun z => if z.1=t then some z.2 else none))
    ∃ h : (π (Fin.castLE fit j)).val < raw.length,
      out[j.val]? = some (raw[(π (Fin.castLE fit j)).val]'h).2 := by
  let out := (List.finRange sites).flatMap (fun t => raw.filterMap (fun z => if z.1=t then some z.2 else none))
  have ho : j.val < out.length := (sorted_prefix_length raw fit π sorted).symm ▸ j.isLt
  let read := fun i : Fin raw.length => raw[(π (Fin.castLE fit i)).val]?.map Prod.snd
  have eq : List.ofFn read = out.map some := sorted_prefix raw fit π sorted
  have hget := congrArg (fun l : List (Option A) => l[j.val]?) eq
  have hj : j.val < (List.ofFn read).length := by simp
  have hmap : j.val < (out.map some).length := by simpa using ho
  rw [List.getElem?_eq_getElem hj,List.getElem?_eq_getElem hmap,List.getElem_ofFn,List.getElem_map] at hget
  have hval : raw[(π (Fin.castLE fit j)).val]?.map Prod.snd = some out[j.val] :=
    Option.some.inj hget
  have real : (π (Fin.castLE fit j)).val < raw.length := by
    by_contra! h
    rw [List.getElem?_eq_none h] at hval
    contradiction
  refine ⟨real,?_⟩
  rw [List.getElem?_eq_getElem real] at hval
  exact (List.getElem?_eq_getElem ho).trans hval.symm

end CellPacketGeometry.SiteOrder

end BorderVNP
end Computability
end OAI
