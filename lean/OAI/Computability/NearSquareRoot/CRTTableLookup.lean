import OAI.Computability.NearSquareRoot.CRTTableNode
import OAI.Computability.NearSquareRoot.CRTTableSubstitution

/-! # Entries of the forward and inverse CRT node tables

These identities read the operational lookup tables produced by the stack
program on packed control bits. A valid target is translated in its residue
ring, with the sign selected by the direction bit. Every padding position
keeps its own index.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

open IntegerMultiplication IntegerMultiplication.Code

private theorem cast_inverseOffset (s a : Tally) (ha : 0 < a.length) :
    ((inverseOffset (s,a)).length : ZMod a.length) = -(s.length : ZMod a.length) := by
  rw [inverseOffset_length, Nat.cast_sub (Nat.mod_lt _ ha).le,
    ZMod.natCast_self, zero_sub]
  exact congrArg Neg.neg ((ZMod.natCast_eq_natCast_iff ..).2 (Nat.mod_modEq ..))

private theorem chooseShift_cast (inv : Bool) (d : Descriptor) (s : Row)
    (hm : 0 < d.2.length) (delta : ZMod d.2.length)
    (hs : (s.2.1.length : ZMod d.2.length) = -delta) :
    ((chooseShift ((true,inv),d,s)).length : ZMod d.2.length) =
      bif inv then -delta else delta := by
  cases inv with
  | false =>
    change ((inverseOffset (s.2.1,d.2)).length : ZMod d.2.length) = delta
    rw [cast_inverseOffset _ _ hm, hs, neg_neg]
  | true => exact hs

/-- The real tape query consists of two descriptor lists and the MSF fields
in decreasing axis order. Here `true` requests the inverse translation. -/
abbrev fieldQuery (inv : Bool) (fs : List (ControlAxis × List Bool)) (r : List Descriptor) :
    NodeQuery := (inv, fs.map Prod.fst, r, (fs.reverse.map Prod.snd).flatten)

theorem nodeTables_valid (inv : Bool) (fs : List (ControlAxis × List Bool))
    (r : List Descriptor) (xs : List Tally)
    (width : ∀ f ∈ fs, f.2.length = f.1.1.length)
    (valid : ∀ f ∈ fs, bitValue f.2 < f.1.2.length)
    (h : Observed (fs.map Prod.fst) r (fs.map (fun f => tally (bitValue f.2))) xs)
    (hm : ∀ i : Fin r.length, 0 < r[i.val].2.length) :
    let tabs := nodeTables (fieldQuery inv fs r)
    tabs.length = r.length ∧ ∀ i : Fin r.length,
      let tab := tabs[i.val]?.getD []
      let m := r[i.val].2.length
      let delta := (contribution xs (localAxes (fs.map Prod.fst) r)
        (fs.length + i.val) fs.length : ZMod m)
      tab.length = (padded r[i.val]).length ∧
        ∀ j : Fin (padded r[i.val]).length, (tab[j.val]?.getD []).length =
          if j.val < m then ((j.val : ZMod m) + (bif inv then -delta else delta)).val
          else j.val := by
  let l := fs.map Prod.fst
  let v := fs.map (fun f => tally (bitValue f.2))
  let q := fieldQuery inv fs r
  let rs := residuals (ruler l, initializedRows l r v)
  have hp : prepareRows (initialPacket q) = (true, initializedRows l r v) :=
    prepareRows_valid fs r _ width valid
  have rows : targetRows q = rs := by unfold targetRows; rw [hp]
  obtain ⟨hlen,hr⟩ := substitution_targets l r v xs h hm
  change rs.length = r.length at hlen
  have htab : nodeTables q = (r.zip rs).map (fun p => emitAxis ((true,inv),p)) := by
    unfold nodeTables polyPush
    rw [rows, hp, zipFair_eq_zip _ _ _ _ hlen.symm]
  change (nodeTables q).length = _ ∧ _
  rw [htab]
  refine ⟨by simp [hlen], ?_⟩
  intro i
  have hi : i.val < rs.length := by simp [hlen]
  let d := r[i.val]
  let s := rs[i.val]
  let delta := (contribution xs (localAxes l r) (l.length + i.val) l.length : ZMod d.2.length)
  have hs : (s.2.1.length : ZMod d.2.length) = -delta := by
    have hentry := (hr i).2.2
    change (((rs[i.val]?.getD ([],[],[])).2.1.length : ℕ) : ZMod d.2.length) = _ at hentry
    simpa only [List.getElem?_eq_getElem hi, Option.getD_some] using hentry
  have hg : ((r.zip rs).map (fun p => emitAxis ((true,inv),p)))[i.val]?.getD [] =
      emitAxis ((true,inv),d,s) := by
    have ht : i.val < ((r.zip rs).map (fun p => emitAxis ((true,inv),p))).length := by simp [hlen]
    rw [List.getElem?_eq_getElem ht, Option.getD_some, List.getElem_map, List.getElem_zip]
  dsimp only
  rw [hg]
  refine ⟨rotation_length .., ?_⟩
  intro j
  let payload := ((true,inv),d,s)
  change ((emitAxis payload)[j.val]?.getD []).length = _
  have hj : j.val < (emitAxis payload).length := by
    change j.val < (rotation _).length
    rw [rotation_length]
    exact j.isLt
  rw [List.getElem?_eq_getElem hj, Option.getD_some, emitAxis_entry payload j]
  change (if j.val < d.2.length then
      (j.val + (chooseShift payload).length) % d.2.length else j.val) = _
  split_ifs with hjm
  · have eq := chooseShift_cast inv d s (hm i) delta hs
    rw [← ZMod.val_natCast, Nat.cast_add, eq]
    simp only [delta,l,List.length_map]
  · rfl

end CRTTable

end NearSquareRoot
end Computability
end OAI
