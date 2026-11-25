import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarPatchRecordExtract
import OAI.LinearAlgebra.SpectralBooks.PortGraph.CompleteMapLabelsViews

/-! # Verification of the extracted patch records -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical

namespace PortGraph.PatchRecord

variable {V E A : Type*} [Fintype V] [Fintype E] [DecidableEq V]
  {n K : ℕ} (M : RootedMap V E) (old : Fin n ↪ V)
  (z : V → A) (hn : 0 < n) (hk : n ≤ K)

/-- The wire denoted by a nonfixed outgoing dart in the old record. -/
def originalEdge (e : (ofSlots M old z hn hk).shape.Wire) : E := (actual M old e.val).1

theorem wire_darts (e : (ofSlots M old z hn hk).shape.Wire) (b : Bool) :
    actual M old ((ofSlots M old z hn hk).shape.read (.inl (e,b))) =
      (originalEdge M old z hn hk e,b) := by
  have ht : actual M old e.val = (originalEdge M old z hn hk e,false) := Prod.ext rfl e.property.2
  cases b with
  | false => exact ht
  | true => exact (actual_partner M old e.property.1).trans (congrArg cross ht)

theorem wire_incidence (e : (ofSlots M old z hn hk).shape.Wire) (b : Bool) :
    M.graph.vertex (originalEdge M old z hn hk e) b =
      old ((ofSlots M old z hn hk).toPiece.graph.vertex e b) := by
  let s := (ofSlots M old z hn hk).shape
  exact ((congrArg (fun d : E × Bool => M.graph.vertex d.1 d.2)
    (wire_darts M old z hn hk e b)).symm.trans (actual_owner M old _)).trans
    (congrArg old (s.read_internal_owner e b))

/-- Every internal wire has one record endpoint pair. This includes parallel
wires and the two differently numbered ends of a loop. -/
theorem existsUnique_wire (e : E) (ht : ∃ i, old i = M.graph.tail e)
    (hh : ∃ i, old i = M.graph.head e) :
    ∃! w, originalEdge M old z hn hk w = e := by
  obtain ⟨p,hp⟩ := (actual_range M old (e,false)).mpr ht
  obtain ⟨q,hq⟩ := (actual_range M old (e,true)).mpr hh
  have hc : actual M old q = cross (actual M old p) := by rw [hp,hq]; rfl
  have he : partner M old p ≠ p := fun h => (partner_fixed_iff M old p).1 h ⟨q,hc⟩
  refine ⟨⟨p,he,congrArg Prod.snd hp⟩,congrArg Prod.fst hp,?_⟩
  intro w hw
  exact Subtype.ext (actual_injective M old ((wire_darts M old z hn hk w false).trans
    ((congrArg (fun t => (t,false)) hw).trans hp.symm)))

/-- Read-back from the internal pair table has exactly the original oriented
edge incidences. -/
theorem exists_wire_iff (i j : Fin n) :
    (∃ w, (ofSlots M old z hn hk).toPiece.graph.tail w = i ∧
      (ofSlots M old z hn hk).toPiece.graph.head w = j) ↔
    ∃ e, M.graph.tail e = old i ∧ M.graph.head e = old j := by
  constructor
  · rintro ⟨w,rfl,rfl⟩
    exact ⟨_, wire_incidence M old z hn hk w false, wire_incidence M old z hn hk w true⟩
  · rintro ⟨e,ht,hh⟩
    obtain ⟨w,hw,_⟩ := existsUnique_wire M old z hn hk e ⟨i,ht.symm⟩ ⟨j,hh.symm⟩
    refine ⟨w,old.injective ?_,old.injective ?_⟩
    · exact (wire_incidence M old z hn hk w false).symm.trans (hw ▸ ht)
    · exact (wire_incidence M old z hn hk w true).symm.trans (hw ▸ hh)

/-- The internal graph of the record is the induced graph of the patch,
with its vertices in certified name order. -/
def inducedIso (P : Finset V) (name : V ↪ ℕ) (hn : P.Nonempty) (hk : P.card ≤ K) :
    let R := extract M z P name hn hk
    PlanarPatch.underlying R.toPiece.graph.tail R.toPiece.graph.head ≃g
      (PlanarPatch.underlying M.graph.tail M.graph.head).induce (P : Set V) where
  toEquiv := slotOrder P name
  map_rel_iff' := by
    intro i j
    let f := slots P name
    let R := extract M z P name hn hk
    change (f i ≠ f j ∧ ∃ e, (M.graph.tail e = f i ∧ M.graph.head e = f j) ∨
      (M.graph.tail e = f j ∧ M.graph.head e = f i)) ↔
      i ≠ j ∧ ∃ w, (R.toPiece.graph.tail w = i ∧ R.toPiece.graph.head w = j) ∨
        (R.toPiece.graph.tail w = j ∧ R.toPiece.graph.head w = i)
    have hij := exists_wire_iff M f z (Finset.card_pos.mpr hn) hk i j
    have hji := exists_wire_iff M f z (Finset.card_pos.mpr hn) hk j i
    simp only [ne_eq, exists_or]
    exact Iff.and (not_congr f.injective.eq_iff) (hij.symm.or hji.symm)

theorem actual_slot (p : PatchDart (fun i => M.typeAt (old i))) :
    (M.slots _ ⟨actual M old p,rfl⟩).val = p.2.val := by
  let q := (M.num _).symm p.2
  have hslot {v w : V} (p : M.graph.Port v) (q : M.graph.Port w) (h : p.val = q.val) :
      (M.slots v p).val = (M.slots w q).val := by
    rcases p with ⟨p,rfl⟩
    rcases q with ⟨q,rfl⟩
    change p = q at h
    subst q
    rfl
  refine (hslot (⟨actual M old p,rfl⟩ : M.graph.Port _) q rfl).trans ?_
  change ((M.num _) ((M.num _).symm p.2)).val = p.2.val
  exact congrArg Fin.val ((M.num (old p.1)).apply_symm_apply p.2)

/-- An actual connected patch of a passing map, sorted by its certified
names and with one common identifier, passes every test inside its record. -/
theorem extract_valid {I : Type*} (T : MapLabelTests A) (pass : T.Pass M z)
    (P : Finset V) (hconn : PlanarPatch.Connected M.graph.tail M.graph.head P)
    (hn : P.Nonempty) (hk : P.card ≤ K) (readName : A → ℕ) (name : V ↪ ℕ)
    (hnames : ∀ v, readName (z v) = name v) (patch : A → I)
    (hpatch : ∀ v ∈ P, ∀ w ∈ P, patch (z v) = patch (z w)) :
    (extract M z P name hn hk).Valid readName patch T.vertex T.edge := by
  let f := slots P name
  let R := extract M z P name hn hk
  refine ⟨?_,?_,(inducedIso M z P name hn hk).connected_iff.mpr hconn,?_,?_,?_⟩
  · change StrictMono (fun i => readName (z (f i)))
    intro i j hij
    change readName (z (f i)) < readName (z (f j))
    rw [hnames (f i), hnames (f j)]
    exact slotOrder_strict P name hij
  · exact fun i j => hpatch _ (slotOrder P name i).property _ (slotOrder P name j).property
  · intro i j hi hj
    apply f.injective
    exact (of_decide_eq_true hi).trans (of_decide_eq_true hj).symm
  · exact fun i => pass.1 _
  · intro w
    let e := originalEdge M f z (Finset.card_pos.mpr hn) hk w
    have hd (b : Bool) := wire_darts M f z (Finset.card_pos.mpr hn) hk w b
    have hv (b : Bool) := wire_incidence M f z (Finset.card_pos.mpr hn) hk w b
    have hs (b : Bool) : (M.slots _ ⟨(e,b),rfl⟩).val = (R.shape.read (.inl (w,b))).2.val :=
      (congrArg (fun d : E × Bool => (M.slots _ ⟨d,rfl⟩).val) (hd b).symm).trans (actual_slot M f _)
    have h := pass.2 e
    change T.edge _ _ (z (f (R.toPiece.graph.tail w))) (z (f (R.toPiece.graph.head w)))
    convert h using 1
    · exact Fin.ext (hs false).symm
    · exact Fin.ext (hs true).symm
    · exact congrArg z (hv false).symm
    · exact congrArg z (hv true).symm

end PortGraph.PatchRecord

end

end SpectralBooks
end LinearAlgebra
end OAI
