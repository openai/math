import OAI.Computability.BorderVNP.CubeScatterCrossKeys
import OAI.Computability.BorderVNP.CubeScatterSharedStreams

/-! # Every raw crossing word decodes to one valuation of its strict row

The order starts with native packet trials and their active cut lanes, then
continues with the two directed singleton scans. Each physical shared bit of
the row occurs once in this list.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open Physical Physical.Owned VPVNP.MotifBase

variable {n d blocks h K : ℕ}

/-- A physical shared bit on this strict row, either a cut lane in its selected
packet or one singleton bit from the unordered row. -/
abbrev RowCrossBit (b s : ℕ) (select : Packet n d blocks → Selector n K h) (i : Fin (n+1)) (sym : Symbols d) :=
  (Σ p : {p : Packet n d blocks // p.1.1 i = sym}, CrossLane (select p.val) i s) ⊕
    {z : SingleSlot n d blocks (h*b) // itemRow i (.inr z : Item n d blocks (h*b)) = Sym2.mk sym.val.1 sym.val.2}

private def rowPackets (blocks : ℕ) (i : Fin (n+1)) (sym : Symbols d) :=
  (packetVisits blocks i sym).attachWith (fun p => p.1.1 i = sym) (fun p hp => (mem_packetVisits blocks i sym p).mp hp)

private def rowSingles (blocks width : ℕ) (i : Fin (n+1)) (sym : Symbols d) :=
  (singleVisits blocks width i sym.val.1 sym.val.2 ++ singleVisits blocks width i sym.val.2 sym.val.1).attachWith
    (fun z => itemRow i (.inr z : Item n d blocks width) = Sym2.mk sym.val.1 sym.val.2)
    (fun z hz => (mem_singleVisits_append blocks width i sym.val.1 sym.val.2 z).mp hz)

/-- All row keys in their actual raw suffix order. -/
def rowCrossKeys (b s : ℕ) (select : Packet n d blocks → Selector n K h) (i : Fin (n+1)) (sym : Symbols d) :
    List (RowCrossBit b s select i sym) :=
  ((rowPackets blocks i sym).sigma (fun p => crossKeys b (select p.val) i s)).map Sum.inl ++
    (rowSingles blocks (h*b) i sym).map Sum.inr

/-- Every physical key of the strict row occurs in its emitted list. -/
theorem rowCrossKeys_mem (b s : ℕ) (select : Packet n d blocks → Selector n K h) (i : Fin (n+1)) (sym : Symbols d)
    (x : RowCrossBit b s select i sym) : x ∈ rowCrossKeys b s select i sym := by
  rw [rowCrossKeys,List.mem_append]
  cases x with
  | inl q =>
    obtain ⟨p,k⟩ := q
    apply Or.inl
    refine List.mem_map.mpr ⟨⟨p,k⟩,List.mem_sigma.mpr ⟨?_,crossKeys_mem b (select p.val) i k⟩,rfl⟩
    exact (List.mem_attachWith _ p).mpr ((mem_packetVisits blocks i sym p.val).mpr p.property)
  | inr z =>
    apply Or.inr (List.mem_map.mpr ⟨z,?_,rfl⟩)
    exact (List.mem_attachWith _ z).mpr ((mem_singleVisits_append blocks (h*b) i _ _ z.val).mpr z.property)

/-- No two raw suffix offsets refer to the same physical row bit. -/
theorem rowCrossKeys_nodup (b s : ℕ) (select : Packet n d blocks → Selector n K h) (i : Fin (n+1)) (sym : Symbols d) :
    (rowCrossKeys b s select i sym).Nodup := by
  have hp : (rowPackets blocks i sym).Nodup := List.Nodup.of_map Subtype.val
    (by simpa only [rowPackets,List.attachWith_map_subtype_val] using packetVisits_nodup blocks i sym)
  have hs : (rowSingles blocks (h*b) i sym).Nodup := List.Nodup.of_map Subtype.val
    (by simpa only [rowSingles,List.attachWith_map_subtype_val] using singleVisits_append_nodup blocks (h*b) i _ _ sym.property.ne)
  refine List.nodup_append.mpr ⟨(hp.sigma (fun _ => crossKeys_nodup ..)).map Sum.inl_injective,
    hs.map Sum.inr_injective,?_⟩
  intro x hx y hy
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp hx
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp hy
  exact Sum.inl_ne_inr

/-- The physical value of one shared row bit. -/
def rowCrossValue {b s : ℕ} {select : Packet n d blocks → Selector n K h} {i : Fin (n+1)} {sym : Symbols d}
    (z : (p : Packet n d blocks) → (e : Edge (n+1)) → Fin (payload (onEdge s) (select p).2 e) → Bool)
    (single : SingleSlot n d blocks (h*b) → Bool) : RowCrossBit b s select i sym → Bool
  | .inl ⟨p,k⟩ => z p.val (k.1,i) k.2
  | .inr x => single x.val

/-- Encoding the physical valuation gives exactly the native packet and
singleton crossing stream, bit for bit. -/
theorem commonCrossings_eq_keys (b : ℕ) (i : Fin (n+1)) (sym : Symbols d) (select : Packet n d blocks → Selector n K h)
    {s : ℕ} (z : (p : Packet n d blocks) → (e : Edge (n+1)) → Fin (payload (onEdge s) (select p).2 e) → Bool)
    (single : SingleSlot n d blocks (h*b) → Bool) :
    commonCrossings b i sym select z single = (rowCrossKeys b s select i sym).map (rowCrossValue z single) := by
  rw [rowCrossKeys,List.map_append,List.map_map,List.map_map,commonCrossings,List.append_assoc]
  congr 1
  · rw [List.sigma,List.map_flatMap]
    let f := fun p : Packet n d blocks => crossingStream b (select p) i (z p)
    change (packetVisits blocks i sym).flatMap f = _
    rw [← (List.attachWith_map_subtype_val (fun p hp => (mem_packetVisits blocks i sym p).mp hp)),List.flatMap_map]
    apply List.flatMap_congr
    intro p _
    simp only [f,List.map_map,crossingStream_eq_keys]
    rfl
  · change _ = (rowSingles blocks (h*b) i sym).map (fun x => single x.val)
    rw [rowSingles,List.attachWith_map_val,List.map_append]

/-- The number of raw key positions is exactly the declared row width at its grouping cut. -/
theorem rowCrossKeys_length (b s : ℕ) (select : Packet n d blocks → Selector n K h) (i : Fin (n+1)) (sym : Symbols d) :
    (rowCrossKeys b s select i sym).length = subtotals itemRow (crossCount b s select) i (Sym2.mk sym.val.1 sym.val.2) i := by
  have eq := commonCrossings_length (b := b) (s := s) i sym select (fun _ _ _ => false) (fun _ => false)
  rwa [commonCrossings_eq_keys,List.length_map] at eq

/-- Bijection between valuations on exactly the physical shared bits of this
row and arbitrary raw suffixes of the declared length. -/
noncomputable def rowCrossEquiv (b s : ℕ) (select : Packet n d blocks → Selector n K h) (i : Fin (n+1)) (sym : Symbols d) :
    (RowCrossBit b s select i sym → Bool) ≃
      {xs : List Bool // xs.length = subtotals itemRow (crossCount b s select) i (Sym2.mk sym.val.1 sym.val.2) i} := by
  classical
  let ks := rowCrossKeys b s select i sym
  let ord := List.Nodup.getEquivOfForallMemList ks (rowCrossKeys_nodup ..) (rowCrossKeys_mem b s select i sym)
  have len := rowCrossKeys_length b s select i sym
  refine ⟨fun f => ⟨ks.map f,by simpa only [List.length_map] using len⟩,
    fun xs q => xs.val[(ord.symm q).val]'(by rw [xs.property,← len]; exact (ord.symm q).isLt),?_,?_⟩
  · intro f
    funext q
    simp only [List.getElem_map]
    exact congrArg f (ord.apply_symm_apply q)
  · intro xs
    apply Subtype.ext
    apply List.ext_getElem (by simpa only [List.length_map] using len.trans xs.property.symm)
    intro j hj _
    have hlt : j < ks.length := by simpa using hj
    have eq : ord.symm (ks[j]) = ⟨j,hlt⟩ := ord.symm_apply_apply ⟨j,hlt⟩
    simp [eq]

/-- Encoding the row valuation recovers the native common suffix. -/
theorem rowCrossEquiv_encode (b s : ℕ) (select : Packet n d blocks → Selector n K h) (i : Fin (n+1)) (sym : Symbols d)
    (z : (p : Packet n d blocks) → (e : Edge (n+1)) → Fin (payload (onEdge s) (select p).2 e) → Bool)
    (single : SingleSlot n d blocks (h*b) → Bool) :
    ((rowCrossEquiv b s select i sym) (rowCrossValue z single)).val = commonCrossings b i sym select z single :=
  (commonCrossings_eq_keys ..).symm

/-- Supply digits recovered from a row valuation on its active cut. Other
positions receive a fixed zero extension. -/
def rowSupply {b s : ℕ} {select : Packet n d blocks → Selector n K h} {i : Fin (n+1)} {sym : Symbols d}
    (f : RowCrossBit b s select i sym → Bool) (p : Packet n d blocks) (e : Edge (n+1))
    (j : Fin (payload (onEdge s) (select p).2 e)) : Bool :=
  if hp : p.1.1 i = sym then
    if he : e.2 = i then f (.inl ⟨⟨p,hp⟩,e.1,⟨j.val,by simpa only [← he] using j.isLt⟩⟩) else false
  else false

/-- Singleton digits recovered from this unordered row. -/
def rowSingleton {b s : ℕ} {select : Packet n d blocks → Selector n K h} {i : Fin (n+1)} {sym : Symbols d}
    (f : RowCrossBit b s select i sym → Bool) (z : SingleSlot n d blocks (h*b)) : Bool :=
  if hz : itemRow i (.inr z : Item n d blocks (h*b)) = Sym2.mk sym.val.1 sym.val.2 then f (.inr ⟨z,hz⟩) else false

/-- The two concrete arrays recovered from the row valuation restrict to that
same valuation at every physical key. -/
theorem rowCrossValue_extend {b s : ℕ} {select : Packet n d blocks → Selector n K h} {i : Fin (n+1)} {sym : Symbols d}
    (f : RowCrossBit b s select i sym → Bool) : rowCrossValue (rowSupply f) (rowSingleton f) = f := by
  funext x
  cases x with
  | inl q => rcases q with ⟨p,v,j⟩; simp only [rowCrossValue,rowSupply,dite_eq_left p.property,dite_true]
  | inr z => simp only [rowCrossValue,rowSingleton,dite_eq_left z.property]

/-- Decoding a raw suffix and populating the physical arrays produces those
exact raw bits again in the native trial order. -/
theorem commonCrossings_decode (b s : ℕ) (select : Packet n d blocks → Selector n K h) (i : Fin (n+1)) (sym : Symbols d)
    (raw : {xs : List Bool // xs.length = subtotals itemRow (crossCount b s select) i (Sym2.mk sym.val.1 sym.val.2) i}) :
    let f := (rowCrossEquiv b s select i sym).symm raw
    commonCrossings b i sym select (rowSupply f) (rowSingleton f) = raw.val := by
  intro f
  rw [commonCrossings_eq_keys,rowCrossValue_extend]
  exact congrArg Subtype.val ((rowCrossEquiv b s select i sym).apply_symm_apply raw)

/-- Each arbitrary word of the declared length encodes precisely one assignment
on the physical shared row bits. -/
theorem existsUnique_rowCrossValue (b s : ℕ) (select : Packet n d blocks → Selector n K h) (i : Fin (n+1)) (sym : Symbols d)
    (raw : List Bool) (len : raw.length = subtotals itemRow (crossCount b s select) i (Sym2.mk sym.val.1 sym.val.2) i) :
    ∃! f : RowCrossBit b s select i sym → Bool, (rowCrossKeys b s select i sym).map f = raw := by
  let e := rowCrossEquiv b s select i sym
  let x : {xs : List Bool // xs.length = subtotals itemRow (crossCount b s select) i (Sym2.mk sym.val.1 sym.val.2) i} := ⟨raw,len⟩
  exact ⟨e.symm x,congrArg Subtype.val (e.apply_symm_apply x),fun f hf => e.injective ((Subtype.ext hf).trans (e.apply_symm_apply x).symm)⟩

end Cube.Scatter

end BorderVNP
end Computability
end OAI
