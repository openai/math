import OAI.Computability.BorderVNP.TransmissionReceivedFields

/-! # Assigning genuine data and shared bits to their scheduled unordered-pair ordinals -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

/-- Interpret an assigned row/bit family on the actual public unordered-pair list.
Only positions outside the pair's true demand are padded. -/
noncomputable def TableLayout.recordPayload {N : ℕ} (l : TableLayout) (row : ℕ → TableRow)
    (value : Fin l.count → ℕ → Bool) (u z : Fin N) (j : ℕ) : Bool :=
  let key := l.pairKey u.val z.val
  if h : j < l.pairWidth row l.count key then
    let p := (l.recordBitsEquiv row key).symm ⟨j,h⟩
    value p.val.1 p.val.2
  else false

/-- At every transmitted offset this lookup recovers the indicated row and bit,
independently of the ordering of the two endpoints. -/
theorem TableLayout.recordPayload_eq {N : ℕ} (l : TableLayout) (row : ℕ → TableRow)
    (value : Fin l.count → ℕ → Bool) (u z : Fin N) (ne : u ≠ z) (i : Fin l.count)
    (first : (row i).first = u.val) (second : (row i).second = z.val) (j : ℕ) (hj : j < (row i).width) :
    l.recordPayload row value (min u z) (max u z) (l.ordinal row i+j) = value i j := by
  let key := l.pairKey (min u z).val (max u z).val
  have hkey : l.pairKey (row i).first (row i).second = key := by
    dsimp [key,TableLayout.pairKey]
    rw [first,second]
    rcases le_total u z with h | h <;> simp [h]
  let p : l.RecordBit row key :=
    ⟨(i,j),fun h => ne (Fin.ext (first.symm.trans (h.trans second))),hkey,hj⟩
  have atKey : l.ordinal row i+j = (l.recordBitsEquiv row key p).val := rfl
  change (if h : l.ordinal row i+j < l.pairWidth row l.count key then
    value ((l.recordBitsEquiv row key).symm ⟨l.ordinal row i+j,h⟩).val.1
      ((l.recordBitsEquiv row key).symm ⟨l.ordinal row i+j,h⟩).val.2 else false) = value i j
  rw [atKey,dite_eq_left (l.recordBitsEquiv row key p).isLt,Equiv.symm_apply_apply]

end RoutingISA

namespace Routing

open private source_swap source_endpoint from OAI.Computability.BorderVNP.RoutingMessages

/-- Either endpoint of a checked transmission reads the assigned payload, since the
designated source reads it and the physical relay compares its two legs. -/
theorem Checks.hop_payload {N : ℕ} {h : 2 < N} {width : Fin N → Fin N → ℕ} {Header Pad : Type}
    {fixed : Block N} {header : Header} {high payload : Fin N → Fin N → ℕ → Bool}
    {m : Messages h width Header Pad} (checks : Checks h width fixed header high payload m)
    (u v : Fin N) (p : Hop h width u v) :
    m.hop u v p = payload (min u p.1) (max u p.1) p.2.val := by
  obtain ⟨_,_,source,relay,_⟩ := checks
  rcases source_endpoint high u p.1 p.2.val with here | other
  · exact source u v p here
  · have src := other.trans (source_swap high u p.1 p.2.val)
    have eq := source p.1 v (otherHop h width p) src
    rw [relay u v p]
    change m.hop p.1 v (otherHop h width p) = payload (min p.1 u) (max p.1 u) p.2.val at eq
    simpa only [min_comm p.1 u,max_comm p.1 u] using eq

end Routing

namespace TeamContraction

open VPVNP BurstRAM RoutingISA RoutingISA.Pins

variable {R r t d link inner n w : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)

/-- Boolean forced by one raw data row before any exterior assignment is chosen.
The ordinary field is the programmed input. The extra field uses the independently
chosen substitute, including the inactive zero padding. -/
def Wiring.dataBit (guess : Fin (R+1) → ℕ → Bool) (row : Packing.Directory.Row) (j : ℕ) : Bool :=
  let u := Fin.ofNat (R+1) row.team
  let off := row.offset+j
  if row.field = 0 then
    if h : row.processor < r then ((G.program ++ List.ofFn (G.literal u ⟨row.processor,h⟩))[off]?).getD false else false
  else
    let x := row.processor*(G.program.length+t)+off
    if u.val=0 ∧ x<d then guess u x else false

/-- Every actual raw data source word is the corresponding Boolean value, both for
ordinary processor literals and for a prepared secondary pin. -/
theorem Wiring.read_dataBit (guess : Fin (R+1) → ℕ → Bool) (u : Fin (R+1)) (pin : Fin d → Bool)
    (ext : Exterior R r link → Bool) (ib hb sb : ℕ) (m : Memory w)
    (input : (G.processorFields u pin ext ib hb sb).ContainsInput m)
    (substituted : SubstitutionAt (G.pinLayout u ib hb sb) (guess u) m)
    (row : Packing.Directory.Row) (team : row.team = u.val) (proc : row.processor < r)
    (j : ℕ) (offset : row.offset+j < G.program.length+t) :
    m (row.sourceBase (G.pinLayout u ib hb sb)+j) = Fin.ofNat _ (G.dataBit guess row j).toNat := by
  have caller : Fin.ofNat (R+1) row.team = u := Fin.ext (by rw [team,Fin.val_ofNat,Nat.mod_eq_of_lt u.isLt])
  let L := G.pinLayout u ib hb sb
  by_cases field : row.field=0
  · have read := input.literal (⟨row.processor,proc⟩ : Fin L.processors) (⟨row.offset+j,offset⟩ : Fin L.literal)
    rw [Packing.Directory.Row.sourceBase,ite_eq_left field,Nat.add_assoc]
    apply read.trans
    change Fin.ofNat (2^w) (((G.program ++ List.ofFn (G.literal u ⟨row.processor,proc⟩))[row.offset+j]?).getD false).toNat = _
    unfold Wiring.dataBit
    rw [caller,ite_eq_left field,dite_eq_left proc]
  · let x := row.processor*L.literal+(row.offset+j)
    have lim : x < L.count := (Nat.add_lt_add_left offset _).trans_le
      ((Nat.succ_mul _ _).symm ▸ Nat.mul_le_mul_right (G.program.length+t) proc)
    have read := substituted x lim
    rw [Packing.Directory.Row.sourceBase,ite_eq_right field,Nat.add_assoc _ row.offset,Nat.add_assoc]
    change m (L.ibase+x) = _
    rw [read]
    simp only [Wiring.dataBit,ite_eq_right field,caller]
    change (if L.active x then Fin.ofNat _ (guess u x).toNat else 0) = Fin.ofNat _ (if L.active x then guess u x else false).toNat
    split <;> rfl

/-- The assigned value of a table row bit, independently of the exterior. Data rows
use their forced Boolean sources and each shared row uses the expansion assignment. -/
def Wiring.assignedRows (guess : Fin (R+1) → ℕ → Bool) (D : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
    {count : ℕ} (shared : Fin count → ℕ → Bool) (i : Fin count) (j : ℕ) : Bool :=
  if h : i.val < (D.directory pp lp).length then G.dataBit guess (D.directory pp lp)[i.val] j else shared i j

end TeamContraction

end BorderVNP
end Computability
end OAI
