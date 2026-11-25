import OAI.ThreeFlat.Diagonal.LaneCursorCanonical

namespace OAI
/-! # Decoding an outgoing reservation from one receiving cell -/

namespace ThreeFlat.Diagonal.LaneCursor.RowLayout

variable {F : Type*} {p k low offsets slots : ℕ} {N : BitNetwork F p}
variable (P : RowLayout N k low offsets slots)

private instance {n : ℕ} (s : BitSource n p) : Decidable (wired s) := by
  cases s <;> dsimp only [wired] <;> infer_instance

/-- A rectangular trace provides a cell for every site and local ordinal. -/
structure Rectangular where
  cell : Row k low → Fin slots → Fin N.cells
  at_cell : ∀ row i, P.cellAddress (cell row i)=(row,i)

/-- Decode one tag by one XOR and one call to the rectangular cell address.
The check on the receiving occurrence suppresses unused wires and duplicate masks. -/
def reverseProbe (R : P.Rectangular) (lane : Lane k)
    (tag : Fin offsets × PayloadAddress low slots) : Option (Occurrence N) :=
  let owner := (splitRow k low).symm (lane,tag.2.1)
  let cell := R.cell (partner owner (P.offset tag.1)) tag.2.2.1
  let leg := tag.2.2.2
  if h : wired (N.source cell leg) then
    let a : Occurrence N := ⟨(cell,leg),h⟩
    if P.key a=(lane,tag) then some a else none
  else none

private theorem reverse_cell (R : P.Rectangular) (a : Occurrence N) (lane : Lane k)
    (tag : Fin offsets × PayloadAddress low slots) (ha : P.key a=(lane,tag)) :
    R.cell (partner ((splitRow k low).symm (lane,tag.2.1)) (P.offset tag.1)) tag.2.2.1
      = a.val.1 := by
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj ha
  have h : ((splitRow k low).symm (P.ownerLane a,(P.tag a).2.1))=P.owner a :=
    (splitRow k low).symm_apply_apply _
  apply P.cellAddress.injective
  rw [R.at_cell,h]
  exact Prod.ext (P.reaches a).symm rfl

theorem reverseProbe_iff (R : P.Rectangular) (lane : Lane k)
    (tag : Fin offsets × PayloadAddress low slots) (a : Occurrence N) :
    P.reverseProbe R lane tag=some a ↔ P.key a=(lane,tag) := by
  constructor
  · intro h
    unfold reverseProbe at h
    dsimp only at h
    split at h
    · split at h
      · rename_i hk
        obtain rfl := Option.some.inj h
        exact hk
      · cases h
    · cases h
  · intro ha
    have hc := P.reverse_cell R a lane tag ha
    have hl : tag.2.2.2=a.val.2 := (congrArg (fun z => z.2.2.2.2) ha).symm
    unfold reverseProbe
    dsimp only
    rw [hc,hl]
    simp only [dite_eq_left a.property,ha,ite_true]

/-- The reverse test computes the actual outgoing bit without enumerating
the trace's global incidence set. -/
theorem reverseProbe_emitted (R : P.Rectangular) (lane : Lane k)
    (tag : Fin offsets × PayloadAddress low slots) (pin : Fin p → Bool)
    (hidden : Fin N.internal → Bool) :
    (match P.reverseProbe R lane tag with
      | none => false
      | some a => (N.source a.val.1 a.val.2).read hidden pin) =
      P.emitted pin hidden lane tag := by
  cases e : P.reverseProbe R lane tag with
  | none =>
    symm
    apply P.emitted_unused
    rintro ⟨a,ha⟩
    have := (P.reverseProbe_iff R lane tag a).2 ha
    simp [e] at this
  | some a =>
    have ha := (P.reverseProbe_iff R lane tag a).1 e
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj ha
    exact (P.emitted_wire pin hidden a).symm

/-- A rectangular candidate matches exactly when it is wired to the queried
owner and the public mask ordinal is canonical. The receiver fixes both
the cell slot and the leg. -/
theorem candidate_key_iff (R : P.Rectangular) (lane : Lane k)
    (tag : Fin offsets × PayloadAddress low slots) :
    let owner := (splitRow k low).symm (lane,tag.2.1)
    let cell := R.cell (partner owner (P.offset tag.1)) tag.2.2.1
    ∀ h : wired (N.source cell tag.2.2.2),
      let a : Occurrence N := ⟨(cell,tag.2.2.2),h⟩
      P.canonical.key a=(lane,tag) ↔ P.owner a=owner ∧ firstMask P.offset tag.1=true := by
  intro owner cell h a
  have site : P.cellAddress cell=(partner owner (P.offset tag.1),tag.2.2.1) :=
    R.at_cell _ _
  have seg : (splitRow k low) owner=(lane,tag.2.1) := (splitRow k low).apply_symm_apply _
  constructor
  · intro hit
    have upper := congrArg (fun z => z.1) hit
    have lower := congrArg (fun z => z.2.2.1) hit
    have mask := congrArg (fun z => z.2.1) hit
    have joined : (splitRow k low) (P.owner a)=(lane,tag.2.1) := by
      apply Prod.ext
      · exact upper
      · exact lower
    exact ⟨(splitRow k low).injective (joined.trans seg.symm),
      ((P.canonical_code_iff a tag.1).1 mask).1⟩
  · rintro ⟨ha,hm⟩
    have geom : partner owner (P.offset (P.code a))=partner owner (P.offset tag.1) := by
      have reach : (P.cellAddress cell).1=partner (P.owner a) (P.offset (P.code a)) := P.reaches a
      rw [ha,site] at reach
      exact reach.symm
    have eq : P.offset tag.1=P.offset (P.code a) := by
      apply Fin.ext
      have same := congrArg (fun t : Row k low => owner.val ^^^ t.val) geom.symm
      simpa only [partner,←Nat.xor_assoc,Nat.xor_self,Nat.zero_xor] using same
    have hc := (P.canonical_code_iff a tag.1).2 ⟨hm,eq⟩
    have pair := (congrArg (splitRow k low) ha).trans seg
    apply Prod.ext
    · exact congrArg (fun z : Lane k × Fin (2^low) => z.1) pair
    apply Prod.ext
    · exact hc
    apply Prod.ext
    · exact congrArg (fun z : Lane k × Fin (2^low) => z.2) pair
    apply Prod.ext
    · exact congrArg (fun z : Row k low × Fin slots => z.2) site
    · rfl

end ThreeFlat.Diagonal.LaneCursor.RowLayout

end OAI
