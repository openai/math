import OAI.Computability.BorderVNP.CellPacketGeometryOrderedRun

/-! # Public volume and cubic logarithmic factor of the true native geometry -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.LiveWords

open ParseBatchSort Packing.BankPacket Packing.Word VPVNP.VerifierNetwork

/-- Least power-of-two padding of a possibly empty physical table. -/
theorem pow_clog_le (n : ℕ) : 2^(Nat.clog 2 n) ≤ 2*(n+1) := by
  cases h : Nat.clog 2 n with
  | zero => simp; omega
  | succ j =>
    have smaller : 2^j < n := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mp (by omega)
    rw [pow_succ]
    omega

/-- The sorter costs a cubic factor in a common index and operand width, per
actual padded row. A combined payload may contain two width-sized fields. -/
theorem sort_cubic {a k w W : ℕ} (ha : a≤W) (hk : k≤W) (hw : w≤2*W) :
    (sortedFrame a k w).size ≤ 1+2^a*(500*(W+1)^3) := by
  apply (sortedFrame_size a k w).trans
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  calc
    _ ≤ (((2*W+W)+1+W)+W^2*(24*((2*W+W)+1+W)+1)+(2*W+W)+W^2*(24*(2*W+W)+1)) := by gcongr
    _ ≤ _ := by nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3)]

/-- Same cubic factor for the two stable cell-count histograms. -/
theorem histogram_cubic {s C k w W : ℕ} (hb : Nat.clog 2 (s+C) ≤ W) (hk : k≤W) (hw : w≤W) :
    histogramBudget s C k w ≤ 2^(Nat.clog 2 (s+C))*(500*(W+1)^3) := by
  unfold histogramBudget
  apply Nat.mul_le_mul_left
  calc
    _ ≤ ((W+1+W)+((W+W)+1+W)+W^2*(24*((W+W)+1+W)+1)+W*(60*W+16*W+33)+W^2*(24*(W+W)+1)) := by gcongr
    _ ≤ _ := by nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3)]

variable {σ E I Orig : Type} [Fintype σ] [Fintype E] [Fintype I] {s C k w q u : ℕ}

/-- Total public scalar volume before power-of-two padding. Private one-copy
body bits, multiplicities, and expanded repeated wire occurrences are excluded. -/
def Template.publicVolume (T : Template E I Orig s C) : ℕ :=
  1+s+C+T.atoms.length+T.recordSlots.length+T.chunkLabels.length+Fintype.card T.Fields+
    ∑ z : T.RowPin, (tape (T.format z.1))[z.2].nodes

/-- Canonical dimensions of the three native sorts. -/
def Template.publicDepth (T : Template E I Orig s C) := Nat.clog 2 (C+T.atoms.length+C)
/-- Power-of-two row width of the descriptor sort (three words per chunk). -/
def Template.chunkDepth (T : Template E I Orig s C) := Nat.clog 2 (C+3*T.chunkLabels.length+C)
/-- Power-of-two width of the chronological record-field source. -/
def Template.recordDepth (T : Template E I Orig s C) := Nat.clog 2 T.recordSlots.length

omit [Fintype I] in
/-- The exact geometry output arity is linear in the genuine public volume. -/
theorem Template.output_linear (T : Template E I Orig s C) :
    Total T.publicDepth T.chunkDepth ≤ 20*T.publicVolume := by
  have a := pow_clog_le (C+T.atoms.length+C)
  have b := pow_clog_le (C+3*T.chunkLabels.length+C)
  simp only [Total,Template.publicDepth,Template.chunkDepth,Template.publicVolume]
  omega

omit [Fintype E] [Fintype I] in
/-- The least padding dimensions always fit their three genuine public arrays. -/
theorem Template.sort_rooms (T : Template E I Orig s C) :
    C+T.atoms.length+C ≤ 2^T.publicDepth ∧ C+(Schema.coords T.chunkLabels.length).length+C ≤ 2^T.chunkDepth ∧
      T.recordSlots.length ≤ 2^T.recordDepth := by
  refine ⟨Nat.le_pow_clog (by decide) _,?_,Nat.le_pow_clog (by decide) _⟩
  simpa [Schema.coords,List.length_flatMap,Template.chunkDepth,Nat.mul_comm] using
    Nat.le_pow_clog (by decide : 1 < 2) (C+3*T.chunkLabels.length+C)

/-- The site-ordered packet frame before it is joined to the terminal routing
outputs. Keeping its shared Boolean gates here allows the combined geometry to
be lowered into a single native table. -/
noncomputable def Template.orderedFrame (T : Template E I Orig s C) (up : Frame σ (Base s k w E I))
    (anchors : Frame σ (Fin s × Fin q)) (baseOwner : Fin s → Fin C) (pin : Orig → T.Fields)
    (pad : s < 2^q) (dest H : ℕ) : Frame σ (GeometryFrameEncoding.Outputs (Total T.publicDepth T.chunkDepth) w) :=
  joint (Schema.source C T.publicDepth T.chunkDepth (T.orderedPins up anchors baseOwner T.sort_rooms.2.2 pad))
    (Schema.expression C T.chunkDepth T.sort_rooms.1 dest H (T.reference baseOwner pin))

/-- Shared cubic bound for the actual frame, including the site, descriptor
and cell sorts and both histograms. -/
theorem Template.orderedFrame_cubic (T : Template E I Orig s C) (up : Frame σ (Base s k w E I))
    (anchors : Frame σ (Fin s × Fin q)) (baseOwner : Fin s → Fin C) (pin : Orig → T.Fields)
    (pad : s < 2^q) (dest H W : ℕ)
    (wk : k≤W) (ww : w≤W) (wq : q≤W) (wp : T.publicDepth≤W) (wd : T.chunkDepth≤W) (wb : T.recordDepth≤W)
    (wh : Nat.clog 2 (s+C) ≤ W) :
    (T.orderedFrame up anchors baseOwner pin pad dest H).size ≤
      up.size+anchors.size+250000*T.publicVolume*(W+1)^3 := by
  let V := T.publicVolume
  let B := 500*(W+1)^3
  have hv : 1 ≤ V := by dsimp [V,Template.publicVolume]; omega
  have hN : T.atoms.length ≤ V := by dsimp [V,Template.publicVolume]; omega
  have hM : T.chunkLabels.length ≤ V := by dsimp [V,Template.publicVolume]; omega
  have hE : Fintype.card T.Fields ≤ V := by dsimp [V,Template.publicVolume]; omega
  have hnodes : (∑ z : T.RowPin, (tape (T.format z.1))[z.2].nodes) ≤ V := by dsimp [V,Template.publicVolume]; omega
  have capP : 2^T.publicDepth ≤ 10*V := (pow_clog_le _).trans (by dsimp [V,Template.publicVolume]; omega)
  have capD : 2^T.chunkDepth ≤ 10*V := (pow_clog_le _).trans (by dsimp [V,Template.publicVolume]; omega)
  have capB : 2^T.recordDepth ≤ 10*V := (pow_clog_le _).trans (by dsimp [V,Template.publicVolume]; omega)
  have capH : 2^(Nat.clog 2 (s+C)) ≤ 10*V := (pow_clog_le _).trans (by dsimp [V,Template.publicVolume]; omega)
  have sP := (sort_cubic wp wk (by omega : w≤2*W)).trans (Nat.add_le_add_left (Nat.mul_le_mul_right B capP) 1)
  have sD := (sort_cubic wd wk (by omega : w≤2*W)).trans (Nat.add_le_add_left (Nat.mul_le_mul_right B capD) 1)
  have sB := (sort_cubic wb wq (by omega : w+k≤2*W)).trans (Nat.add_le_add_left (Nat.mul_le_mul_right B capB) 1)
  have sH := (histogram_cubic wh wk ww).trans (Nat.mul_le_mul_right B capH)
  have cubic : 100*(w+1)^2 ≤ B := by dsimp [B]; nlinarith [Nat.mul_le_mul ww ww,Nat.zero_le (W^3)]
  have width : q+(w+k) ≤ B := by dsimp [B]; nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3)]
  have kw : k+w≤B := by omega
  have kc : k≤B := by omega
  have wc : w≤B := by omega
  have hb : 1 ≤ B := by dsimp [B]; nlinarith [Nat.zero_le (W^3),Nat.zero_le (W^2)]
  have mass : 1 ≤ V*B := Nat.mul_le_mul hv hb
  have live := (T.exists_liveFrame up T.chunkLabels.get).choose_spec.1
  change (T.sourcePins up).size ≤ _ at live
  have hn := Nat.mul_le_mul hnodes cubic
  have nh := Nat.mul_le_mul hN kw
  have md := Nat.mul_le_mul hM kc
  have eh := Nat.mul_le_mul hE wc
  have pb := Nat.mul_le_mul capB width
  have pn := Nat.mul_le_mul capP kw
  have dm := Nat.mul_le_mul capD kc
  have dcost := Nat.mul_le_mul (Nat.mul_le_mul_left 5 capD) cubic
  have dc : 5*2^T.chunkDepth*(100*(w+1)^2) ≤ 50*(V*B) := dcost.trans_eq (by ring)
  have first := T.orderedPins_size up anchors baseOwner T.sort_rooms.2.2 pad
  have second := Schema.joint_budget (d := T.chunkDepth) (T.orderedPins up anchors baseOwner T.sort_rooms.2.2 pad)
    T.sort_rooms.1 dest H (T.reference baseOwner pin)
  have all : (T.orderedFrame up anchors baseOwner pin pad dest H).size ≤ up.size+anchors.size+500*(V*B) := by
    change (joint _ _).size ≤ _
    simp only [Nat.mul_assoc] at sP sD sB sH pb pn dm
    omega
  exact all.trans_eq (by dsimp [V,B]; ring)

/-- The true native table with least possible sort padding costs the two input
frames plus public scalar volume times a cubic logarithmic factor. -/
theorem Template.orderedGeometry_cubic (T : Template E I Orig s C) (up : Frame σ (Base s k w E I))
    (anchors : Frame σ (Fin s × Fin q)) (baseOwner : Fin s → Fin C) (pin : Orig → T.Fields)
    (pad : s < 2^q) (dest H : ℕ) (pins : σ → (Fin u ⊕ Fin 0) ⊕ Bool) (W : ℕ)
    (wk : k≤W) (ww : w≤W) (wq : q≤W) (wp : T.publicDepth≤W) (wd : T.chunkDepth≤W) (wb : T.recordDepth≤W)
    (wh : Nat.clog 2 (s+C) ≤ W) :
    (T.orderedGeometry up anchors baseOwner pin T.sort_rooms.2.2 pad T.chunkDepth T.sort_rooms.1 dest H pins).size ≤
      4*(up.size+anchors.size)+1000000*T.publicVolume*(W+1)^3 := by
  have h := T.orderedFrame_cubic up anchors baseOwner pin pad dest H W wk ww wq wp wd wb wh
  have compiled := GeometryFrameEncoding.size_le (T.orderedFrame up anchors baseOwner pin pad dest H) pins
  exact compiled.trans ((Nat.mul_le_mul_left 4 h).trans_eq (by ring))

end CellPacketGeometry.LiveWords

end BorderVNP
end Computability
end OAI
