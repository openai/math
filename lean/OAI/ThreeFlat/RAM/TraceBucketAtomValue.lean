import OAI.ThreeFlat.RAM.TraceBucketOriginalArgs
import OAI.ThreeFlat.RAM.TraceBucketComparisonArgs
import OAI.ThreeFlat.RAM.TraceBucketEndArgs
import OAI.ThreeFlat.RAM.TraceBucketFieldFits

namespace OAI
/-! # Value of the native original-atom metadata procedure -/

namespace ThreeFlat.RAM.TraceBucketAtom
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr
open Diagonal.TraceSourceOwner
open scoped Fin.CommRing
variable {W : ℕ}

def Layout.relayInputs (s : Layout) (lane row field stage : ℕ) :=
  Diagonal.TraceBucketRelay.arguments s.arcs s.tags s.per s.depth s.low stage
    (if stage=0 then s.pinCount lane else 0) s.equalId row field

def atomNat (s : Layout) (m : ℕ→ℕ) (lane row field stage : ℕ) :=
  if row<s.relays then Diagonal.TraceBucketRelay.values (s.relayInputs lane row field stage)
  else if row<s.relays+s.gates then TraceBucketFields.originalNat m (originalInputs s m lane row field)
  else if row<s.relays+s.gates+s.tags then TraceBucketFields.compareNat (cmpInputs s m lane row field)
  else let v := holeInputs s lane row field
       if v 0<3 then 2+v 1+v 2+v 3 else if v 4=0 then v 5 else v 6

/-- Every condition in this certificate is a bound on the physical memory
or on an explicitly decoded scalar. It does not constrain any emitted word. -/
structure Widths (s : Layout) (v : Fin 4→Word W) (m : Memory W) (cap : ℕ) : Prop where
  terms : s.relays+s.gates+s.tags<2^W
  header : s.shape.header+2<2^W
  interval : s.pinLow (v 2).val+2*s.lowRows<2^W
  literal : 3<2^W
  margin : 5*cap+128≤W
  relay : (v 0).val<s.relays →
    Diagonal.TraceBucketRelay.Bounds W (s.relayInputs (v 2).val (v 0).val (v 1).val (v 3).val)
  original : s.relays≤(v 0).val → (v 0).val<s.relays+s.gates →
    let i := (v 0).val-s.relays
    let a := (v 2).val*s.lowRows+i/s.slots
    let j := i%s.slots
    let n := (m (s.readAt a j (v 1).val)).val
    let u := originalInputs s (fun t => (m t).val) (v 2).val (v 0).val (v 1).val
    s.slots<2^W ∧ s.readAt a j (v 1).val<2^W ∧ (∀ l, TraceOwnerFormula.vars s.shape 1 n a l<2^cap) ∧
      (∀ l, u l<2^W) ∧ u 11+(u 2 ^^^ u 3)<2^W ∧ u 12+u 5<2^W
  comparison : s.relays+s.gates≤(v 0).val → (v 0).val<s.relays+s.gates+s.tags →
    CompareFits W cap s v m ∧ s.depth+1<2^W
  hole : s.relays+s.gates+s.tags≤(v 0).val →
    let q := (v 0).val-(s.relays+s.gates+s.tags)
    let a := (v 2).val*s.lowRows+q/s.shape.stride
    let j := q%s.shape.stride
    s.shape.stride<2^W ∧ a<s.shape.rows ∧ j<s.shape.stride ∧
      (∀ i, TraceOwnerFormula.vars s.shape 1 a j i<2^cap) ∧ s.shape.count+s.shape.rows*s.shape.stride+1≤2^cap ∧
      (∀ i,holeInputs s (v 2).val (v 0).val (v 1).val i<2^W)

theorem program_value (s : Layout) (v : Fin 4→Word W) (data : Fin 1→Word W) (m : Memory W)
    (cap : ℕ) (h : Widths s v m cap) :
    (program W s).eval data m v=(atomNat s (fun t => (m t).val) (v 2).val (v 0).val (v 1).val (v 3).val : Word W) := by
  have proj := selected_word s data m v h.terms
  dsimp only at proj
  have header : s.shape.header<2^W := by have := h.header; omega
  by_cases a : (v 0).val<s.relays
  · have hr := h.relay a
    have val := relayArgs_value s v data m header h.interval hr.inputs
    simp only [a,ite_true,val,Diagonal.TraceBucketRelay.formula_natural] at proj
    simpa only [atomNat,a,ite_true,Layout.relayInputs] using proj (Diagonal.TraceBucketRelay.fits _ _ _ hr)
  · by_cases b : (v 0).val<s.relays+s.gates
    · have start : s.relays≤(v 0).val := by omega
      obtain ⟨ss,raw,small,nums,dict,ids⟩ := h.original start b
      have val := origArgs_value s v data m cap start ss header h.interval raw small h.margin nums
      simp only [a,b,ite_false,ite_true,val] at proj
      simpa only [atomNat,a,b,ite_false,ite_true] using proj (TraceBucketFields.original_fits _ _ _ nums h.literal dict ids)
    · by_cases c : (v 0).val<s.relays+s.gates+s.tags
      · obtain ⟨hc,hd⟩ := h.comparison (by omega) c
        have val := cmpArgs_value s v data m cap hc
        simp only [a,b,c,ite_false,ite_true,val] at proj
        have hdr : 2+s.shape.header<2^W := by have := h.header; omega
        simpa only [atomNat,a,b,c,ite_false,ite_true] using
          proj (TraceBucketFields.compare_fits _ _ _ hc.numeric h.literal hdr hd)
      · have start : s.relays+s.gates+s.tags≤(v 0).val := by omega
        obtain ⟨stride,row,slot,small,capacity,nums⟩ := h.hole start
        have val := holeArgs_value s v data m cap start stride header h.interval row slot small capacity h.margin nums
        simp only [a,b,c,ite_false,val] at proj
        have castChoice (q : Prop) [Decidable q] (x y : ℕ) :
            ((if q then x else y : ℕ) : Word W) = (if q then (x : Word W) else (y : Word W)) := by
          by_cases truth : q <;> simp only [truth,ite_true,ite_false]
        simpa only [atomNat,a,b,c,ite_false,castChoice,Nat.cast_add,Nat.cast_ofNat] using
          proj (TraceBucketFields.hole_fits _ _ _ (nums 0) (nums 4) h.literal)


end ThreeFlat.RAM.TraceBucketAtom

end OAI
