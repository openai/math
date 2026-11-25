import OAI.Computability.NearSquareRoot.FixedCandidateCRTStages
import OAI.Computability.NearSquareRoot.FixedLayerSetup
import OAI.Computability.NearSquareRoot.FixedLayerSweep

/-! # One prepared forest of bounded physical CRT switch calls -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTStream
open IntegerMultiplication Code Space FixedPoint DigitPacking

/-- The short per-stage header carries the original box, level, direction and Beneš phase. -/
def seed (inv : Bool) {n : ℕ} (s : Switch n) : CRTTable.HeaderSeed :=
  ((s.2.1,tally s.2.2),inv,tally s.1.val,BoxProgram.encoded (tally (addressBits n)))

def seeds (inv : Bool) (t : Tally) : List CRTTable.HeaderSeed :=
  CRTTable.seedStream (inv,tally (BoxScale.width t.length),BoxProgram.encoded t)

theorem seeds_poly (inv : Bool) : Poly (seeds inv) :=
  ((Easy.const inv).poly.pair (BoxParameterTask.width_poly.pair BoxProgram.encoded_poly)).compose
    CRTTable.seedStream_poly

private theorem seedStream_length_cast (D d : ℕ) (ds : List CRTTable.ControlAxis) (inv : Bool)
    (hl : ds.length = d) :
    CRTTable.seedStream (inv,tally D,ds) = (CRTTable.switchOrder d D inv).map
      (fun s => ((s.2.1,tally s.2.2),inv,tally s.1.val,ds)) := by
  subst d
  exact CRTTable.seedStream_eq _ _ _

theorem seeds_eq (inv : Bool) (n : ℕ) :
    seeds inv (tally (addressBits n)) = (order n inv).map (seed inv) := by
  unfold seeds order seed
  rw [tally_length]
  exact seedStream_length_cast _ _ _ _ (by simp [BoxProgram.encoded])

def count (n : ℕ) := Nat.clog 2 (box n).length * (2*BoxScale.width (addressBits n))

theorem order_length (inv : Bool) (n : ℕ) : (order n inv).length = count n :=
  CRTTable.switchOrder_length _ _ _

variable {I : Type} (n : I → ℕ) (hs : ∀ i, Directory (n i)) (inv : Bool)

/-- A stage is among the genuinely generated depth/phase entries. All input records are allowed. -/
abbrev Input := (i : I) × {s // s ∈ order (n i) inv} × Array (n i)

noncomputable section

private def prefixState {n : ℕ} (h : Directory n) (inv : Bool) (v : Array n) (j : ℕ) : Array n :=
  ((order n inv).take j).foldl (step h inv) v

private theorem timeCap (C a b : ℕ) : a + C*(b+1)+1 ≤ (C+2)*(a+b+1) := by
  have h := Nat.mul_le_mul_left C (show b+1 ≤ a+b+1 by omega)
  rw [Nat.add_mul]
  omega

private theorem spaceCap (C b : ℕ) : C*(b+1)+b+1 ≤ (C+2)*(b+1) := by
  rw [Nat.add_mul]; omega

/-- Prepare the descriptors once, then execute one fixed physical command on each descriptor.
Only one scratch allowance is charged to peak space. -/
theorem sweep (hn : ∀ i, 2 ≤ n i) (tick : ℕ → ℕ)
    (stage : BoundedTask (fun p : Input n inv => tick (n p.1)) (fun p => n p.1)
      (fun p => .fork (send (seed inv p.2.1.val)) (framed p.2.2))
      (fun p => framed (step (hs p.1) inv p.2.2 p.2.1.val))) :
    StreamPass n (fun u => count u*tick u+u) (fun i => outcome (hs i) inv) := by
  let Y := (i : I) × Array (n i)
  let rows (y : Y) := seeds inv (tally (addressBits (n y.1)))
  let state (y : Y) (j : ℕ) := framed (prefixState (hs y.1) inv y.2 j)
  have rl (y : Y) : (rows y).length = (order (n y.1) inv).length := by simp [rows,seeds_eq]
  let runAt := (y : Y) × Fin (rows y).length
  let sel (p : runAt) : Fin (order (n p.1.1) inv).length := Fin.cast (rl p.1) p.2
  let s (p : runAt) := (order (n p.1.1) inv)[(sel p).val]
  let entry (p : runAt) : Input n inv :=
    ⟨p.1.1,⟨s p,List.getElem_mem (sel p).isLt⟩,prefixState (hs p.1.1) inv p.1.2 p.2.val⟩
  have rowAt (p : runAt) : (rows p.1)[p.2.val] = seed inv (s p) := by
    simp [rows,seeds_eq,s,sel]
  have next (p : runAt) : step (hs p.1.1) inv (entry p).2.2 (s p) =
      prefixState (hs p.1.1) inv p.1.2 (p.2.val+1) := by
    have hi : p.2.val < (order (n p.1.1) inv).length := (sel p).isLt
    simp only [entry,prefixState,s,sel,Fin.val_cast]
    rw [List.take_succ_eq_append_getElem hi,List.foldl_append]
    rfl
  have once := (stage.on entry).conform (fun _ => rfl) (fun _ => rfl)
    (input' := fun p : runAt => .fork (send ((rows p.1)[p.2.val])) (state p.1 p.2.val))
    (fun p => by rw [rowAt]) (output' := fun p : runAt => state p.1 (p.2.val+1))
    (fun p => congrArg framed (next p))
  obtain ⟨A,hA⟩ := FixedLayer.headerVolume n hn (seeds inv) (seeds_poly inv)
  let C := A+75000
  let V (y : Y) := C*(n y.1+1)
  have bounded := FixedLayer.sweep default rows state (fun y => tick (n y.1)) V (fun y => n y.1) once
    (fun y => (hA y.1).trans (Nat.mul_le_mul_right _ (Nat.le_add_right ..)))
    (fun y _ _ => (framed_size (hn y.1) _).trans (Nat.mul_le_mul_right _ (Nat.le_add_left ..)))
  let T (y : Y) := count (n y.1)*tick (n y.1)+n y.1
  have time (y : Y) : (rows y).length*tick (n y.1)+V y+1 ≤ (C+2)*(T y+1) := by
    rw [rl,order_length]
    exact timeCap C _ _
  have space (y : Y) : V y+n y.1+1 ≤ (C+2)*(n y.1+1) := spaceCap C _
  have boot := (FixedLayer.prepareHeader (fun y : Y => n y.1) (fun y => hn y.1) (seeds inv)
    (seeds_poly inv) (fun y => y.2)).mono (time' := T) (fun _ => Nat.le_add_left ..) (fun _ => le_rfl)
  apply sequence boot
  apply (bounded.bound (C+2) (C+2) time space).conform (fun _ => rfl) (fun _ => rfl)
  · intro y; rfl
  · intro y
    simp [state,prefixState,rl,fold_step]

end
end FixedCandidate.CRTStream

end NearSquareRoot
end Computability
end OAI
