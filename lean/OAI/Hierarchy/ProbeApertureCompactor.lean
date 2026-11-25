import OAI.Hierarchy.ProbeApertureMask
import OAI.Hierarchy.ProbeHistogramNative
import OAI.ThreeFlat.Diagonal.MotifCompactionOrder

namespace OAI
/-! # A fixed trivalent circuit packs original role slots into the signed site's chord aperture -/

noncomputable section
namespace Hierarchy.Probe.ApertureCompactor
open ThreeFlat Routing Routing.StableCompaction
open Diagonal TraceCircuit TraceWords MotifSelectorChecks MotifBinaryPacking
open Computability.VPVNP.BurstRAM
open scoped Classical BigOperators Fin.CommRing

variable {n d b : ℕ}
abbrev Size (n d b : ℕ) := n*b+(n*d+n*d)

def checkPins : Fin (Fintype.card (ApertureMask.Pins n d b))→BitSource (n*d) (Size n d b) :=
  fun t=>match (Fintype.equivFin _).symm t with
  | .inl p=>.pin ((finProdFinEquiv p).castAdd _)
  | .inr i=>.hidden i

def compactPins : Fin (n*d+(n*d+n*d))→BitSource (n*d) (Size n d b) :=
  Fin.append BitSource.hidden (fun j=>.pin (Fin.natAdd (n*b) j))

def component (F : Type*) [CommRing F] (n d b : ℕ) : Bool → Component F (n*d) (Size n d b)
  | true=>⟨_,ApertureMask.network F n d b,checkPins⟩
  | false=>⟨_,NativeHistogram.compactor F (n*d),compactPins⟩

def network (F : Type*) [CommRing F] (n d b : ℕ) : BitNetwork F (Size n d b) :=
  BitNetwork.glue (fun i=>(component F n d b i).net) (fun i=>(component F n d b i).wire)

def pins (width : Fin n→ℕ) (input output : Fin (n*d)→Bool) : Fin (Size n d b)→Bool :=
  Fin.append (blocks n b (fun i=>bits (width i:Word b))) (Fin.append input output)

private theorem check_at (width : Fin n→ℕ) (input output mask : Fin (n*d)→Bool) :
    (fun j=>(checkPins (n:=n) (d:=d) (b:=b) j).read mask (pins width input output))=
      (ApertureMask.pins (b:=b) width mask) ∘ (Fintype.equivFin (ApertureMask.Pins n d b)).symm := by
  funext j
  rcases h : (Fintype.equivFin (ApertureMask.Pins n d b)).symm j with ⟨i,t⟩|a
  · simp [checkPins,pins,h,ApertureMask.pins,blocks_at,BitSource.read]
  · simp [checkPins,h,ApertureMask.pins,BitSource.read]

private theorem compact_at (width : Fin n→ℕ) (input output mask : Fin (n*d)→Bool) :
    (fun j=>(compactPins (n:=n) (d:=d) (b:=b) j).read mask (pins width input output))=
      Fin.append mask (Fin.append input output) := by
  funext j
  refine Fin.addCases (fun i=>?_) (fun i=>?_) j <;>
    simp [compactPins,pins,BitSource.read,-Fin.natAdd_eq_addNat]

/-- The exposed width words determine a unique internal selection mask.
Consequently the reverse network has exactly the same signed factor as a
forward packing on the uniquely padded physical role data. -/
theorem eval (F : Type*) [CommRing F] (width : Fin n→ℕ) (input output : Fin (n*d)→Bool)
    (small : ∀i,width i≤d) (room : d<2^b) :
    (network F n d b).eval (pins width input output) =
      if output=compact (ApertureMask.mask width) input then 1 else 0 := by
  rw [network,BitNetwork.glue_eval]
  have per (mask : Fin (n*d)→Bool) :
      (∏t,((component F n d b t).net).eval
        (fun j=>((component F n d b t).wire j).read mask (pins width input output)))=
      (if mask=ApertureMask.mask width then (1:F) else 0)*
      (if output=compact mask input then 1 else 0) := by
    rw [Fintype.prod_bool]
    apply congrArg₂ (·*·)
    · change (ApertureMask.network F n d b).eval
        (fun j=>(checkPins (n:=n) (d:=d) (b:=b) j).read mask (pins width input output))=_
      rw [check_at]
      exact ApertureMask.eval F width mask small room
    · change (NativeHistogram.compactor F (n*d)).eval
        (fun j=>(compactPins (n:=n) (d:=d) (b:=b) j).read mask (pins width input output))=_
      rw [compact_at]
      exact NativeHistogram.compactor_run F _ _ _ _
  simp only [per,ite_mul,one_mul,zero_mul]
  simp

def compacted (width : Fin n→ℕ) (x : ∀i,Fin (width i)→Bool) (j : Fin (n*d)) :=
  if h : j.val<∑i,width i then flatten width x ⟨j.val,h⟩ else false

theorem compacted_eq (width : Fin n→ℕ) (small : ∀i,width i≤d) (x : ∀i,Fin (width i)→Bool) :
    compact (ApertureMask.mask width) (TrackData.padded finProdFinEquiv.symm width x)=compacted (d:=d) width x := by
  funext j
  by_cases hj : j.val<∑i,width i
  · let k : Fin (∑i,width i):=⟨j.val,hj⟩
    have stream:=congrFun (stream_eq_flatten width small x) k
    change compact (ApertureMask.mask width) (TrackData.padded finProdFinEquiv.symm width x) j =
      flatten width x k at stream
    simpa [compacted,hj,k] using stream
  · rw [compacted,dite_eq_right hj]
    change compact (TrackData.mask finProdFinEquiv.symm width)
      (TrackData.padded finProdFinEquiv.symm width x) j = false
    exact TrackData.compact_after finProdFinEquiv.symm width small x j (Nat.le_of_not_gt hj)

theorem packed_eval (F : Type*) [CommRing F] (width : Fin n→ℕ) (small : ∀i,width i≤d)
    (room : d<2^b) (x : ∀i,Fin (width i)→Bool) (out : Fin (n*d)→Bool) :
    (network F n d b).eval (pins width (TrackData.padded finProdFinEquiv.symm width x) out) =
      if out=compacted width x then 1 else 0 := by
  rw [eval F _ _ _ small room,compacted_eq _ small]

theorem cost (F : Type*) [CommRing F] (n d b : ℕ) :
    (network F n d b).cells+(network F n d b).internal≤
      n*d+n*d*(500*b+501)+128000*(n*d+1)*(Nat.log 2 (n*d+1)+2)^3 := by
  simp only [network,BitNetwork.glue_cells,BitNetwork.glue_internal,Fintype.sum_bool,component]
  have check:=ApertureMask.cost F n d b
  have compacted:=NativeHistogram.compactor_size F (n*d)
  omega

end Hierarchy.Probe.ApertureCompactor
end

end OAI
