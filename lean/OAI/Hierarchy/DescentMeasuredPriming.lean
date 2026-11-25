import OAI.Hierarchy.DescentMeasuredRowProducer
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # Fixed input directories for the native measured header and payload passes -/
namespace Hierarchy.DescentMeasuredPriming

open DescentMeasuredHeader DescentMeasuredWeights DescentPackedExchange ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable {H k Δ w : ℕ}
local notation "primingRows" h:arg z:arg d:arg => (h*(z+1)+h*d)
local notation "primingWords" h:arg z:arg d:arg => ((primingRows h z d)*2^z)

abbrev span := DescentDyadicSpan.span
private theorem span_pos (n : ℕ) : 0 < span n := DescentDyadicSpan.span_pos n
private theorem span_ge (n : ℕ) : n ≤ span n := DescentDyadicSpan.span_ge n

theorem span_le (n : ℕ) : span n ≤ 2*n+1 := DescentDyadicSpan.span_le n

def bank (lo n j : ℕ) : Bank := ⟨lo+j*span n,Nat.clog 2 n⟩
def start (lo H k Δ : ℕ) := lo+11*span (primingWords H k Δ)

def header (lo H k Δ : ℕ) : Tape :=
  ⟨bank lo (primingWords H k Δ) 0,bank lo (primingWords H k Δ) 1,bank lo (primingWords H k Δ) 2,bank lo (primingWords H k Δ) 3,bank lo (primingWords H k Δ) 4,bank lo (primingWords H k Δ) 5⟩

def payload (lo H k Δ : ℕ) : DataTape :=
  ⟨bank lo (primingWords H k Δ) 6,bank lo (primingWords H k Δ) 7,bank lo (primingWords H k Δ) 8,⟨start lo H k Δ,Nat.clog 2 (primingRows H k Δ)⟩,bank lo (primingWords H k Δ) 9,bank lo (primingWords H k Δ) 10⟩

/-- Exclusive end of the four scans, including the producer's sentinel. -/
def finish (lo H k Δ : ℕ) := origin (start lo H k Δ) H k Δ + (primingWords H k Δ)

private theorem row_count : (primingRows H k Δ) ≤ (primingWords H k Δ) :=
  (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k))

private theorem site_count : H ≤ (primingRows H k Δ) := by
  have h : H ≤ H*(k+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  omega

theorem extent (lo H k Δ : ℕ) : finish lo H k Δ ≤ lo + 26*(primingWords H k Δ) + 12 := by
  have h := span_le (primingWords H k Δ)
  have r := row_count (H:=H) (k:=k) (Δ:=Δ)
  unfold finish origin start
  omega

theorem extent_by_dimension (lo H k Δ : ℕ) :
    finish lo H k Δ ≤ lo+26*(H*(k+Δ+1)*2^k)+12 := by
  convert extent lo H k Δ using 1; ring

private theorem bank_end (lo H k Δ : ℕ) (j : ℕ) (hj : j < 11) :
    (bank lo (primingWords H k Δ) j).base+(bank lo (primingWords H k Δ) j).size ≤ start lo H k Δ := by
  change lo+j*span (primingWords H k Δ)+span (primingWords H k Δ) ≤ lo+11*span (primingWords H k Δ)
  have h := Nat.mul_le_mul_right (span (primingWords H k Δ)) (show j+1 ≤ 11 by omega)
  rw [Nat.succ_mul] at h
  omega

private theorem bank_fits (lo H k Δ : ℕ) (room : finish lo H k Δ < 2^w) (j : ℕ) (hj : j < 11) :
    (bank lo (primingWords H k Δ) j).Fits w (start lo H k Δ) := by
  have endAt := bank_end lo H k Δ j hj
  have upper : start lo H k Δ ≤ finish lo H k Δ := by unfold finish origin; omega
  exact ⟨span_pos _,by omega,endAt⟩

theorem headerFits (lo H k Δ : ℕ) (room : finish lo H k Δ < 2^w) :
    Fits (header lo H k Δ) w H k Δ (start lo H k Δ) := by
  have hN := (row_count (H:=H) (k:=k) (Δ:=Δ)).trans (span_ge (primingWords H k Δ))
  refine ⟨?_,?_,(site_count (H:=H) (k:=k) (Δ:=Δ)).trans hN,?_⟩
  · intro z hz
    simp only [header,Tape.banks,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl <;> exact bank_fits lo H k Δ room _ (by decide)
  · intro z hz
    simp only [header,Tape.fixed,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl <;> exact hN
  · change H*Δ ≤ span (primingWords H k Δ)
    omega

theorem before (lo H k Δ : ℕ) : Before (payload lo H k Δ) (start lo H k Δ) := by
  refine ⟨?_,rfl⟩
  intro z hz
  simp only [payload,fixedData,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl|rfl <;> exact bank_end lo H k Δ _ (by decide)

theorem dataFits (lo H k Δ : ℕ) (room : finish lo H k Δ < 2^w) :
    DataFits (payload lo H k Δ) w H k Δ (origin (start lo H k Δ) H k Δ) := by
  have p := span_pos (primingRows H k Δ)
  have endAt : start lo H k Δ + span (primingRows H k Δ) ≤ origin (start lo H k Δ) H k Δ := by
    have := span_le (primingRows H k Δ)
    unfold origin
    omega
  have live : (Bank.mk (start lo H k Δ) (Nat.clog 2 (primingRows H k Δ))).Fits w (origin (start lo H k Δ) H k Δ) := by
    change 0 < span (primingRows H k Δ) ∧ span (primingRows H k Δ) < 2^w ∧ _
    unfold finish at room
    exact ⟨p,by omega,endAt⟩
  have ordinary (j : ℕ) (hj : j < 11) : (bank lo (primingWords H k Δ) j).Fits w (origin (start lo H k Δ) H k Δ) := by
    have h := bank_fits lo H k Δ room j hj
    exact ⟨h.1,h.2.1,le_trans h.2.2 (by unfold origin; omega)⟩
  refine ⟨?_,?_,span_ge (primingRows H k Δ),?_,?_⟩
  · intro z hz
    simp only [payload,dataBanks,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl <;> first | exact live | exact ordinary _ (by decide)
  · intro z hz
    simp only [payload,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl <;> exact span_ge (primingWords H k Δ)
  · exact (Nat.mul_le_mul_right (2^k) (site_count (H:=H) (k:=k) (Δ:=Δ))).trans (span_ge (primingWords H k Δ))
  · exact (Nat.mul_le_mul_right (2^k) (show H*Δ ≤ (primingRows H k Δ) by omega)).trans (span_ge (primingWords H k Δ))

/-- Enumeration of all actual row/word fields, in native output address order. -/
def dataOrd (H k Δ : ℕ) : Rows H k Δ × Fin (2^k) ≃ Fin (primingWords H k Δ) :=
  ((rowOrd H k Δ).prodCongr (Equiv.refl _)).trans finProdFinEquiv

private def tabulate {n : ℕ} (f : Fin n → ℕ) (i : ℕ) : ℕ :=
  if h : i<n then f ⟨i,h⟩ else 0

private theorem tabulate_at {n : ℕ} (f : Fin n → ℕ) (i : Fin n) :
    tabulate f i.val = f i := by simp [tabulate,i.isLt]

/-- A missing literal selects the existing word of a mutable input column. -/
def literal (H k Δ f B K j i : ℕ) : Option ℕ :=
  let head := fun (g : (Rows H k Δ) → ℕ) => some (tabulate (g ∘ (rowOrd H k Δ).symm) i)
  let entry := fun (g : (Rows H k Δ) × Fin (2^k) → ℕ) => some (tabulate (g ∘ (dataOrd H k Δ).symm) i)
  match j with
  | 0 => head tag
  | 1 => head fun t => (owner t).val
  | 2 => head arg
  | 3 => head (tariff f B K)
  | 6 => entry fun p => (rowOrd H k Δ p.1).val
  | 7 => entry fun p => tag p.1
  | 8 => entry fun p => sourceAddress p.1 p.2
  | _ => none

def memory (lo H k Δ f B K : ℕ) (previous : Memory w) : Memory w :=
  initialMemory (start lo H k Δ) fun a =>
    if a < lo then previous a else
      let j := (a-lo)/span (primingWords H k Δ)
      let i := (a-lo)%span (primingWords H k Δ)
      match literal H k Δ f B K j i with
      | some wordValue => (wordValue : Word w)
      | none => previous a

theorem prefix_frame (lo H k Δ f B K : ℕ) (previous : Memory w) (a : ℕ) (low : a<lo) :
    memory lo H k Δ f B K previous a = previous a := by
  have high : a<start lo H k Δ := by unfold start; omega
  simp [memory,initialMemory,high,low]

private theorem cell (lo H k Δ f B K j i : ℕ) (previous : Memory w) (hj : j < 11) (hi : i < span (primingWords H k Δ)) :
    let a := (bank lo (primingWords H k Δ) j).base+i
    memory lo H k Δ f B K previous a =
      match literal H k Δ f B K j i with | some val => (val : Word w) | none => previous a := by
  let a := (bank lo (primingWords H k Δ) j).base+i
  have loA : lo ≤ a := by change lo ≤ lo+j*span (primingWords H k Δ)+i; omega
  have high : a < start lo H k Δ := by
    have h := bank_end lo H k Δ j hj
    change (bank lo (primingWords H k Δ) j).base+span (primingWords H k Δ) ≤ _ at h
    dsimp only [a]; omega
  have off : a-lo = j*span (primingWords H k Δ)+i := by change lo+j*span (primingWords H k Δ)+i-lo=_; omega
  have quo : (j*span (primingWords H k Δ)+i)/span (primingWords H k Δ) = j := by
    rw [Nat.mul_comm j (span (primingWords H k Δ)),Nat.mul_add_div (span_pos _),Nat.div_eq_of_lt hi,Nat.add_zero]
  have rem : (j*span (primingWords H k Δ)+i)%span (primingWords H k Δ)=i := Nat.mul_add_mod_of_lt hi
  change memory lo H k Δ f B K previous a=_
  simp only [memory,initialMemory,ite_eq_left high,ite_eq_right (Nat.not_lt.mpr loA),off,quo,rem]
  cases literal H k Δ f B K j i <;> rfl

/-- The seven directories are present in the current state, including their padded cells. -/
def Resident (lo H k Δ f B K : ℕ) (m : Memory w) : Prop :=
  ∀j < 11, ∀i < span (primingWords H k Δ), ∀v, literal H k Δ f B K j i = some v →
    m ((bank lo (primingWords H k Δ) j).base+i) = (v : Word w)

theorem memory_resident (lo H k Δ f B K : ℕ) (previous : Memory w) :
    Resident lo H k Δ f B K (memory lo H k Δ f B K previous) := by
  intro j hj i hi v hv
  simpa only [hv] using cell lo H k Δ f B K j i previous hj hi

theorem resident_of_frame (lo H k Δ f B K : ℕ) {m m' : Memory w}
    (old : Resident lo H k Δ f B K m)
    (keep : ∀j < 11, ∀i < span (primingWords H k Δ), (literal H k Δ f B K j i).isSome →
      m' ((bank lo (primingWords H k Δ) j).base+i) = m ((bank lo (primingWords H k Δ) j).base+i)) :
    Resident lo H k Δ f B K m' := by
  intro j hj i hi v hv
  exact (keep j hj i hi (by simp [hv])).trans (old j hj i hi v hv)

theorem prefix_fixed_iff (lo H k Δ f B K : ℕ) (previous : Memory w) :
    (∀a < start lo H k Δ, memory lo H k Δ f B K previous a = previous a) ↔
      Resident lo H k Δ f B K previous := by
  constructor
  · intro fixed j hj i hi v hv
    have e := bank_end lo H k Δ j hj
    change (bank lo (primingWords H k Δ) j).base+span (primingWords H k Δ) ≤ _ at e
    exact (fixed ((bank lo (primingWords H k Δ) j).base+i) (by omega)).symm.trans
      (memory_resident lo H k Δ f B K previous j hj i hi v hv)
  · intro loaded a ha
    by_cases low : a < lo
    · exact prefix_frame lo H k Δ f B K previous a low
    let j := (a-lo)/span (primingWords H k Δ)
    let i := (a-lo)%span (primingWords H k Δ)
    have hj : j < 11 := (Nat.div_lt_iff_lt_mul (span_pos (primingWords H k Δ))).mpr (by unfold start at ha; omega)
    have hi : i < span (primingWords H k Δ) := Nat.mod_lt _ (span_pos (primingWords H k Δ))
    have eqn : (bank lo (primingWords H k Δ) j).base+i = a := by
      have h : j*span (primingWords H k Δ)+i = a-lo := by
        simpa only [j,i,Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div (a-lo) (span (primingWords H k Δ))
      change lo+j*span (primingWords H k Δ)+i = a
      omega
    rw [← eqn]
    have val := cell lo H k Δ f B K j i previous hj hi
    cases hv : literal H k Δ f B K j i with
    | none => simpa only [hv] using val
    | some v =>
      simp only [hv] at val
      exact val.trans (loaded j hj i hi v hv).symm

/-- At initialization there are no live words above the initialized prefix. Later iterations use
`prefix_fixed_iff`, which also applies to states with a live suffix. -/
theorem memory_fixed_iff (lo H k Δ f B K : ℕ) (previous : Memory w)
    (suffix : ∀a, start lo H k Δ ≤ a → previous a = 0) :
    memory lo H k Δ f B K previous = previous ↔ Resident lo H k Δ f B K previous := by
  constructor
  · intro h
    exact (prefix_fixed_iff lo H k Δ f B K previous).mp fun a _ => congrFun h a
  · intro h
    funext a
    by_cases low : a < start lo H k Δ
    · exact (prefix_fixed_iff lo H k Δ f B K previous).mpr h a low
    · simp only [memory,initialMemory,ite_eq_right low,suffix a (Nat.le_of_not_gt low)]

private theorem header_size (t : (Rows H k Δ)) : (rowOrd H k Δ t).val < span (primingWords H k Δ) :=
  (rowOrd H k Δ t).isLt.trans_le (row_count.trans (span_ge (primingWords H k Δ)))

theorem contents_read (lo H k Δ f B K : ℕ) (previous : Memory w)
    (b : Fin H → ℕ) (next : Port H Δ → Option (Fin H))
    (depth : ∀v : Fin H, previous ((header lo H k Δ).depth.base+v.val)=(b v : Word w))
    (neighbor : ∀p : Port H Δ, previous ((header lo H k Δ).neighbor.base+(slot H Δ p).val)=
      (target (next p) : Word w)) :
    contents (k:=k) (header lo H k Δ) b next f B K (memory lo H k Δ f B K previous) := by
  have hN := (row_count (H:=H) (k:=k) (Δ:=Δ)).trans (span_ge (primingWords H k Δ))
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro t
    simpa [header,literal,tabulate_at] using cell lo H k Δ f B K 0 _ previous (by decide) (header_size t)
  · intro t
    simpa [header,literal,tabulate_at] using cell lo H k Δ f B K 1 _ previous (by decide) (header_size t)
  · intro t
    simpa [header,literal,tabulate_at] using cell lo H k Δ f B K 2 _ previous (by decide) (header_size t)
  · intro t
    simpa [header,literal,tabulate_at] using cell lo H k Δ f B K 3 _ previous (by decide) (header_size t)
  · intro v
    have hi := v.isLt.trans_le ((site_count (H:=H) (k:=k) (Δ:=Δ)).trans hN)
    exact (cell lo H k Δ f B K 4 _ previous (by decide) hi).trans (depth v)
  · intro p
    have hi := (slot H Δ p).isLt.trans_le ((show H*Δ ≤ (primingRows H k Δ) by omega).trans hN)
    exact (cell lo H k Δ f B K 5 _ previous (by decide) hi).trans (neighbor p)

theorem static_read (lo H k Δ f B K : ℕ) (previous : Memory w) :
    dataStatic (H:=H) (k:=k) (Δ:=Δ) (payload lo H k Δ) (memory lo H k Δ f B K previous) := by
  intro t d
  let i := dataOrd H k Δ (t,d)
  have hi := i.isLt.trans_le (span_ge (primingWords H k Δ))
  change memory _ _ _ _ _ _ _ _ ((bank lo (primingWords H k Δ) 6).base+i.val)=_ ∧
      memory _ _ _ _ _ _ _ _ ((bank lo (primingWords H k Δ) 7).base+i.val)=_ ∧
      memory _ _ _ _ _ _ _ _ ((bank lo (primingWords H k Δ) 8).base+i.val)=_
  constructor
  · simpa [i,literal,tabulate_at] using cell lo H k Δ f B K 6 i.val previous (by decide) hi
  constructor
  · simpa [i,literal,tabulate_at] using cell lo H k Δ f B K 7 i.val previous (by decide) hi
  · simpa [i,literal,tabulate_at] using cell lo H k Δ f B K 8 i.val previous (by decide) hi

theorem loads_read (lo H k Δ f B K : ℕ) (previous : Memory w)
    (site : Fin H → Fin (2^k) → ℕ) (traffic : Port H Δ → Fin (2^k) → ℕ)
    (prior : oldLoads (payload lo H k Δ) site traffic previous) :
    oldLoads (payload lo H k Δ) site traffic (memory lo H k Δ f B K previous) := by
  constructor
  · intro v z
    have endAt := Nat.mul_le_mul_right (2^k) (site_count (H:=H) (k:=k) (Δ:=Δ))
    have next := Nat.mul_le_mul_right (2^k) (show v.val+1 ≤ H from v.isLt)
    rw [Nat.succ_mul] at next
    have hi : v.val*2^k+z.val < span (primingWords H k Δ) := by have := span_ge (primingWords H k Δ); have := z.isLt; omega
    exact (cell lo H k Δ f B K 9 _ previous (by decide) hi).trans (prior.1 v z)
  · intro p z
    let j := slot H Δ p
    have endAt := Nat.mul_le_mul_right (2^k) (show H*Δ ≤ (primingRows H k Δ) by omega)
    have next := Nat.mul_le_mul_right (2^k) (show j.val+1 ≤ H*Δ from j.isLt)
    rw [Nat.succ_mul] at next
    have hi : j.val*2^k+z.val < span (primingWords H k Δ) := by have := span_ge (primingWords H k Δ); have := z.isLt; omega
    exact (cell lo H k Δ f B K 10 _ previous (by decide) hi).trans (prior.2 p z)

/-- The header scan can start directly in an evolved resident memory. -/
theorem resident_contents (lo H k Δ f B K : ℕ) (m : Memory w)
    (resident : Resident lo H k Δ f B K m) (b : Fin H → ℕ) (next : Port H Δ → Option (Fin H))
    (depth : ∀v : Fin H, m ((header lo H k Δ).depth.base+v.val)=(b v : Word w))
    (neighbor : ∀p : Port H Δ, m ((header lo H k Δ).neighbor.base+(slot H Δ p).val)=
      (target (next p) : Word w)) : contents (k:=k) (header lo H k Δ) b next f B K m := by
  refine ⟨?_,?_,?_,?_,depth,neighbor⟩
  · intro t
    apply resident 0 (by decide) _ (header_size t)
    simp [literal,tabulate_at]
  · intro t
    apply resident 1 (by decide) _ (header_size t)
    simp [literal,tabulate_at]
  · intro t
    apply resident 2 (by decide) _ (header_size t)
    simp [literal,tabulate_at]
  · intro t
    apply resident 3 (by decide) _ (header_size t)
    simp [literal,tabulate_at]

theorem resident_static (lo H k Δ f B K : ℕ) (m : Memory w)
    (resident : Resident lo H k Δ f B K m) : dataStatic (H:=H) (k:=k) (Δ:=Δ) (payload lo H k Δ) m := by
  intro t d
  let i := dataOrd H k Δ (t,d)
  have hi := i.isLt.trans_le (span_ge (primingWords H k Δ))
  refine ⟨?_,?_,?_⟩
  · apply resident 6 (by decide) i.val hi
    simp [i,literal,tabulate_at]
  · apply resident 7 (by decide) i.val hi
    simp [i,literal,tabulate_at]
  · apply resident 8 (by decide) i.val hi
    simp [i,literal,tabulate_at]

end
end Hierarchy.DescentMeasuredPriming

end OAI
