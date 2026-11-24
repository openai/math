import OAI.Computability.VPVNP.CompressorRecordRefreshBuild

/-!
# Retaining an earlier refresh level for the history traversal

The old segment columns, dense demands and selected term descriptors occupy the interval
from the allocation start up to the selected-supply column. Agreement on this interval
transfers every refresh field required by a later depth-first traversal.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.Build

open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh SpectralGeometry
open NewSlots RefreshRAM Allocation

variable {bits a a₀ g dH t : ℕ} {k : Type*} [_root_.Field k] {K K' : ℝ}
  {X : State a (a+g)} {E : RegularArcGraph (Fin (2^a)) dH} {hdH : 0 < dH}
  {conn : (arcSupportGraph E.multiplicity).Connected}
  {F : RefreshBlock k (expanderSupply E hdH conn) (2^a₀) K K'}
  {choice : DyadicRefreshChoice X E hdH conn F}
  {ties : Fin t ≃ Tie (2^a)} {start stride : ℕ} {m m' : Memory bits}

local notation "P" => plan X a₀ dH t stride start
local notation "Q" => Plan.scratch P bits
local notation "B" => Fintype.card X.Base * 2^g
local notation "S" => Fintype.card X.Base * 2^a * 2^g * 2^a
local notation "demandBase" => word (bits := bits) (Plan.demand P)
local notation "termBase" => word (bits := bits) (Plan.term P)

/-- A later memory contains the same segment rows, demands, grid and repetition
headers, and payload coordinates whenever it agrees on their allocated interval. -/
theorem Stored.transfer {fit : S ≤ 2^bits} (data : Stored X E hdH conn F choice ties start stride fit m)
    (wide : 2+2^a*dH ≤ stride) (room : (P).stop ≤ 2^bits)
    (same : ∀ addr, start ≤ addr → addr < (P).supply → m' addr = m addr) :
    Stored X E hdH conn F choice ties start stride fit m' := by
  have capPos : 0 < (P).capacity := by change 0 < Fintype.card X.Base*2^a*2^g*2^a₀; positivity
  have upto : (P).supply < 2^bits := by
    dsimp only [Plan.stop,Plan.next,Plan.reverseSlot,Plan.targetPort] at room; omega
  have h₀ : start ≤ (P).demand := Nat.le_add_right ..
  have h₁ : (P).demand+B*t = (P).term := rfl
  have h₂ : (P).term+B*stride = (P).supply := rfl
  have db : (demandBase).val = (P).demand := Nat.mod_eq_of_lt (by omega)
  have tb : (termBase).val = (P).term := Nat.mod_eq_of_lt (by omega)
  have terms (s : X.Base × BitWord g) :
      start ≤ (SupplyScan.recordBase X termBase stride s).val ∧
      (SupplyScan.recordBase X termBase stride s).val+stride ≤ (P).supply := by
    let i := (DemandScan.blocks X s).val
    have step := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt (DemandScan.blocks X s).isLt)
    rw [Nat.succ_mul] at step
    have inside : (P).term+i*stride < 2^bits := by dsimp only [i]; omega
    have head : (SupplyScan.recordBase X termBase stride s).val = (P).term+i*stride := by
      rw [SupplyScan.recordBase,← DemandScan.blocks_val,Fin.val_add,Fin.val_mul,tb]
      change ((P).term + ((i % 2^bits * (stride % 2^bits)) % 2^bits)) % 2^bits = _
      rw [Nat.mod_mul_mod,Nat.mul_mod_mod,Nat.add_mod_mod,Nat.mod_eq_of_lt inside]
    rw [head]; dsimp only [i]; constructor <;> omega
  constructor
  · apply SegmentFields.transfer X Q data.segments
    intro c hc i hi
    obtain ⟨lower,upper⟩ := (P).scratch_interval (by omega : (P).demand ≤ 2^bits) c hc i hi
    exact same _ lower (by omega)
  · intro s
    funext e
    let i := (DemandScan.blocks X s).val
    have step := Nat.mul_le_mul_right t (Nat.succ_le_of_lt (DemandScan.blocks X s).isLt)
    rw [Nat.succ_mul] at step
    have inside : (P).demand+i*t < 2^bits := by dsimp only [i]; omega
    have head : (DemandScan.rowBase X t demandBase s).val = (P).demand+i*t := by
      rw [DemandScan.rowBase,Fin.val_add,db,Fin.val_ofNat,Nat.add_mod_mod,Nat.mod_eq_of_lt inside]
    obtain ⟨j,rfl⟩ := ties.surjective e
    have fits := DemandScan.rowBase_fits X demandBase (by rw [db]; omega : (demandBase).val+B*t ≤ 2^bits) s
    have cell := DemandPreparation.demandAt_address ties (DemandScan.rowBase X t demandBase s) m fits j
    have cell' := DemandPreparation.demandAt_address ties (DemandScan.rowBase X t demandBase s) m' fits j
    rw [cell',same _ (by rw [head]; omega) (by rw [head]; dsimp only [i]; have := j.isLt; omega),← cell,data.demands]
  · refine ⟨data.terms.fits,fun s => ?_,fun s e => ?_⟩
    · obtain ⟨lo,hi⟩ := terms s
      rw [same _ (by omega) (by omega)]
      exact data.terms.repetitions s
    · obtain ⟨lo,hi⟩ := terms s
      have h := Nat.mul_le_mul_right dH e.1.isLt
      rw [Nat.succ_mul] at h
      have hk := e.2.isLt
      rw [same _ (by omega) (by omega)]
      exact data.terms.payload s e
  · intro s
    obtain ⟨lo,hi⟩ := terms s
    refine ⟨?_,?_,fun j => ?_⟩
    · rw [same _ lo (by omega)]; exact (data.readback s).1
    · rw [same _ (by omega) (by omega)]; exact (data.readback s).2.1
    · rw [same _ (by omega) (by have := j.isLt; omega)]; exact (data.readback s).2.2 j

end CompressorRecords.PortRefresh.Build

end VPVNP
end Computability
end OAI
