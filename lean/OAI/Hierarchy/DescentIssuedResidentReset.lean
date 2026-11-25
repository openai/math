import OAI.Hierarchy.DescentIssuedEmittedReset
import OAI.Hierarchy.DescentMeasuredDepthReceipt
import OAI.Hierarchy.DescentResetEstimatorBits

namespace OAI
/-! # Native previous measurements through smoothed depths to the exact
input memory of the installed mixer -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler DescentGL DescentColonies DescentBaseProfile DescentPackedExchange
open DescentBaseVariance DescentIntegerScale DescentMeasuredHeader DescentMeasuredWeights
open DescentRotor StarKeys Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable (A : GroupStage W G q ε J V k)
variable {m size w : ℕ} (digits : Block m≃J×Block k) (idx : V≃Fin size)
local notation "hdr₀" => A.mixerHeader digits idx
local notation "full" => A.wire*(A.z*G.b)*A.cap

theorem slot_matches (p : Port size A.degree) :
    neighborSlot idx A.mutual p=((hdr₀).neighbors[p.1.val])[p.2.val]? := by
  let ns:=A.mutual (idx.symm p.1)
  have len : ((ns.map idx.toEmbedding).sort (·≤·)).length=Fintype.card ns := by simp
  simp only [mixerHeader, Vector.getElem_ofFn] at *
  change neighborSlot idx A.mutual p=((ns.map idx.toEmbedding).sort (·≤·))[p.2.val]?
  unfold neighborSlot
  by_cases live : p.2.val<Fintype.card ns
  · rw [List.getElem?_eq_getElem (by omega : p.2.val<((ns.map idx.toEmbedding).sort (·≤·)).length)]
    simpa only [ns,dite_eq_left live] using congrArg some (neighborOrder_read idx ns ⟨p.2.val,live⟩)
  · rw [List.getElem?_eq_none (by omega : ((ns.map idx.toEmbedding).sort (·≤·)).length≤p.2.val)]
    exact dite_eq_right live

variable (lo f K scratch : ℕ)
local notation "start₀" => DescentMeasuredPriming.start lo size m A.degree
local notation "hd" => DescentMeasuredPriming.header lo size m A.degree
local notation "dt" => DescentMeasuredPriming.payload lo size m A.degree
local notation "L" => DescentMeasuredPriming.Depth.layout lo size m A.degree f k full scratch
local notation "now" => DescentMeasuredPriming.Depth.memory (H:=size) (k:=m) (Δ:=A.degree) lo f k full scratch
local notation "b" => (hdr₀).depth A f

theorem measured_from_old {payloadBits gainBits : ℕ} (mem : Memory w) (flow : Port size A.degree→Block m→ℕ)
    (ahead : start₀≤ scratch) (room : (L).base (m-f+2)<2^w)
    (headerRoom : DescentMeasuredPriming.finish lo size m A.degree<2^w)
    (endRoom : endAddress start₀ size m A.degree<2^w) (dim : size<2^w) (age : 2*m+1<2^w)
    (decay : decayExponent A.degree<2^w) (fr : f≤k) (km : k≤ m)
    (old : DescentMeasuredPriming.Resident lo size m A.degree f full K mem)
    (peers : ∀p : Port size A.degree,mem ((hd).neighbor.base+(slot size A.degree p).val)=(target (neighborSlot idx A.mutual p):Word w))
    (loads : oldLoads dt (fun v=>A.resetLoad digits (idx.symm v)) flow mem)
    (ports : ∀c : Contacts A.mutual,flow (atPort idx A.mutual A.mutualDegree c)=A.resetFlow digits c.1 c.2.val)
    (totals : ∀v,Native.totalWeight (hdr₀).loads v<2^w)
    (widths : payloadBits≤w ∧ gainBits≤w) (scores : 2^f*full*rateCap m K<2^gainBits)
    (site : ∀v z,A.measuredSiteRow digits v z<2^payloadBits)
    (flowRoom : ∀c z,A.measuredContactRow digits c z<2^payloadBits) :
    (DescentMeasuredPriming.Depth.text lo size m A.degree f k full scratch w).Exec mem (now mem)
      ((L).clocks w (m-f)+(6+5*size)) ∧
    A.MeasuredMemory (f:=f) (K:=K) (start:=start₀) (payloadBits:=payloadBits) (gainBits:=gainBits)
      hdr₀ hd dt flow (now mem) := by
  have load_eq : measuredLoad (hdr₀).loads = fun v=>A.resetLoad digits (idx.symm v) := by
    funext v z
    simp only [mixerHeader,measuredLoad,Vector.getElem_ofFn]
    rfl
  have sourceLoads : oldLoads dt (measuredLoad (hdr₀).loads) flow mem := by rw [load_eq]; exact loads
  obtain ⟨run,hdr,«meta»,oldData⟩:=DescentMeasuredPriming.Depth.receipt lo f k full K scratch mem
    (hdr₀).neighbors (hdr₀).loads (neighborSlot idx A.mutual) flow (A.slot_matches digits idx) ahead room
    ⟨decay,by omega⟩ headerRoom old peers sourceLoads totals (hdr₀).degree
  have hk (v : V) : b v≤ m := by
    let seed:=Native.seeds (hdr₀).loads (2^f*full) (m-k) (m-f)
    have small (u : Fin size) : seed[u.val]≤ m := by
      have h:=DepthRAM.Layout.probe_depth (Native.totalWeight (hdr₀).loads u) (m-f) 0 (2^f*full)
      simp only [seed, Native.seeds, Vector.getElem_ofFn]
      exact max_le (Nat.sub_le m k) (h.trans (by omega))
    change (Native.sweeps _ seed _ _)[(idx v).val]≤ m
    exact (Native.sweeps_read (H:=size) (hdr₀).neighbors seed (decayExponent A.degree) (m-f) (idx v)).le.trans
      (relax_le _ small _ _ _)
  refine ⟨run,DescentMeasuredPriming.headerFits _ _ _ _ headerRoom,
    DescentMeasuredPriming.dataFits _ _ _ _ headerRoom,DescentMeasuredPriming.before ..,
    endRoom,dim,age,?_,«meta»,?_,ports,widths,?_⟩
  · have depth_eq : b ∘ (hdr₀).site.symm = measuredDepth (hdr₀).neighbors (hdr₀).loads A.degree k f full := by
      funext u
      exact congrArg (measuredDepth (hdr₀).neighbors (hdr₀).loads A.degree k f full)
        (idx.apply_symm_apply u)
    rw [depth_eq]
    exact hdr
  · rw [load_eq] at oldData
    exact oldData
  · exact padded_bounds b _ f full K w gainBits payloadBits _ _ hk (by omega) scores site flowRoom

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
