import OAI.Hierarchy.ProtocolRAMTurnRead
import OAI.Hierarchy.ProtocolRAMTurnShelf

namespace OAI
/-! # Installing the true adjacent itinerary visits in fixed physical gate seats -/

noncomputable section
namespace Hierarchy.ProtocolRAMTurnInstalled
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM ProtocolRAMTurnItinerary
open scoped Fin.CommRing

variable {N sites slots W history occ edges : ℕ}

def columns (r : Fin N→Turn) (v : Values) (i : Fin N) := (r i).field v

def program (W N sites slots src base scratch sink : ℕ) (p : Chart) (b : Banks)
    (A : ProtocolRAMTurnShelf.Tables) : Procedure W :=
  (ProtocolRAMTurnItinerary.program W src N p b).seq (ProtocolRAMTurnShelf.program W N sites slots base scratch sink A)

/-- Install any concrete itinerary gather whose width words are authentic on all rows
and whose remaining fields are authentic on live rows. -/
theorem run_from (src sb rom rb base scratch sink : ℕ) (gather : Procedure W) (time : ℕ)
    (col : Fin N→Fin 7→ℕ) (m : Memory W)
    (observed : ∃ mid,gather.Exec m mid time ∧ ProtocolRAMTurnShelf.Source mid src col ∧
      ∀ t,t<src ∨ src+7*N≤t → mid t=m t)
    (put : ProtocolRAMTurnShelf.Live col ↪ ProtocolRAMTurnShelf.Seats sites slots)
    (loc : ∀ u : ProtocolRAMTurnShelf.Live col,
      (put u).1.val=col u.val 5 ∧ (put u).2.val=col u.val 6)
    (romLow : rom+4*2^rb≤ src)
    (directory : ∀ (j : Fin 4) (t : ℕ),t<2^rb →
      (ProtocolRAMTurnDirectory.bank rom rb j).read m (t:Word W)=
        ProtocolRAMTurnDirectory.words N sites slots base j t)
    (romRows : N*5≤2^rb) (romSites : sites≤2^rb) (cap : 5*N≤2^sb)
    (Wroom : 2^sb≤2^W) (widthFit : ∀ i,col i 4<2^W)
    (before : base+5*(sites*slots)≤ scratch) (scratchFit : scratch+(N*5)+(N*5)<2^W)
    (sinkLow : sink<base)
    (af : (ProtocolRAMTurnShelf.addressExpr (ProtocolRAMTurnShelf.tables rom rb src sb N) sink).Fits W base)
    (vf : (ProtocolRAMTurnShelf.valueExpr (ProtocolRAMTurnShelf.tables rom rb src sb N)).Fits W base) :
    let A := ProtocolRAMTurnShelf.tables rom rb src sb N
    ∃ out,(gather.seq (ProtocolRAMTurnShelf.program W N sites slots base scratch sink A)).Exec m out
        (time+(15+30*(sites*slots)+740*N)) ∧
      (∀ (f : Fin 5) (s : ProtocolRAMTurnShelf.Seats sites slots),
        out (base+f.val*(sites*slots)+s.1.val*slots+s.2.val) = ProtocolRAMTurnShelf.entry col put f s) ∧
      ∀ t,(t<src ∨ src+7*N≤t) → (t<base ∨ base+5*(sites*slots)≤t) →
        (t<scratch ∨ scratch+(N*5)+(N*5)≤t) → t≠sink → out t=m t := by
  intro A
  obtain ⟨mid,gatherExec,data,frame⟩ := observed
  have frozen (j : Fin 4) (t : ℕ) (ht : t<2^rb) :
      (ProtocolRAMTurnDirectory.bank rom rb j).read mid (t:Word W)=
        ProtocolRAMTurnDirectory.words N sites slots base j t := by
    refine Eq.trans ?_ (directory j t ht)
    apply frame
    left
    change rom+j.val*2^rb+(t:Word W).val%2^rb<src
    have a := Nat.mod_lt (t:Word W).val (Nat.two_pow_pos rb)
    have b := Nat.mul_le_mul_right (2^rb) j.isLt
    rw [Nat.succ_mul] at b
    omega
  obtain ⟨out,write,read,last⟩ := ProtocolRAMTurnShelf.run rom rb src sb base scratch sink mid col
    put loc data frozen romRows romSites cap Wroom widthFit before scratchFit sinkLow af vf
  rw [ProtocolRAMTurnShelf.work] at write
  refine ⟨out,?_,read,fun t a b c d=>(last t b c d).trans (frame t a)⟩
  intro P R K M pc reg pub exit installed publicData cfg mem start eq
  exact Procedure.Exec.then gatherExec write M pc reg pub exit installed publicData cfg mem start eq

/-- A single CPU prefix reads both actual itinerary sides, compiles their roles/weighted
starts and width, and publishes the five prescribed words at each live paid site/seat. -/
theorem run (src sb rom rb base scratch sink : ℕ) (p : Chart) (b : Banks)
    (r : Fin N→Turn) (v : Values) (m : Memory W)
    (rd : p.Reads r m) (banks : b.Reads v history occ edges m)
    (fit : ∀ i,(r i).Fits v W history occ edges) (one : 1<2^W)
    (fields : ∀ j,(field p b j).Fits W src) (fieldRoom : src+7*N<2^W)
    (put : ProtocolRAMTurnShelf.Live (columns r v) ↪ ProtocolRAMTurnShelf.Seats sites slots)
    (loc : ∀ u : ProtocolRAMTurnShelf.Live (columns r v),
      (put u).1.val=(r u.val).site ∧ (put u).2.val=(r u.val).seat)
    (romLow : rom+4*2^rb≤ src)
    (directory : ∀ (j : Fin 4) (t : ℕ),t<2^rb →
      (ProtocolRAMTurnDirectory.bank rom rb j).read m (t:Word W)=
        ProtocolRAMTurnDirectory.words N sites slots base j t)
    (romRows : N*5≤2^rb) (romSites : sites≤2^rb) (cap : 5*N≤2^sb)
    (Wroom : 2^sb≤2^W) (widthFit : ∀ i,(r i).width<2^W)
    (before : base+5*(sites*slots)≤ scratch) (scratchFit : scratch+(N*5)+(N*5)<2^W)
    (sinkLow : sink<base)
    (af : (ProtocolRAMTurnShelf.addressExpr (ProtocolRAMTurnShelf.tables rom rb src sb N) sink).Fits W base)
    (vf : (ProtocolRAMTurnShelf.valueExpr (ProtocolRAMTurnShelf.tables rom rb src sb N)).Fits W base) :
    let A := ProtocolRAMTurnShelf.tables rom rb src sb N
    ∃ out,(program W N sites slots src base scratch sink p b A).Exec m out
        (ticks src N p b + (15+30*(sites*slots)+740*N)) ∧
      (∀ (f : Fin 5) (s : ProtocolRAMTurnShelf.Seats sites slots),
        out (base+f.val*(sites*slots)+s.1.val*slots+s.2.val) = ProtocolRAMTurnShelf.entry (columns r v) put f s) ∧
      ∀ t,(t<src ∨ src+7*N≤t) → (t<base ∨ base+5*(sites*slots)≤t) →
        (t<scratch ∨ scratch+(N*5)+(N*5)≤t) → t≠sink → out t=m t := by
  intro A
  obtain ⟨mid,gather,arr,width,frame⟩ := observed p b r v m rd banks fit one fields fieldRoom
  have data : ProtocolRAMTurnShelf.Source mid src (columns r v) := by
    intro i f read
    rcases read with rfl|nz
    · exact width i
    · have within : (r i).position≤(r i).length := by
        by_contra! outside
        simp [columns,Turn.field,outside] at nz
      exact arr i f within
  have bounds (i : Fin N) : columns r v i 4<2^W := by
    change (if (r i).length < (r i).position then 0 else (r i).width)<2^W
    split <;> first | exact Nat.two_pow_pos _ | exact widthFit i
  exact run_from src sb rom rb base scratch sink (ProtocolRAMTurnItinerary.program W src N p b)
    (ticks src N p b) (columns r v) m ⟨mid,gather,data,frame⟩ put loc romLow directory
    romRows romSites cap Wroom bounds before scratchFit sinkLow af vf

end Hierarchy.ProtocolRAMTurnInstalled

end
end OAI
