import OAI.Computability.VPVNP.CompressorTermWorkerScan
import OAI.Computability.VPVNP.CompressorRecordsOrdinalRun
import OAI.Computability.VPVNP.CompressorRecordsOnline

/-!
# Fused term scans in the guarded descriptor dispatcher

The term writes stay in a single strided row at each reset. A dispatch frame
outside those rows therefore remains ready through the exclusive motif count.
The closing guard transfers to the level calendar.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.TermWorker

open BurstRAM TermRecordScan MotifGrid MotifBlocks MotifConversion MotifSelector Schedule OrdinalRun
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {J D S : Type} [Fintype J] [Fintype D] [Fintype S]
variable {a b : D → J} {P : Supply J S} {p : D → ℚ} {q : S → ℚ} {H H' : ℝ}
variable (B : FixedBlock k a b P (realWidths p) (realWidths q) H H')
variable {d n : ℕ} (order : Fin d ≃ D) (supply : Fin n ≃ S) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)

/-- Fixed word-width allowance used to prove that a successful call writes only its selected
term row. -/
noncomputable def frameFit : ℕ := (call_frame B order supply hp hq).choose

variable {m w workers M fuel : ℕ} (C : Catalog workers) (worker : Fin workers) (ports : Schedule.Ports w)
  (pub : Fin (C worker).params → BurstRAM.Word w) (L : Layout m d n w) (addr : Fin 4 → BurstRAM.Word w)
  (haddr : Addresses L addr) (demand : Fin m → D → ℕ) (hD : ∀ i e, demand i e ≤ M)
  (hW : frameFit B order supply hp hq + 4*Nat.clog 2 (M+1) ≤ w)
  (hcap : budget B d n w M ≤ fuel) (hstop : m < 2^w)
  (apart : ∀ i x, ControlCell (C worker).params ports x → L.Outside i x)
  (mem : Memory w) (hin : Inputs order L demand mem)
  (ready : Schedule.Ready C worker ports pub (m : BurstRAM.Word w) mem)
  (bits : List (List Bool)) (rs : List (Report w)) (size : bits.length = m)
  (run : runSegment (program B order supply addr) fuel (some 0) mem bits = some rs)

include haddr hD hW hcap hstop apart hin ready size run in
theorem valid_trace :
    ValidTrace C worker ports pub (m : BurstRAM.Word w) 0 mem rs ∧
      Inputs order L demand (after mem (eventLog rs)) ∧
      Preserved (C worker).params ports mem (after mem (eventLog rs)) := by
  have step := (call_frame B order supply hp hq).choose_spec m M w hW L addr haddr demand hD fuel hcap
  let cursor (j : ℕ) : BurstRAM.Word w := j
  have active (j : ℕ) (hj : j < m) : cursor j < cursor m := by
    change j%(2^w) < m%(2^w)
    simpa only [Nat.mod_eq_of_lt (hj.trans hstop),Nat.mod_eq_of_lt hstop] using hj
  apply OrdinalRun.validTrace C worker ports (program B order supply addr) fuel pub (cursor m) cursor m
    (fun _ x => Inputs order L demand x) active le_rfl _ 0 bits mem rs (by omega) hin ready run
  intro j hj x inv bs rep he
  let i : Fin m := ⟨j,hj⟩
  obtain ⟨inc,next,frame,_,_⟩ := step x inv i bs rep he
  exact ⟨inc,next,fun u hu => frame u (apart i u hu)⟩

/-- Public operands of a catalog slot whose instruction table is the fixed
motif worker. The cast accounts for the slot's dependent arity. -/
noncomputable def catalogWords (passEq : C worker = motifPass B order n) : Fin (C worker).params → BurstRAM.Word w :=
  fun i => motifData B order supply w addr (i.cast (congrArg Schedule.Pass.params passEq))

private theorem run_catalog {W : Schedule.Pass} (eq : W = motifPass B order n) (f : ℕ)
    (mem : Memory w) (bs : List (List Bool)) :
    runSegment (W.table.instantiate w (fun i => motifData B order supply w addr (i.cast (congrArg Schedule.Pass.params eq)))).program
      f (some 0) mem bs = runSegment (program B order supply addr) f (some 0) mem bs := by
  subst W
  rfl

variable {initial phases cap : ℕ} (plan : Online.Config C initial phases) (passEq : C worker = motifPass B order n)

include haddr hD hW hcap hstop apart hin size run in
/-- Execute the whole term pass under the online tag reader, including the
closing transfer and arbitrary subsequent calendar calls. -/
theorem online_segment (prepared : Schedule.Ready C worker ports (catalogWords B order supply C worker addr passEq)
    (m : BurstRAM.Word w) mem) (tagFit : Online.N workers (initial+phases) ≤ 2^w)
    (clock : fuel+3+4*((C worker).params+1)+2*Online.N workers (initial+phases)+5 ≤ cap)
    (tail : List (List Bool)) :
    let T := Online.program plan ports
    let finalMem := after mem (eventLog rs)
    runSegment T cap (some 0) mem (bits ++ [] :: tail) =
      (runSegment T cap (some 0) (writeMemory finalMem ports.tag
        (LiveStageLink.tagWord w (Online.calendarIndex workers (initial+phases)))) tail).map
        (fun more => Online.workerRows C (initial+phases) ports worker mem rs ++
          Online.stopReport C (initial+phases) ports worker finalMem :: more) := by
  have valid := valid_trace B order supply hp hq C worker ports _ L addr haddr demand hD hW hcap hstop apart
    mem hin prepared bits rs size run
  have original := (run_catalog B order supply addr passEq fuel mem bits).trans run
  have positive : 0 < fuel := by unfold budget at hcap; omega
  exact Online.worker_segment plan ports worker _ (m : BurstRAM.Word w) 0 mem bits rs fuel cap positive
    tagFit clock original valid.1 tail

end CompressorRecords.TermWorker

end VPVNP
end Computability
end OAI
