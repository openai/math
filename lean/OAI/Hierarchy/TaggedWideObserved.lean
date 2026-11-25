import OAI.Hierarchy.TaggedWideObservationCore
import OAI.Hierarchy.ProtocolRAMMachine
import OAI.Hierarchy.ProtocolRAMControl
import OAI.Hierarchy.ProtocolRAMVerdicts

namespace OAI
/-! # Summing the native history, all observed words and the tagged control sockets -/

noncomputable section
namespace Hierarchy.TaggedShorterControlHistory
open ThreeFlat Routing Diagonal TraceRows TraceBanks
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory
open scoped Classical BigOperators

/-- The return bit and the words used by every site must be read from
the same terminal memory. A rejected native run contributes zero. -/
theorem observed_accepting {F : Type*} [CommRing F] {W p r k S f u m a t : ℕ}
    (M : Machine W p r k) (ww : 3≤W+1) (hp : p≤2^(W+1)) (st : Word W)
    (addr : Fin u → Word W) (header : ℕ → Word W) (hs : S≤2^W)
    (clock : f+u≤2^(W+1)) (slots : S+(f+u)≤2^m) (positive : 0<a)
    (record : TaggedShorterHistoryOrder.RecordWidth (W+1)≤a*m)
    (done : Config W p r) (out : Memory W) (result : Option (Word W)) (fuel : t<f)
    (ran : RAM.advance M.program t (M.program.start st) (initialMemory S header)=some (done,out))
    (halt : M.program.step done=.finish result) (i : Fin u) (flag : ℕ)
    (atFlag : (addr i).val=flag) (accept : Prop) (flagZero : out flag=0 ↔ accept)
    (φ : (Fin u → Word (W+1)) → F) :
    observationSum (m:=m) a M ww hp st addr header hs clock (fun v=>if (v i).val=0 then φ v else 0) =
      if accept then φ (fun j=>wide (out (addr j).val)) else 0 := by
  classical
  have correct : (wide (out (addr i).val)).val=0 ↔ accept := by
    rw [atFlag]
    exact (show (out flag).val=0 ↔ out flag=0 by
      constructor
      · intro h; exact Fin.ext h
      · intro h; simp [h]).trans flagZero
  rw [observed_weight (F:=F) M ww hp st addr header hs clock slots positive record done out result fuel ran halt]
  simp only [correct]

open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM

/-- A running procedure supplies its actual post-state; adjoining its
three-instruction return tail preserves all observed cells. -/
theorem observed_of_exec {F : Type*} [CommRing F] {w S f u budget m a : ℕ}
    (A : Procedure w) (flag st : Word w) (addr : Fin u → Word w)
    (header : ℕ → Word w) (out : Memory w) (exec : A.Exec (initialMemory S header) out budget)
    (hw : 3≤w+1) (hp : A.labels+3≤2^(w+1)) (hs : S≤2^w)
    (clockFit : f+u≤2^(w+1)) (fits : S+(f+u)≤2^m) (positive : 0<a)
    (room : TaggedShorterHistoryOrder.RecordWidth (w+1)≤a*m) (fuel : budget+2<f)
    (φ : (Fin u → Word (w+1)) → F) :
    observationSum (m:=m) a (machine A flag) hw hp st addr header hs clockFit φ =
      φ (fun i => wide (out (addr i).val)) := by
  obtain ⟨t,within,done,ran,halt⟩ := machine_run A flag st _ out budget exec
  exact observed_weight _ hw hp st addr header hs clockFit fits positive room done out _
    (within.trans_lt fuel) ran halt φ

/-- A reporter runs on the live adaptive outcome. Its input memory is
supplied by the verified prefix execution from the very same physical
header that appears in the CPU verifier. -/
theorem observed_after {F : Type*} [CommRing F] {w S f u first last m a : ℕ}
    (P A : Procedure w) (flag st : Word w) (addr : Fin u → Word w)
    (header : ℕ → Word w) (staged out : Memory w)
    (prefixRun : P.Exec (initialMemory S header) staged first) (reportRun : A.Exec staged out last)
    (hw : 3≤w+1) (hp : (P.seq A).labels+3≤2^(w+1)) (hs : S≤2^w)
    (clockFit : f+u≤2^(w+1)) (fits : S+(f+u)≤2^m) (positive : 0<a)
    (room : TaggedShorterHistoryOrder.RecordWidth (w+1)≤a*m) (fuel : (first+last)+2<f)
    (φ : (Fin u → Word (w+1)) → F) :
    observationSum (m:=m) a (machine (P.seq A) flag) hw hp st addr header hs clockFit φ =
      φ (fun i => wide (out (addr i).val)) :=
  observed_of_exec (P.seq A) flag st addr header out (prefixRun.then reportRun)
    hw hp hs clockFit fits positive room fuel φ

open DescriptorExpr

/-- Applying the native controller's own execution theorem yields all endpoint,
menu, ID and output-flag cells from its reported memory without a correctness
assumption about the terminal image. -/
theorem observed_controller {F : Type*} [CommRing F] {w S f u m a : ℕ}
    (src dst n : ℕ) (owners : Bank) (phases : List Pass) (fields : Fin 7 → Expr)
    (flag st : Word w) (addr : Fin u → Word w) (header : ℕ → Word w)
    (good : ∀ pass ∈ phases, pass.Fits w) (wideW : 3<w)
    (dir : Owners owners n (result phases (initialMemory S header)))
    (inputFits : (packed owners fields).Fits w src) (srcFit : src+8*n<2^w)
    (dstFit : dst+9*n<2^w) (apart : src+8*n≤dst ∨ dst+9*n ≤ src)
    (hp : (controller w src dst n owners phases fields).labels+3≤2^(w+1)) (hs : S≤2^w)
    (clockFit : f+u≤2^(w+1)) (fits : S+(f+u)≤2^m) (positive : 0<a)
    (room : TaggedShorterHistoryOrder.RecordWidth (w+1)≤a*m)
    (fuel : ((clock phases+(report src n owners fields).clock)+(27+117*n))+2<f)
    (φ : (Fin u → Word (w+1)) → F) :
    observationSum (m:=m) a (machine (controller w src dst n owners phases fields) flag)
      (by omega) hp st addr header hs clockFit φ =
      φ (fun i => wide (finalMemory src dst n owners phases fields (initialMemory S header) (addr i).val)) := by
  have exec : (controller w src dst n owners phases fields).Exec (initialMemory S header)
      (finalMemory src dst n owners phases fields (initialMemory S header))
      ((clock phases+(report src n owners fields).clock)+(27+117*n)) :=
    controller_exec src dst n owners phases fields (initialMemory S header) good wideW dir inputFits srcFit dstFit apart
  exact observed_of_exec _ flag st addr header _ exec (by omega) hp hs clockFit fits positive room fuel φ

/-- Reading the actual terminal tally multiplies the downstream site scalar
by exactly the native all-greedy-batches-admitted condition. -/
theorem observed_verdict {F : Type*} [CommRing F] {w S f u m a : ℕ}
    (ss : List Audit) (flag : ℕ) (st : Word w) (addr : Fin u → Word w) (header : ℕ → Word w)
    (i : Fin u) (observes : (addr i).val=flag)
    (ok : AuditReady ss (initialMemory S header)) (order : OrderedTallies ss)
    (inputs : (verdict ss).Fits w flag) (space : flag+1<2^w) (hw : 3≤w+1)
    (hp : (finalVerdict w flag ss).labels+3≤2^(w+1)) (hs : S≤2^w)
    (clockFit : f+u≤2^(w+1)) (fits : S+(f+u)≤2^m) (positive : 0<a)
    (room : TaggedShorterHistoryOrder.RecordWidth (w+1)≤a*m)
    (fuel : (auditTicks ss+(4+1*(2*(verdict ss).work+4)))+2<f)
    (φ : (Fin u → Word (w+1)) → F) :
    observationSum (m:=m) a (machine (finalVerdict w flag ss) (addr i)) hw hp st addr header hs clockFit
      (fun obs => if (obs i).val=0 then φ obs else 0) =
      if AllAdmitted ss (initialMemory S header) then
        φ (fun j => wide (verdictMemory flag ss (initialMemory S header) (addr j).val)) else 0 := by
  classical
  let mem := initialMemory S header
  have exec : (finalVerdict w flag ss).Exec mem (verdictMemory flag ss mem)
      (auditTicks ss+(4+1*(2*(verdict ss).work+4))) :=
    finalVerdict_exec ss flag mem ok inputs space
  have zero : (wide (verdictMemory flag ss mem (addr i).val)).val=0 ↔ AllAdmitted ss mem := by
    rw [observes]
    exact (show (verdictMemory flag ss mem flag).val=0 ↔ verdictMemory flag ss mem flag=0 by
      constructor
      · intro h; exact Fin.ext h
      · intro h; simp [h]).trans (finalVerdict_flag ss flag mem ok order (by omega))
  rw [observed_of_exec (F:=F) _ _ st addr header _ exec hw hp hs clockFit fits positive room fuel]
  exact if_congr zero rfl rfl

end Hierarchy.TaggedShorterControlHistory

end
end OAI
