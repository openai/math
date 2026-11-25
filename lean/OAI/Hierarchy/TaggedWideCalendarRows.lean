import OAI.Hierarchy.TaggedWideRetainedSite
import OAI.Hierarchy.TaggedWideControlBoard
import OAI.Hierarchy.TaggedWideControlGateEval
import OAI.Hierarchy.ProtocolRAMCalendarMesh

namespace OAI
/-! # One fixed family of dated local site programs with native selector words -/

noncomputable section
namespace Hierarchy.WireTelescope.PassMatrix
open ThreeFlat Routing Diagonal TraceWords
open LinearAlgebra.SpectralBooks ChordGraph
open Tagged Tagged.WideControlJoin ProtocolRAM.Calendar ProtocolRAM.SiteScatter Computability.VPVNP.BurstRAM
open scoped Classical BigOperators
variable {F : Type} [Field F] {Ex Sel D : Type} [Fintype Ex] [Fintype Sel] [Fintype D] (B : Gate)
    {S formats digits : ℕ} (fit : formats+1≤2^digits)
local notation "V" => SitePins Ex Sel D B
local notation "Net" => BitNetwork F (Fintype.card V)

/-- The mode field comes only from the paid machine's frozen native observation. -/
def modePin (address : Attempt→Fin S→Fin B.u) (low : digits≤B.W+1) (a : Attempt) (s : Fin S)
    (j : Fin digits) : V := .inr (.inr (.inr (address a s,j.castLE low)))

variable (address : Attempt→Fin S→Fin B.u) (low : digits≤B.W+1)
    (carry : Attempt→Fin S→Net) (packet : Attempt→Fin S→Fin formats→Net)
    (feed : Boundary→Fin S→Net)

/-- Installation depends only on the public list of attempt/feed dates. A
retained attempt selects its finite party packet on top of the passive-site
table. Each feed has its own original deterministic local program. -/
def dateProgram (fit : formats+1≤2^digits) (address : Attempt→Fin S→Fin B.u)
    (low : digits≤B.W+1) (carry : Attempt→Fin S→Net) (packet : Attempt→Fin S→Fin formats→Net)
    (feed : Boundary→Fin S→Net) (s : Fin S) : Event→Net
  | .attempt a=>dated (carry a s) (packet a s) (modePin (Ex:=Ex) (Sel:=Sel) (D:=D) B address low a s) fit
  | .feed b=>feed b s

def rowProgram (fit : formats+1≤2^digits) (address : Attempt→Fin S→Fin B.u)
    (low : digits≤B.W+1) (carry : Attempt→Fin S→Net) (packet : Attempt→Fin S→Fin formats→Net)
    (feed : Boundary→Fin S→Net) (es : List Event) (s : Fin S) (j : Fin es.length) : Net :=
  dateProgram B fit address low carry packet feed s (es.get j)

set_option Elab.async false in
set_option maxHeartbeats 800000 in
theorem attempt_bill (fit : formats+1≤2^digits) (address : Attempt→Fin S→Fin B.u)
    (low : digits≤B.W+1) (carry : Attempt→Fin S→BitNetwork F (Fintype.card (SitePins Ex Sel D B)))
    (packet : Attempt→Fin S→Fin formats→BitNetwork F (Fintype.card (SitePins Ex Sel D B)))
    (feed : Boundary→Fin S→BitNetwork F (Fintype.card (SitePins Ex Sel D B))) (s : Fin S) (a : Attempt) :
    (dateProgram (F:=F) (Ex:=Ex) (Sel:=Sel) (D:=D) B fit address low carry packet feed s (.attempt a)).cells +
      (dateProgram (F:=F) (Ex:=Ex) (Sel:=Sel) (D:=D) B fit address low carry packet feed s (.attempt a)).internal ≤ ((carry a s).cells+(carry a s).internal)+177^digits*
        ∑t : Fin formats,((packet a s t).cells+(packet a s t).internal) := by
  have bound:=site_fee (F:=F) (carry a s) (Fin.cases (idleNet (F:=F) («V»:=V)) (packet a s))
    (modePin (Ex:=Ex) (Sel:=Sel) (D:=D) B address low a s) (ProtocolRAM.SiteScatter.tag fit)
  have zero : (idleNet (F:=F) («V»:=V)).cells+(idleNet (F:=F) («V»:=V)).internal=0 := by
    rw [idleNet,WideHost.localFamily_size]
    simp
  rw [Fin.sum_univ_succ] at bound
  simpa only [dateProgram, dated, Fin.cases_zero, Fin.cases_succ, zero, zero_add] using bound

omit [Fintype Ex] [Fintype Sel] [Fintype D] in
theorem modePin_read (a : Attempt) (s : Fin S) (m : Memory B.W)
    (ext : Ex→Bool) (sel : Sel→Bool) (d : D→Bool) (j : Fin digits) :
    Sum.elim ext (Sum.elim sel (Sum.elim d (B.terminal m))) (modePin B address low a s j)=
      (m (B.addr (address a s)).val).val.testBit j.val := rfl

end Hierarchy.WireTelescope.PassMatrix

end
end OAI
