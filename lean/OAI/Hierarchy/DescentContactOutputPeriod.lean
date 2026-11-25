import OAI.Hierarchy.DescentContactCatalog
import OAI.Hierarchy.DescentResetStemProjectExprTariff

namespace OAI
/-! # One post-trunk execution from original donor counts to the projected four contact operands -/
namespace Hierarchy.DescentContactOutputShape.Shape
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (A : Shape) (donorStart first : ℕ) {w : ℕ}
local notation "D" => A.donor
local notation "P" => A.marker first
local notation "E" => A.projected first
local notation "H" => A.sparseHosts
local notation "M" => A.donor.batch
variable (u : DescentContactSenderDate.Prior A.donor.degree A.donor.lows A.donor.cap A.donor.n A.donor.residual)

def four {α : Type*} (xs : Fin A.sockets→Fin 4→α) (i : Fin A.fields) : α:=
  xs (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
def held (m : Memory w) := A.catalogImage first (DescentContactMaskShape.result (D) donorStart first u m)
def prepared (w : ℕ):=(DescentContactMaskShape.period (D) donorStart first u w).seq (A.catalog first w)
def prepareTicks:=DescentContactMaskShape.clock (D) donorStart first u+A.catalogClock

variable (operands : Fin A.sockets→Fin 4→Expr)
local notation "terms" => A.four operands
local notation "prj" => DescentResetStemProjectExpr.program E H A.groups A.blocks A.metaBits M A.batch terms
def program (w : ℕ):=(A.prepared donorStart first u w).seq (prj w)
def image (m : Memory w):=DescentResetStemProjectExpr.image E H A.groups A.blocks A.metaBits M A.batch terms
  (A.held donorStart first u m)
def ticks:=A.prepareTicks donorStart first u+DescentResetStemProjectExpr.ticks E H A.groups A.blocks A.metaBits M A.batch terms
def output (q : Fin A.sockets) (field : Fin 4) (x : Fin A.blocks):=
  DescentResetStemProject.bank E A.fields H A.groups A.blocks A.metaBits M A.batch (finProdFinEquiv (q,field)) x

variable (prior : A.donor.endAddress donorStart≤first) (old : A.donor.Space donorStart u w)
variable (space : A.endAddress first<2^w) (batch : 0<A.batch) (blocks : 0<A.blocks)
variable (fit : ∀q f,(operands q f).Fits w (A.projected first))

include prior old space in
theorem prepared_any (m : Memory w) :
    (A.prepared donorStart first u w).Exec m (A.held donorStart first u m) (A.prepareTicks donorStart first u) ∧
    CheapCode (A.prepared donorStart first u w) ∧ ∀z,z<first ∨ E≤z→A.held donorStart first u m z=m z:=by
  obtain ⟨a,b,c,d,e,f⟩:=A.cuts first
  have last:=f.trans_lt space
  have earlier:=b.trans (c.trans (d.trans e))
  have stage:=DescentContactMaskShape.period_any (D) donorStart first u prior old (earlier.trans_lt last) m
  have pages:=A.catalog_any first (DescentContactMaskShape.result A.donor donorStart first u m) last
  exact ⟨Procedure.Exec.then stage.1 pages.1,cheap_seq stage.2.1 pages.2.1,fun z h=>
    (pages.2.2 z (h.imp (fun lo=>lo.trans_le a) id)).trans (stage.2.2 z (h.imp id (fun hi=>earlier.trans hi)))⟩

include prior old space batch blocks fit in
theorem any (m : Memory w) :
    (A.program donorStart first u operands w).Exec m (A.image donorStart first u operands m) (A.ticks donorStart first u operands) ∧
    CheapCode (A.program donorStart first u operands w) ∧
    ∀z,z<first ∨ A.endAddress first≤z→A.image donorStart first u operands m z=m z:=by
  have prep:=A.prepared_any donorStart first u prior old space m
  have tail_:=DescentResetStemProjectExpr.any E H A.groups A.blocks A.metaBits M A.batch terms (A.held donorStart first u m) batch blocks
    (fun i=>fit _ _) space
  obtain ⟨a,b,c,d,e,f⟩:=A.cuts first
  exact ⟨Procedure.Exec.then prep.1 tail_.1,cheap_seq prep.2.1 tail_.2.2,fun z h=>
    (tail_.2.1 z (h.imp (fun lo=>lo.trans_le (a.trans (b.trans (c.trans (d.trans e))))) id)).trans
      (prep.2.2 z (h.imp id (fun hi=>f.trans hi)))⟩

def native : NativePhase w:=
  ⟨A.program donorStart first u operands w,A.ticks donorStart first u operands,A.image donorStart first u operands,
    (A.any donorStart first u operands prior old space batch blocks fit (fun _=>0)).2.1⟩

private theorem source_cast {g j a h m : ℕ} (eqn : g=j) (src : Expr) (v : Fin h→Fin g→Cell a)
    (mem : Memory w) (read : Source src v m mem) :
    Source src (fun u (i : Fin j)=>v u (Fin.cast eqn.symm i)) m mem :=by
  subst j
  exact read

include space batch blocks fit in
theorem issued (m : Memory w) (oldBatch : 0<M) (size : (D).groups=A.groups*A.blocks)
    (values : Fin A.sockets→Fin 4→Fin H→Fin (D).groups→Cell A.metaBits)
    (live : ∀q f,Source (operands q f) (values q f) M (A.held donorStart first u m)) (q : Fin A.sockets) (f : Fin 4)
    (x : Fin A.blocks) :
    (A.output first q f x).Fits w (A.endAddress first) ∧
    Source (.lookup (A.output first q f x) .row)
      (fun h g=>values q f h (Fin.cast size.symm (finProdFinEquiv (g,x)))) A.batch
      (A.image donorStart first u operands m):=by
  let Y : Fin A.fields→Fin H→Fin (A.groups*A.blocks)→Cell A.metaBits:=
    fun i h g=>A.four values i h (Fin.cast size.symm g)
  have actual (i : Fin A.fields) : Source (terms i) (Y i) M (A.held donorStart first u m):=
    source_cast size _ _ _ (live (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)
  have run:=DescentResetStemProjectExpr.run E H A.groups A.blocks A.metaBits M A.batch terms (A.held donorStart first u m) Y oldBatch batch blocks
    (fun i=>fit _ _) actual space
  exact ⟨run.2.2.1 _ _,by simpa only [Y,output,image,four,Equiv.symm_apply_apply] using run.2.1 (finProdFinEquiv (q,f)) x⟩

end
end Hierarchy.DescentContactOutputShape.Shape

end OAI
