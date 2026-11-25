import OAI.Hierarchy.DescentScalarActorTickets
import OAI.Hierarchy.ProbeStageColumnScan
import OAI.Hierarchy.DescentStaticTablePages

namespace OAI
/-! # Simultaneously publish both short fields for every physical old and born actor -/
namespace Hierarchy.DescentScalarVenueMask.Publisher
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentSharedCableNames DescentPacking.PackedMatch.Local
open DescentHaloWalkRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {r D cap d slots raw H G M w : ℕ}
local notation "K" => 1+cap*6
local notation "pathWidth" => breadth D
local notation "bits" => Owners.digits r D d
local notation "regWidth" => ((bits*3)*r)
local notation "headsWidth" => Owners.outputBits r D (2*cap) d

abbrev Label (r cap : ℕ):= Fin r×Fin (1+cap*6)
abbrev choice (r cap : ℕ):=Fin 2×Label r cap

def index (r cap : ℕ) : choice r cap≃Fin (2*(r*(1+cap*6))):=(Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv

def ticket (v : Label r cap) (active : Cell (1*r)) (prior : Owners.Register r D d) (heads : Cell headsWidth) : Ticket pathWidth raw :=
  (finSumFinEquiv.symm v.2).elim (fun _ : Fin 1=>oldTicket v.1 slots raw active prior)
    (fun x:Fin (cap*6)=>let j:=finProdFinEquiv.symm x;newTicket v.1 (j.1.castLE (by omega : cap≤2*cap)) j.2 slots raw active heads)

structure Chart (r cap : ℕ) where
  actor : Bank
  old : Bank
  born : Bank
  gate : choice r cap→Tables

private def column (B : Bank) : Expr:=.lookup B .row

def expr (C : Chart r cap) (c : choice r cap) : Expr :=(C.gate c).read (column C.actor)
    ((finSumFinEquiv.symm c.2.2).elim (fun _:Fin 1=>column C.old) (fun _:Fin (cap*6)=>column C.born))

def expressions (C : Chart r cap) :=List.ofFn (fun j=>expr C ((index r cap).symm j))
def passes (C : Chart r cap) (H G M base : ℕ) :=ProbeStage.Native.columns (H*chunks G M) base (expressions C)
def bank (H G M base rowBits : ℕ) (c : choice r cap) : Bank:=⟨base+((index r cap c).val*(H*chunks G M)),rowBits⟩

def projection (P raw : ℕ) (which : Fin 2) (x : Ticket P raw) : Cell (Packed.bits (if which=0 then P else raw)) :=
  if zero : which=0 then Fin.cast (by simp [zero]) (pathCode x)
  else Fin.cast (by simp [zero]) (localCode x)

private theorem project_none (which : Fin 2) : projection pathWidth raw which none=0:=by
  apply Fin.ext
  by_cases z:which=0 <;> simp [projection,z,pathCode,localCode,Packed.token]

def oldFunction (which : Fin 2) (x : Fin r) (mask : Cell (1*r)) (home : Owners.Register r D d) :=
  projection pathWidth raw which (oldTicket x slots raw mask home)
def bornFunction (which : Fin 2) (x : Fin r) (j : Fin cap) (who : Fin 6) (mask : Cell (1*r)) (heads : Cell headsWidth) :=
  projection pathWidth raw which (newTicket x (j.castLE (by omega : cap≤2*cap)) who slots raw mask heads)

private theorem zero_mask (i : Fin r) : (encode 1 r).symm 0 i=0 :=by
  have z:encode 1 r (fun _=>0)=0:=by apply Fin.ext;change (finFunctionFinEquiv (fun _ : Fin r=>(0:Cell 1))).val=0;simp []
  rw [(encode 1 r).symm_apply_eq.mpr z.symm]

structure Mounted (C : Chart r cap) (D d slots raw H G M base : ℕ) (m : Memory w)
    (active : Fin H→Fin G→Cell (1*r)) (prior : Fin H→Fin G→Owners.Register r D d) (heads : Fin H→Fin G→Cell (Owners.outputBits r D (2*cap) d)) : Prop where
  actors : Source (column C.actor) active M m
  old : Source (column C.old) prior M m
  born : Source (column C.born) heads M m
  smallOld : ∀f x,let c:choice r cap:=(f,x,finSumFinEquiv (Sum.inl (0:Fin 1)));DescentPackedZip.Fits (C.gate c) (column C.actor) (column C.old) (1*r) ((Owners.digits r D d*3)*r) M base w
  smallNew : ∀f x (z:Fin (cap*6)),let c:choice r cap:=(f,x,finSumFinEquiv (Sum.inr z));DescentPackedZip.Fits (C.gate c) (column C.actor) (column C.born) (1*r) (Owners.outputBits r D (2*cap) d) M base w
  oldROM : ∀f x,Static (C.gate (f,x,finSumFinEquiv (Sum.inl (0:Fin 1)))) (oldFunction (D:=D) (d:=d) (slots:=slots) (raw:=raw) f x) M m
  bornROM : ∀f x (z : Fin (cap*6)),let u:=finProdFinEquiv.symm z;Static (C.gate (f,x,finSumFinEquiv (Sum.inr z))) (bornFunction (D:=D) (d:=d) (slots:=slots) (raw:=raw) f x u.1 u.2) M m

theorem chip (C : Chart r cap) (active : Fin H→Fin G→Cell (1*r)) (old : Fin H→Fin G→Owners.Register r D d) (heads : Fin H→Fin G→Cell headsWidth)
    (base : ℕ) (m : Memory w) (ready : Mounted C D d slots raw H G M base m active old heads) (c : choice r cap) :
    (expr C c).Fits w base ∧ Source (expr C c) (fun h g=>projection pathWidth raw c.1 (ticket (slots:=slots) c.2 (active h g) (old h g) (heads h g))) M m :=by
  obtain ⟨f,x,j⟩:=c;obtain ⟨z,rfl⟩:=finSumFinEquiv.surjective j;rcases z with unit|z
  · have eqn:unit=0:=Subsingleton.elim ..;subst unit
    have fit:=ready.smallOld f x;simp only [expr,ticket,Equiv.symm_apply_apply,Sum.elim_inl]
    constructor
    · simp only [Tables.read,Expr.Fits,fit.apply,fit.shift,fit.left,fit.right,and_self]
    · exact read_data _ _ _ base fit _ (by simp [oldFunction,oldTicket,zero_mask,project_none]) m (ready.oldROM f x) _ _ ready.actors ready.old
  · have fit:=ready.smallNew f x z;simp only [expr,ticket,Equiv.symm_apply_apply,Sum.elim_inr]
    constructor
    · simp only [Tables.read,Expr.Fits,fit.apply,fit.shift,fit.left,fit.right,and_self]
    · exact read_data _ _ _ base fit _ (by simp [bornFunction,newTicket,zero_mask,project_none]) m (ready.bornROM f x z) _ _ ready.actors ready.born

theorem publish (C : Chart r cap) (active : Fin H→Fin G→Cell (1*r)) (old : Fin H→Fin G→Owners.Register r D d) (heads : Fin H→Fin G→Cell headsWidth)
    (base rowBits : ℕ) (m : Memory w) (ready : Mounted C D d slots raw H G M base m active old heads)
    (space : base+2*(r*K)*(H*chunks G M)<2^w) :
    let ps:=passes C H G M base;let o:=result ps m
    (program w ps).Exec m o (clock ps) ∧ (∀c:choice r cap,Reads (bank H G M base rowBits c)
      (fun h g=>projection pathWidth raw c.1 (ticket (slots:=slots) c.2 (active h g) (old h g) (heads h g))) M o) ∧
      (∀a,a<base ∨ base+2*(r*K)*(H*chunks G M)≤a → o a=m a) ∧ CheapCode (program w ps) :=by
  intro ps o;let es:=expressions C
  have fit:∀e∈es,e.Fits w base:=by intro e he;obtain ⟨j,rfl⟩:=List.mem_ofFn.mp he;exact (chip C active old heads base m ready _).1
  refine ⟨ProbeStage.Native.columns_exec es m (ProbeStage.Native.columns_safe es le_rfl fit (by simpa [es,expressions] using space)),?_,?_,@ProtocolRAM.program_cheap _ _⟩
  · intro c p;let j:=index r cap c
    have use:=ProbeStage.Native.columns_read es m le_rfl fit j.val (by simp [es,expressions,j]) (row H G M p)
    have recorded: (es[j.val]'(by simp [es,expressions]))=expr C c:=by simp [es,expressions,j]
    rw [recorded] at use;exact use.trans ((chip C active old heads base m ready c).2 p)
  · intro a away;apply ProbeStage.Native.columns_frame;simpa [es,expressions] using away

end
end Hierarchy.DescentScalarVenueMask.Publisher

end OAI
