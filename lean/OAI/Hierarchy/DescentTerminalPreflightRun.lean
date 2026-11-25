import OAI.Hierarchy.DescentTerminalPreflightBill
import OAI.Hierarchy.DescentTerminalPrimitiveAny
import OAI.Hierarchy.DescentTerminalPreflightPriorRun
import OAI.Hierarchy.DescentTerminalPreflightHigh

namespace OAI
/-! # Fixed preprocessing execution and its attained terminal memory -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open DescentSIMDLookup DescentTerminalPreflightInvoice DescentTerminalLocalPortBook
open DescentTerminalCombinedRole DescentTerminalPointerDigits DescentTerminalHeaderDraft
open DescentStaticWordColumn DescentColonies.SplitRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false

private theorem phases_time (a b c d e f g h i j : ℕ) :
    a+b+c+d+e+f+g+h+i+j = (((a+b)+c)+(d+e))+f+((g+h)+(i+j)) := by
  simp only [Nat.add_assoc]

private theorem phases_cheap {w:ℕ} (a b c d e f : Procedure w)
    (ha:CheapCode a) (hb:CheapCode b) (hc:CheapCode c) (hd:CheapCode d)
    (he:CheapCode e) (hf:CheapCode f) :
    CheapCode ((((a.seq b).seq (c.seq d)).seq e).seq f) :=
  cheap_seq (cheap_seq (cheap_seq (cheap_seq ha hb) (cheap_seq hc hd)) he) hf

private theorem phases_exec {w : ℕ} (a b c d e f : Procedure w)
    {m₀ m₁ m₂ m₃ m₄ m₅ m₆ : Memory w} {ta tb tc td te tf : ℕ}
    (ha:a.Exec m₀ m₁ ta) (hb:b.Exec m₁ m₂ tb) (hc:c.Exec m₂ m₃ tc)
    (hd:d.Exec m₃ m₄ td) (he:e.Exec m₄ m₅ te) (hf:f.Exec m₅ m₆ tf) :
    ((((a.seq b).seq (c.seq d)).seq e).seq f).Exec m₀ m₆ (((ta+tb)+(tc+td))+te+tf) :=
  Procedure.Exec.then (Procedure.Exec.then
    (Procedure.Exec.then (Procedure.Exec.then ha hb) (Procedure.Exec.then hc hd)) he) hf

variable (x:DescentTerminalPreflightSpace.Spec) (base:ℕ) (peer:Bank)
    (wing:Fin x.scalar.blocks→Fin (2*x.cap)→Bank)
    (w q p nd nodes hidden args:ℕ) (oldPaid actor:Fin x.scalar.blocks→Bank)
    (first second:Shelf) (chart:Fin x.scalar.columns→Fin x.scalar.blocks→Gather.Address)
    {out0 out7:ℕ} (f0:(Fin x.scalar.columns→Cell x.scalar.pointerBits)→Cell out0)
    (f7:(Fin x.scalar.columns→Cell x.scalar.pointerBits)→Cell out7)
    (decode:(Fin x.strips→Cell x.printBits)→Directory 4 x.vertices x.arguments)
    (count modulo homes:Bank) (boundary:ℕ) (control:ℕ→ℕ)

local notation "s" => x.scalar
local notation "H0" => (s).shops
local notation "C" => x.issuedBook base peer wing
local notation "P" => x.publicWidths base
local notation "A" => x.draft base count modulo homes boundary
local notation "ports" => x.eventInputs base peer wing
local notation "T" => x.cables base peer wing
local notation "c" => x.controls base
local notation "at0" => x.primitive base
local notation "popStart" => x.cohortEnd base
local notation "next" => DescentTerminalPriorArena.actStart s x.groups x.paidLanes x.paidBits x.externalBits popStart
local notation "takeActor" => (fun (_:Fin (s).blocks) (u:Cell 1)=>u)
local notation "pop" => DescentTerminalPopulation.RAM.issue H0 x.groups x.paidLanes x.paidBits nd x.externalBits popStart oldPaid (x.census base) w
local notation "live" => DescentTerminalActorRepack.program takeActor H0 x.groups x.actorLanes next actor w
local notation "prim" => DescentTerminalPrimitiveNames.program w first second at0 ((s).gather at0) H0 chart f0 f7
  ((s).sources at0 (x.population base)) (s).countBits ((s).counting at0) ((s).widths at0) q hidden nodes args x.groups p
local notation "weights" => Book.WeightShelf.program x.vertices x.arguments (x.weights base) w
local notation "book" => (C).prefix decode (x.vertices*x.arguments) w 6 le_rfl
local notation "controls" => (c).program w control (Book.expression (x.parts base))
local notation "rack" => (T).program w q p
local notation "exterior" => (P).program w q p
local notation "literals" => litProc w (x.literalBase base) (A).rows
local notation "draft" => machine A ports x.degree w

local notation "machine_" => purchasedProgram x base peer wing w q p nd nodes hidden args oldPaid actor
  first second chart f0 f7 decode count modulo homes boundary control
local notation "ticks_" => purchasedClocks x base peer wing q p oldPaid actor chart count modulo homes boundary


local notation "priorMem" => DescentTerminalPriorArena.final («s»:=s) (groups:=x.groups) (mPaid:=x.paidLanes)
  (mAct:=x.actorLanes) (paidBits:=x.paidBits) (extBits:=x.externalBits) (actBits:=1) (origin:=popStart)
  (paid:=oldPaid) (actorSrc:=actor) (ext:=x.census base) (nodeBits:=nd) (pick:=takeActor) (wb:=w)
local notation "primMem" => (s).primitiveImage at0 (x.population base) first second chart f0 f7 q hidden nodes args x.groups p
local notation "weightsMem" => Book.WeightShelf.memory x.vertices x.arguments (x.weights base)
local notation "bookMem" => fun m:Memory w=>(C).memory decode (x.vertices*x.arguments) m 6 le_rfl
local notation "controlMem" => (c).after control (Book.expression (x.parts base))
local notation "geometry" => x.afterSiteControls base q p peer wing count modulo homes boundary

def paidSnapshot (m:Memory w) := priorMem m

def primitiveSnapshot (m:Memory w) := primMem (priorMem m)

def bookSnapshot (m:Memory w) := bookMem (weightsMem (primMem (priorMem m)))

/-- The exact last memory of the purchased lower pipeline, defined on all machine inputs. -/
def purchasedMem (m:Memory w) :=
  geometry (controlMem (bookMem (weightsMem (primMem (priorMem m)))))

local notation "done_" => x.purchasedMem base peer wing w q p nd nodes hidden args oldPaid actor
  first second chart f0 f7 decode count modulo homes boundary control

theorem purchased_frames (m:Memory w) (before:x.Before base oldPaid actor wing peer count modulo homes boundary)
    (room:x.maskBase base<2^w) (positive:0<w) (nonempty:0<x.strips) (columns:0<(s).columns)
    (role:(emit first).Fits w at0) (arity:(emit second).Fits w at0)
    (pointers:∀j b,(chart j b).Fits ((s).gather at0) H0 w) :
    (machine_).Exec m (done_ m) ticks_ ∧ CheapCode machine_ ∧
      (∀a,a<popStart ∨ x.maskBase base≤a→done_ m a=m a) ∧
      (∀a,a<x.weights base→done_ m a=(primMem (priorMem m)) a) ∧
      (∀a,a<x.bookEnd base→done_ m a=(bookMem (weightsMem (primMem (priorMem m)))) a) := by
  obtain ⟨e,pr,prb,bb,bc,ct,tw,wd,stop⟩:=x.layers base
  have leaf:(s).finish at0<2^w:=by change x.weights base<_;omega
  have fit:=x.book_fits base room nonempty
  have kit:=(s).realized at0 (x.population base) _ (x.prior base) leaf columns
  have priorRun:=x.purchased_prior base nd oldPaid actor wing peer count modulo homes boundary m before room
  have firstRun:=(s).primitive_any at0 (x.population base) first second chart f0 f7 q hidden nodes args x.groups p
    (priorMem m) kit role (ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) arity) pointers
  let m0:=primMem (priorMem m)
  have buy:=Book.WeightShelf.execute x.vertices x.arguments (x.weights base) m0
    (by change x.bookBegin base<2^w;omega)
  have buyCheap : CheapCode weights :=(Book.WeightShelf.tariff x.vertices x.arguments x.binSize q (x.weights base) w).1
  have bk:=(C).native decode (x.vertices*x.arguments) (weightsMem m0)
    (x.source_fit base peer wing room before.roster before.oldCables) fit.2.1 fit.2.2 6 le_rfl
  let acquired:=bookMem (weightsMem m0)
  have controlRun:=(c).any acquired control (Book.expression (x.parts base))
    (x.control_fits base room nonempty) (by omega)
  have last:=x.after_site_run base q p peer wing count modulo homes boundary
    (controlMem acquired) oldPaid actor before room positive
  obtain ⟨priorSteps, priorCheap, priorKeep⟩ := priorRun
  obtain ⟨firstSteps, firstCheap, firstKeep⟩ := firstRun
  obtain ⟨buySteps, _, buyKeep⟩ := buy
  obtain ⟨bookSteps, bookCheap, bookKeep, bookRest⟩ := bk
  obtain ⟨controlSteps, controlCheap, controlKeep⟩ := controlRun
  obtain ⟨lastSteps, lastCheap, lastKeep⟩ := last
  constructor
  · unfold purchasedClocks
    rw [phases_time]
    exact phases_exec ((pop).seq live) prim weights book controls
      (x.afterSiteProgram base q p peer wing count modulo homes boundary w)
      (@priorSteps) (@firstSteps) (@buySteps) (@bookSteps) (@controlSteps) (@lastSteps)
  · have «protected» (a:ℕ) (ha:a<x.bookEnd base) : done_ m a=acquired a :=
      (lastKeep a (ha.trans_le bc)).trans (controlKeep a (.inl ha))
    have kept (a:ℕ) (ha:a<x.weights base) : done_ m a=m0 a :=
      («protected» a ((ha.trans_le prb).trans_le bb)).trans
        ((bookKeep a (ha.trans_le prb)).trans (buyKeep a (.inl ha)))
    refine ⟨phases_cheap ((pop).seq live) prim weights book controls
      (x.afterSiteProgram base q p peer wing count modulo homes boundary w)
      (@priorCheap) (@firstCheap) (@buyCheap) (@bookCheap) (@controlCheap) (@lastCheap),?_,kept,«protected»⟩
    intro j outside
    rcases outside with low|high
    · exact (kept j (by omega)).trans ((firstKeep j (.inl (by omega))).trans (priorKeep j (.inl low)))
    · have keptLast:=x.after_site_high base q p peer wing count modulo homes boundary
        (controlMem acquired) oldPaid actor before room j high
      have keptBook:=(C).memory_high decode (x.vertices*x.arguments) (weightsMem m0)
        (x.source_fit base peer wing room before.roster before.oldCables) fit.2.1 fit.2.2 6 le_rfl j
        (by change x.bookEnd base≤j;omega)
      exact keptLast.trans ((controlKeep j (.inr (by omega))).trans (keptBook.trans
        ((buyKeep j (.inr (by change x.bookBegin base≤j;omega))).trans
          ((firstKeep j (.inr (by change x.weights base≤j;omega))).trans
            (priorKeep j (.inr (by omega)))))))

theorem purchased_run (m:Memory w) (before:x.Before base oldPaid actor wing peer count modulo homes boundary)
    (room:x.maskBase base<2^w) (positive:0<w) (nonempty:0<x.strips) (columns:0<(s).columns)
    (role:(emit first).Fits w at0) (arity:(emit second).Fits w at0)
    (pointers:∀j b,(chart j b).Fits ((s).gather at0) H0 w) :
    (machine_).Exec m (done_ m) ticks_ ∧ CheapCode machine_ ∧
      ∀a,a<popStart→done_ m a=m a := by
  have all_:=x.purchased_frames base peer wing w q p nd nodes hidden args oldPaid actor first second chart f0 f7
    decode count modulo homes boundary control m before room positive nonempty columns role arity pointers
  exact ⟨all_.1,all_.2.1,fun j hj=>all_.2.2.1 j (.inl hj)⟩

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
