import OAI.Computability.BorderVNP.CubeRouteEmitterInputs

/-! # Complete success and inverse readback of the physical public group schedule -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical TeamContraction Transmission

variable {w R : ℕ} {ar : CubeArena.Layout} {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
variable {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {r : Bank w} {slotted : Memory w}
variable {base controls team ticks : ℕ} {decl : LengthDeclaration ar.n ar.header.d} {ok : Prop}
variable {group : Fin ar.header.d → Fin (R+1)} {owner : ℕ → Fin (R+1)} {pins : Pins.Layout} {input : ℕ → ℕ}
variable {I : Type*} [Fintype I] {cell : I → Fin ar.cells} {id : I ↪ ℕ} {width : I → ℕ}

local notation "initialRAM" => Packing.Directory.ISA.publish slotted (Fin.val (pub 0)) base (D.directory pp lp)
local notation "entries" => List.length (D.directory pp lp)
local notation "g" => ar.sharedRows (Fin.val (pub 0)) (Fin.val (Prod.fst decl)) (List.length (D.directory pp lp))
local notation "selectorBits" => Tally.selectorWidth ar.n ar.K ar.h

/-- The state properties discharged by the true first nine native passes. -/
def WriterSources (ar : CubeArena.Layout) (frame controls team R : ℕ) (decl : LengthDeclaration ar.n ar.header.d)
    (group : Fin ar.header.d → Fin (R+1)) (args : Arg → ℕ) (input orig m : ℕ → ℕ) (w : ℕ) : Prop :=
  NativeEntry ar frame controls decl.1 R input orig m ∧
    DirectorySources ar frame controls decl.1
      (fun z => ar.ScannerWords frame team decl.1.val (fun x => (group x).val) args z decl.2) w m

/-- The actual shared writer and the true source inventory retained by a normal native return. -/
structure ReturnedWriters (ar : CubeArena.Layout) (D : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
    (owner : ℕ → Fin (R+1)) (decl : LengthDeclaration ar.n ar.header.d) (group : Fin ar.header.d → Fin (R+1))
    (pins : Pins.Layout) {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {r t : Bank w}
    {m mt : Memory w} {es : List (TeamRAM.Event w)}
    (H : WriterHistory ar.n (Tally.selectorWidth ar.n ar.K ar.h) pub mac r m es t mt) : Prop where
  emission : PreparedEmission ar D pp lp owner decl group pins pub H.dataInput
  low : ∀ x < ar.header.header, H.dataInput x = m x
  written : (ar.sharedRows (pub 0).val decl.1.val (D.directory pp lp).length).Emitted
    (readings H.sharedInput) (readings mt)

/-- Final shared writer source facts, on the actual reached intermediate RAM. -/
theorem ReturnedWriters.shared_inputs {t : Bank w} {mt : Memory w} {es : List (TeamRAM.Event w)}
    {H : WriterHistory ar.n selectorBits pub mac r initialRAM es t mt}
    (cert : ReturnedWriters ar D pp lp owner decl group pins H) :
    (g).Fields (readings H.sharedInput) ∧ (g).Fits w (readings H.sharedInput) ∧
      SymbolFrame g (readings H.sharedInput) ar.header.blocks ar.K ar.h decl group := by
  rw [H.dataImage cert.emission.demand.ready]
  exact ⟨cert.emission.sharedFields,cert.emission.sharedFit,cert.emission.symbols⟩

/-- Successful native executions are exactly those admitted by the real prefix. Both directions
use the slotted input, decoded group/cell/label-pair directories and physically computed writer addresses. -/
theorem SlottedWriter.complete_schedule (P : SlottedWriter ar D pp lp pins pub slotted base cell id width)
    (first : TestRun pub mac (.block (beforeWriters ar.n selectorBits)) r initialRAM ticks ok (fun z =>
      WriterSources ar (pub 0).val controls team R decl group (readings pub) input (readings initialRAM) z.mem w))
    (cells : ∀ c < ar.cells, ar.receivingOwner (pub 0).val decl.1 R input c = owner c)
    (low : (pub 0).val+112 ≤ ar.header.header) (axes : ar.header.a = ar.n+1)
    (cap : ok → ∀ p j, decl.2 p j ≤ ar.header.cap)
    (rows : entries+ar.header.d.choose 2 ≤ ar.maxRows) (fit : ar.stop < 2^w) :
    (ok → ∃ es t mt, ∃ H : WriterHistory ar.n selectorBits pub mac r initialRAM es t mt,
      ReturnedWriters ar D pp lp owner decl group pins H ∧
      traceCost es ≤ ticks + (DataWriter.setup.slots+entries*(DataWriter.step.slots+1)+5+SharedRows.budget ar.header.d)) ∧
    (∀ {es t mt}, Runs pub mac (scheduleGroups ar.n selectorBits) r initialRAM es t mt → ok ∧
      ∃ H : WriterHistory ar.n selectorBits pub mac r initialRAM es t mt, ReturnedWriters ar D pp lp owner decl group pins H) := by
  have cert {dataReg : Bank w} {data : Memory w} (pass : ok)
      (entry : WriterSources ar (pub 0).val controls team R decl group (readings pub) input (readings initialRAM) (readings data) w) :=
    P.emission mac dataReg entry.1 entry.2 cells low axes (cap pass) rows fit
  constructor
  · intro pass
    obtain ⟨ps,u,mu,rs,cost,entry⟩ := first.complete pass
    have out := cert (dataReg := u) pass entry
    let emit := DataWriter.layout (readings pub) (readings mu)
    let sharedInput := DataWriter.publish emit pub mu
    have rd := out.demand.ready
    obtain ⟨ds,v,dataRun,dataTicks⟩ := DataWriter.program_runs pub mac u mu rd.frame rd.teams rd.stride rd.output rd.separate rd.rows
    obtain ⟨ss,t,mt,sharedRun,sharedTicks,emitted⟩ :=
      SharedRows.run_program pub mac g v sharedInput out.sharedFit rfl out.sharedFields
    let H := WriterHistory.mk (n := ar.n) (bits := selectorBits) u mu v sharedInput ps ds ss rs dataRun sharedRun rfl
    have kept (x : ℕ) (hx : x < ar.header.header) : mu x = initialRAM x := Fin.ext (entry.1.low x hx)
    refine ⟨ps++(ds++ss),t,mt,H,⟨out,kept,emitted⟩,?_⟩
    rw [cost_append,cost_append]
    have count : emit.count = entries := out.demand.count.symm
    change traceCost ds ≤ DataWriter.setup.slots+emit.count*(DataWriter.step.slots+1)+5 at dataTicks
    rw [count] at dataTicks
    change traceCost ss ≤ SharedRows.budget ar.header.d at sharedTicks
    omega
  · intro es t mt run
    obtain ⟨H⟩ := scheduleGroups_writerHistory run
    obtain ⟨pass,entry⟩ := first.sound H.prefixRun
    have out := cert (dataReg := H.dataRegs) pass entry
    have shared := H.emitted out.demand.ready g rfl out.sharedFit out.sharedFields
    rw [← H.dataImage out.demand.ready] at shared
    exact ⟨pass,H,out,fun x hx => Fin.ext (entry.1.low x hx),shared⟩

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
