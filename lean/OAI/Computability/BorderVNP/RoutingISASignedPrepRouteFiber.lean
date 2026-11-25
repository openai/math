import OAI.Computability.BorderVNP.CubeScatterTransmissionRecovery

/-! # The joint route fiber on an actual observed exterior

Read every shared row from the lower symbol's physical destination bank. On
the observed exterior, these row words index all and only the simultaneous
returns of the native route, including slots whose two owners coincide.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
    {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
    {tab : TableLayout} {row : ℕ → TableRow} {pub : Fin (R+1) → Arg → Word w}
    {before : Fin (R+1) → Memory w} {dst ib hb sb : Fin (R+1) → ℕ} {guess : Fin (R+1) → ℕ → Bool}
    {g : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ} {a q blocks K h : ℕ}
    {decl : LengthDeclaration a q} {group : Fin q → Fin (R+1)} {anchor : Fin (R+1)}

local notation "PL" => fun u => G.pinLayout u (ib u) (hb u) (sb u)

variable (input : SharedRoutePrepared G pin ext L D pp lp owner origin stride tab row pub before dst ib hb sb guess)
    (header : ReturnedHeaders G pin ext L w) (fixed : Block (R+1))
    (mac : Fin (R+1) → TeamOpcode.Macros w 8) (regs : Fin (R+1) → Bank w)

private abbrev JointRoutes := ∀ u : Fin (R+1), Returns route (pub u) (mac u) (regs u) (before u)
local notation "Routes" => JointRoutes (pub := pub) (before := before) mac regs

/-- Physical decoder of all the shared words from the actual returned states. -/
def readRouteRows (row : ℕ → TableRow) (g : SharedRows.Layout) (group : Fin q → Fin (R+1))
    (mem : Fin (R+1) → Memory w) (p : Symbols q) : List Bool :=
  receivedWord (mem (group p.val.1)) (g.view p.val.1 p.val.2) (row (sharedIndex g p)).width

private theorem readback {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
    (f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins) (z : Routes)
    (fr : f.row = row) (returned : ∀ u, (H u).history.val.2 = (z u).val.2) :
    f.receivedRows g group = readRouteRows row g group (fun u => (z u).val.2.2) := by
  funext p
  simp only [ReturnedDelivery.receivedRows,readRouteRows,sharedIndex,fr,
    show (H (group p.val.1)).history.val.2.2 = (z (group p.val.1)).val.2.2 from congrArg Prod.snd (returned _)]

variable (emitted : ∀ u, g.Emitted (src u) (readings (before u))) (fitted : ∀ u, g.Fits w (src u))
    (records : tab.records = g.records) (count : tab.count = g.dataCount+g.groups.choose 2)
    (dataCount : (D.directory pp lp).length = g.dataCount) (room : g.banks+g.stride*g.groups^2 ≤ 2^w)
    (frame : SymbolFrame g (src anchor) blocks K h decl group)

include input emitted fitted records count dataCount room frame in
private theorem returned_stream (z : Routes) (sched : Fin (R+1) → Memory w)
    (scheduled : ∀ u, ∃ log t, Runs (pub u) (mac u) scheduleTable (regs u) (before u) log t (sched u)) :
    ∀ u, (z u).val.1.flatMap TeamRAM.Event.choices =
      tableChoiceBits (tableRange tab (sched u)) (directoryFrame (pub u) (sched u) 0)
        (assignedShared g (readRouteRows row g group (fun v => (z v).val.2.2))) tab.count := by
  obtain ⟨H,f,ft,fr,fb,real⟩ := exists_delivery_of_routes tab row pub mac regs before _ z input.allocated input.ordered
    input.rowFit input.teams input.widths input.base input.fields input.records dst ib hb sb input.frame input.fit
    input.capacity input.physical input.inputBefore input.written
  have writer : SharedWriters f g src := ⟨fun u => fb ▸ emitted u,fitted,ft ▸ records,ft ▸ count,room⟩
  have reads := readback (g := g) (group := group) mac regs f z fr (fun u => (real u).1)
  intro u
  obtain ⟨es,bank,run⟩ := (real u).2.2.2.2.2.2.1
  obtain ⟨fs,bank',run'⟩ := scheduled u
  have mem := (run.unique_of_deterministic (by decide) run').2.2
  have tape := (real u).2.1.symm.trans (writer.recovered_local_tape frame dataCount u)
  simpa only [reads,TeamHistory.team,(real u).2.2.2.1,(real u).2.2.2.2.1,mem,
    f.fullCount u,ft] using tape

/-- The free row words must fit their declared lengths and place the exact observed
exterior, with all source deliveries, relay copies and padding bits. -/
def RouteWords (raw : Symbols q → List Bool) : Prop :=
  (∀ p, (raw p).length = SharedRows.reserved blocks K h decl p) ∧
    ext = JointHeader.exterior L (JointHeader.observed L ext fixed) (JointHeader.observed_length ..)
      (tab.recordPayload row (G.assignedRows guess D pp lp (fun i => assignedShared g raw i.val)))

set_option maxRecDepth 10000 in
include input header emitted fitted records count dataCount room frame in
/-- An explicit bijection on the full joint native route domain. Its forward
map reads physical destination banks. Its inverse replays every local slot of
each prescribed raw word on its real word-RAM input. -/
noncomputable def SharedRoutePrepared.routeWordsEquiv :
    Routes ≃ {raw : Symbols q → List Bool //
      RouteWords (G := G) (ext := ext) (L := L) (D := D) (pp := pp) (lp := lp) (guess := guess)
        (tab := tab) (row := row) (g := g) (blocks := blocks) (K := K) (h := h) (decl := decl) fixed raw} := by
  let read (z : Routes) := readRouteRows row g group (fun v => (z v).val.2.2)
  have passed (z : Routes) : RouteWords (G := G) (ext := ext) (L := L) (D := D) (pp := pp) (lp := lp)
      (guess := guess) (tab := tab) (row := row) (g := g) (blocks := blocks) (K := K) (h := h)
      (decl := decl) fixed (read z) := by
    obtain ⟨H,f,ft,fr,writer,physical,real⟩ := input.recover header fixed mac regs z emitted fitted records count dataCount room frame
    have rb := readback (g := g) (group := group) mac regs f z fr (fun u => (real u).1)
    refine ⟨fun p => ?_,?_⟩
    · rw [show read z = f.receivedRows g group from rb.symm]
      exact (writer.declaredRows frame p).2.2.1
    · unfold read
      let canonical (t : TableLayout) (rs : ℕ → TableRow) (raw : Symbols q → List Bool) :=
        JointHeader.exterior L (JointHeader.observed L ext fixed) (JointHeader.observed_length ..)
          (t.recordPayload rs (G.assignedRows guess D pp lp (fun i => assignedShared g raw i.val)))
      change ext = canonical f.table f.row (f.receivedRows g group) at physical
      change ext = canonical tab row _
      exact physical.trans (by rw [ft,fr,rb])
  refine Equiv.ofBijective (fun z => ⟨read z,passed z⟩) ⟨?_,?_⟩
  · intro x y eq
    have rx : read x = read y := congrArg Subtype.val eq
    choose es endBank sched runs _cost _rest _image using fun u =>
      scheduleTable_image (pub u) (mac u) (regs u) (before u) tab row input.allocated input.rowFit
        (input.base u) (input.fields u) (input.records u)
    have supplied (u : Fin (R+1)) : ∃ log t, Runs (pub u) (mac u) scheduleTable (regs u) (before u) log t (sched u) := ⟨es u,endBank u,runs u⟩
    have tx := returned_stream input mac regs emitted fitted records count dataCount room frame x sched supplied
    have ty := returned_stream input mac regs emitted fitted records count dataCount room frame y sched supplied
    funext u
    have same : (x u).val.1.flatMap TeamRAM.Event.choices = (y u).val.1.flatMap TeamRAM.Event.choices := by
      rw [tx,ty]
      exact congrArg (fun bs => tableChoiceBits _ _ (assignedShared g bs) _) rx
    obtain ⟨h1,h2,h3⟩ := DiagonalResidueRAM.unique_returns (c := route) (route.program_tag_native (by decide)) (x u).property (y u).property
      (tail := []) (tail' := []) (by simpa using same)
    exact Subtype.ext (Prod.ext h1 (Prod.ext h2 h3))
  · rintro ⟨raw,hlen,hext⟩
    let high (_ _ : Fin (R+1)) (_ : ℕ) := false
    have checks := (JointHeader.exterior_unique L fixed _ (JointHeader.observed_length ..) high _ ext).mpr hext
    obtain ⟨z,H,f,_ft,fr,_writer,rb,real⟩ := input.realize mac regs emitted fitted records count dataCount room frame raw hlen checks
    exact ⟨z,Subtype.ext ((readback (g := g) (group := group) mac regs f z fr (fun u => (real u).1)).symm.trans rb)⟩

/-- The decoder in the bijection reads exactly the actual returned destination words. -/
theorem SharedRoutePrepared.routeWordsEquiv_apply (z : Routes) :
    (input.routeWordsEquiv header fixed mac regs emitted fitted records count dataCount room frame z).val =
      readRouteRows row g group (fun u => (z u).val.2.2) := rfl

end TeamContraction

end BorderVNP
end Computability
end OAI
