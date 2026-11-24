import OAI.Computability.VPVNP.CompressorChoiceGridStage
import OAI.Computability.VPVNP.CompressorSourceTransport
import OAI.Computability.VPVNP.PrimedInputRAMFlowComplete
import OAI.Computability.VPVNP.CompressorFlowFootprint

/-!
# External addresses read by the motif preparation calls

Every successful execution of the demand-energy scan, the repetition program
and the first-cover search probes only the input demand cells. The proof
tracks the energy scan's advancing cursor and the grid's public offsets and
also applies when comparison arithmetic wraps.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.DemandFootprint

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM SourceTransport
open scoped Fin.CommRing
open private rowEvents read_exec from OAI.Computability.VPVNP.CompressorChoicePreparation
open private rowsFrom coordinates keep clear coefficient_slot slot from OAI.Computability.VPVNP.CompressorChoiceGrid

variable {w d t k : ℕ} {D : Type*}

/-- Modular address of an actual demand coordinate. -/
def demandCell (base : Word w) (d address : ℕ) : Prop :=
  ∃ i : Fin d, address = (base + (i.val : Word w)).val

/-- All external reads target the input rectangle and no external writes occur. -/
abbrev Footprint (base : Word w) (d : ℕ) (es : List (Event w)) :=
  Reads (demandCell base d) es ∧ Writes (fun _ => False) es

theorem Footprint.interval {base : Word w} {es : List (Event w)} (h : Footprint base d es)
    (fit : base.val+d ≤ 2^w) :
    Reads (fun n => base.val ≤ n ∧ n < base.val+d) es ∧ Writes (fun _ => False) es := by
  refine ⟨fun a v hv => ?_,h.2⟩
  obtain ⟨i,hi⟩ := h.1 a v hv
  rw [hi,Fin.val_add,Fin.val_natCast,Nat.add_mod_mod,Nat.mod_eq_of_lt (by have := i.isLt; omega)]
  exact ⟨Nat.le_add_right ..,Nat.add_lt_add_left i.isLt _⟩

private theorem append {base : Word w} {es fs : List (Event w)} (h : Footprint base d es)
    (h' : Footprint base d fs) : Footprint base d (es++fs) :=
  ⟨fun a v hv => (List.mem_append.mp hv).elim (h.1 a v) (h'.1 a v),
   fun a v hv => (List.mem_append.mp hv).elim (h.2 a v) (h'.2 a v)⟩

private theorem tick {base : Word w} {es : List (Event w)} (h : Footprint base d es) :
    Footprint base d (.tick :: es) := by
  constructor <;> intro a v hv <;> simp only [List.mem_cons,reduceCtorEq,false_or] at hv
  · exact h.1 _ _ hv
  · exact h.2 _ _ hv

private theorem read {base a : Word w} {es : List (Event w)} (h : Footprint base d es)
    (ha : demandCell base d a.val) (x : Word w) : Footprint base d (.read a x :: es) := by
  constructor <;> intro addr v hv <;> rcases List.mem_cons.mp hv with hv | hv
  · cases hv; exact ha
  · exact h.1 _ _ hv
  · contradiction
  · exact h.2 _ _ hv

private theorem of_zero {base : Word w} {es : List (Event w)} (hz : countProbes es = 0) : Footprint base d es :=
  FlowFootprint.bounds_of_noProbes _ _ hz

private theorem scan_exists (pub : Fin (d+1) → Word w) (base : Word w) (m : Memory w)
    (ids : List (Fin d)) (off : ℕ) (fit : off+ids.length ≤ d) (rs : Regs w 8)
    (cursor : rs 2 = base + (off : Word w)) (one : rs 6 = 1) :
    ∃ es out, Flow.Exec pub base (DemandPreparation.scan ids) rs m es out m ∧
      choiceBits es = [] ∧ Footprint base d es := by
  induction ids generalizing off rs with
  | nil => exact ⟨[.tick],_,.line rfl,rfl,of_zero rfl⟩
  | cons i ids ih =>
    obtain ⟨mid,hr,_,inc,o⟩ := read_exec pub base m rs one i
    have ha : demandCell base d (rs 2).val := ⟨⟨off,by simp only [List.length_cons] at fit; omega⟩,by rw [cursor]⟩
    have cur : mid 2 = base + ((off+1 : ℕ) : Word w) := by rw [inc,cursor,Nat.cast_add,Nat.cast_one,add_assoc]
    obtain ⟨es,out,hs,bits,fp⟩ := ih (off+1) (by simp only [List.length_cons] at fit; omega) mid cur o
    refine ⟨_++es,out,.seq hr hs,?_,append (read (of_zero (by rfl)) ha _) fp⟩
    simpa [rowEvents,choiceBits] using bits

theorem energyPrefix (pub : Fin (d+1) → Word w) (base : Word w) {rs out : Regs w 8} {m m' es}
    (run : Flow.Exec pub base (DemandPreparation.energyPrefix d) rs m es out m') : Footprint base d es := by
  let a := Function.update rs 2 base
  let b := Function.update a 0 0
  let c := Function.update b 6 (1 : Word w)
  have h₁ : Flow.Exec pub base (.line (.stateWord 2)) rs m [.tick] a m := .line rfl
  have h₂ : Flow.Exec pub base (.line (.constant 0 0)) a m [.tick] b m := .line rfl
  have h₃ : Flow.Exec pub base (.line (.constant 6 1)) b m [.tick] c m := .line rfl
  obtain ⟨fs,last,hr,hb,fp⟩ := scan_exists pub base m (List.finRange d) 0 (by simp)
    c (by simp (config := {decide := true}) [c,b,a,Function.update]) (Function.update_self ..)
  have generated : Flow.Exec pub base (DemandPreparation.energyPrefix d) rs m
      (.tick :: .tick :: .tick :: fs) last m := .seq h₁ (.seq h₂ (.seq h₃ hr))
  rw [← FlowFootprint.events_eq generated hb run]
  exact tick (tick (tick fp))

private theorem private_exec {base : Word w} {r : ℕ} {pub : Fin k → Word w} {a : Flow r k}
    {rs m es out m'} (h : Flow.Exec pub base a rs m es out m') (pure : FlowFootprint.privateOnly a = true) :
    Footprint base d es := of_zero (FlowFootprint.noProbes pure h)

theorem repetition (pub : Fin (d+1) → Word w) (base : Word w) {rs out : Regs w 8} {m m' es}
    (run : Flow.Exec pub base (DemandPreparation.repetitionCall d) rs m es out m') : Footprint base d es := by
  cases run with
  | seq he hr => exact append (energyPrefix pub base he) (private_exec hr rfl)

private theorem compare (order : Fin d ≃ D) [Fintype D] (p : D → ℚ) (rows : Fin t → D → ℚ)
    (base : Word w) (j : Fin t) (i : Fin d) {rs out : Regs w 8} {m m' es}
    (run : Flow.Exec (GridRAM.coefficients order p rows) base (GridRAM.compareCoordinate order rows j i)
      rs m es out m') : Footprint base d es := by
  unfold GridRAM.compareCoordinate at run
  cases run with | seq h0 rest =>
  cases h0 with | line h0 =>
  simp only [Op.effect,Option.some.injEq,Prod.mk.injEq] at h0
  obtain ⟨rfl,rfl,rfl⟩ := h0
  cases rest with | seq h1 rest =>
  cases h1 with | line h1 =>
  simp only [Op.effect,Option.some.injEq,Prod.mk.injEq] at h1
  obtain ⟨rfl,rfl,rfl⟩ := h1
  cases rest with | seq h2 rest =>
  cases h2 with | line h2 =>
  simp only [Op.effect,Option.some.injEq,Prod.mk.injEq] at h2
  obtain ⟨rfl,rfl,rfl⟩ := h2
  cases rest with | seq h3 rest =>
  cases h3 with | line h3 =>
  simp only [Op.effect,Option.some.injEq,Prod.mk.injEq] at h3
  obtain ⟨rfl,rfl,rfl⟩ := h3
  apply tick ∘ tick ∘ tick
  apply read (private_exec rest ?_)
  · refine ⟨i,?_⟩
    simp (config := {decide := true}) [Function.update,coefficient_slot,BinaryOp.eval]
  · by_cases h : 0 ≤ rows j (order i) <;> simp only [h,↓reduceIte] <;> rfl

private theorem coords (order : Fin d ≃ D) [Fintype D] (p : D → ℚ) (rows : Fin t → D → ℚ)
    (base : Word w) (j : Fin t) (ids : List (Fin d)) {rs out : Regs w 8} {m m' es}
    (run : Flow.Exec (GridRAM.coefficients order p rows) base (coordinates order rows j ids)
      rs m es out m') : Footprint base d es := by
  induction ids generalizing rs m es with
  | nil => exact private_exec run rfl
  | cons i ids ih =>
    cases run with
    | seq hr hs => exact append (compare order p rows base j i hr) (ih hs)

private theorem table (order : Fin d ≃ D) [Fintype D] (p : D → ℚ) (rows : Fin t → D → ℚ)
    (base : Word w) (ids : List (Fin t)) {rs out : Regs w 8} {m m' es}
    (run : Flow.Exec (GridRAM.coefficients order p rows) base (rowsFrom order rows ids)
      rs m es out m') : Footprint base d es := by
  induction ids generalizing rs m es with
  | nil => exact private_exec run rfl
  | cons j js ih =>
    cases run with | seq init rest =>
    cases rest with | seq row choice =>
    apply append (private_exec init rfl) (append (coords order p rows base j _ row) ?_)
    cases choice with
    | ifEqYes _ h => exact tick (private_exec h rfl)
    | ifEqNo _ h =>
      cases h with | seq inc next => exact tick (append (private_exec inc rfl) (ih next))

theorem grid (order : Fin d ≃ D) [Fintype D] (p : D → ℚ) (rows : Fin t → D → ℚ)
    (base : Word w) {rs out : Regs w 8} {m m' es}
    (run : Flow.Exec (GridRAM.coefficients order p rows) base (GridRAM.grid order rows) rs m es out m') :
    Footprint base d es := by
  cases run with | seq h rest =>
  cases rest with | seq h' scan =>
  exact append (private_exec h rfl) (append (private_exec h' rfl) (table order p rows base _ scan))

theorem gridCode (order : Fin d ≃ D) [Fintype D] (p : D → ℚ) (rows : Fin t → D → ℚ)
    (pub : Fin (d+1) → Word w) (base : Word w) {rs out : Regs w 8} {m m' es}
    (run : Flow.Exec (Fin.append pub (GridRAM.coefficients order p rows)) base
      (DemandGridRAM.code order rows) rs m es out m') : Footprint base d es := by
  cases run with | seq energy test =>
  let data := Fin.append pub (GridRAM.coefficients order p rows)
  have left := (PrimedCounter.restrictExec (Function.Embedding.refl (Fin 8)) (Fin.castAdd (t*d*3))
    data (DemandPreparation.energyPrefix d) energy).1
  have right := (PrimedCounter.restrictExec (Function.Embedding.refl (Fin 8)) (Fin.natAdd (d+1))
    data (GridRAM.grid order rows) test).1
  have hl : data ∘ Fin.castAdd (t*d*3) = pub := funext fun _ => Fin.append_left ..
  have hr : data ∘ Fin.natAdd (d+1) = GridRAM.coefficients order p rows := funext fun _ => Fin.append_right ..
  exact append (energyPrefix pub base (hl ▸ left)) (grid order p rows base (hr ▸ right))

/-- Every successful native repetition call, at any fuel and choice input,
probes only the demand cells. -/
theorem repetitionMachine [Fintype D] (order : Fin d ≃ D) (p : D → ℚ) (L : ℕ) (base : Word w)
    (mem : Memory w) (fuel : ℕ) (bits : List Bool) (rep : Report w)
    (run : let machine := DemandPreparation.repetitionMachine order p L w
      execute machine.program fuel (machine.program.start base) mem bits = some rep) :
    Footprint base d rep.events := by
  obtain ⟨_,_,he,_⟩ := (Flow.template_execute_iff (DemandPreparation.repetitionCall d) (some 2)
    (DemandPreparation.publicWords order p L w) base (fun _ => 0) (fun _ => 0) mem fuel bits rep).mp run
  exact repetition _ base he

/-- Every successful native grid call reads within the same input rectangle. -/
theorem gridMachine [Fintype D] (order : Fin d ≃ D) (p : D → ℚ) (rows : Fin t → D → ℚ)
    (base : Word w) (mem : Memory w) (fuel : ℕ) (bits : List Bool) (rep : Report w)
    (run : let machine := DemandGridRAM.machine order p rows w
      execute machine.program fuel (machine.program.start base) mem bits = some rep) :
    Footprint base d rep.events := by
  obtain ⟨_,_,he,_⟩ := (Flow.template_execute_iff (DemandGridRAM.code order rows) (some 1)
    (Fin.append (DemandPreparation.publicWords order p 1 w) (GridRAM.coefficients order p rows))
    base (fun _ => 0) (fun _ => 0) mem fuel bits rep).mp run
  exact gridCode order p rows _ base he

end CompressorRecords.DemandFootprint

end VPVNP
end Computability
end OAI
