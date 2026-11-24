import OAI.Computability.VPVNP.PairSimulationLeafHandler

/-! # Reading the semantic occurrence at a physical cursor leaf -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafHandler

open BurstRAM CursorRouting CursorNetwork LeafStartup StackMachine DFS

set_option synthInstance.maxSize 10000

variable {d e w W endAddr : ℕ} [NeZero d]
  {A : PrimedInputRAM.Lengths} {n a H s : ℕ} {Q : PrimedInputRAM.Layout A n a H w}
  (D : PrimedCounter.Data Q s) (hw : 2 ≤ w) (hc : 2^d*2^e < 2^w)
  (storage : StackMachine.Layout (Port 52 34) W)
  (load : Word W → Scratch W endAddr → Input d e w W endAddr) (clock : ℕ)
  (node : Word W) (saved : Scratch W endAddr) (bits : List Bool)

theorem parser_suffix :
    let x := load node saved
    ((parser D hw hc storage load clock).read node saved bits).map Prod.snd =
      if Routed x then if x.pos.1 = 0 then
        acceptPrefix auxiliaryCode clock auxiliaryEntry (auxiliaryBank D hw hc x.pos x.buffers) bits
      else some bits else none := by
  intro x
  by_cases hr : Routed x
  · by_cases hz : x.pos.1 = 0
    · let bank := auxiliaryBank D hw hc x.pos x.buffers
      change ((if Routed x then _ else none) : Option (VisitPath W endAddr × List Bool)).map Prod.snd = _
      rw [ite_eq_left hr,ite_eq_left hr,ite_eq_left hz,ite_eq_left hz]
      let f := footprint storage auxiliaryCode clock auxiliaryEntry bank bits
      change (match parse auxiliaryCode clock auxiliaryEntry bank bits with
        | none => none
        | some y => if y.accept then some (⟨node,x.trace++f.events,(· = saved),fun _ => f.applyScratch endAddr x.prepared⟩,y.rest) else none : Option (VisitPath W endAddr × List Bool)).map Prod.snd =
          acceptPrefix auxiliaryCode clock auxiliaryEntry bank bits
      unfold acceptPrefix haltPrefix
      cases he : parse auxiliaryCode clock auxiliaryEntry bank bits with
      | none => rfl
      | some y => cases ok : y.accept <;> simp [ok]
    · simp only [parser,show load node saved = x from rfl,ite_eq_left hr,ite_eq_right hz,Option.map_some]
  · simp only [parser,show load node saved = x from rfl,ite_eq_right hr,Option.map_none]

/-- An actual private argument supplied by its parent uses the same suffix
as the leaf reader of the weighted occurrence expansion. This equality also
covers incompatible half-wire combinations, failed routes, and transit sites. -/
theorem parser_nomination (v : Position d) (z : (validatorNetwork d e w).Half v)
    (position : (load node saved).pos = v) (buffer : (load node saved).buffers = halfBuffers v z)
    (bound : steps 52 (auxiliary D hw hc v (halfBuffers v z)) ≤ clock) :
    ((parser D hw hc storage load clock).read node saved bits).map Prod.snd =
      ((nominationReader D hw hc v z clock bound).read bits).map Prod.snd := by
  rw [parser_suffix,nominationReader_suffix]
  simp only [Routed,position,buffer]

/-- The deterministic prefix supplies all external probes. A successful
cursor-zero call adds at most four native transitions per bounded stack
instruction, with the same bound on all choices and independent input bits. -/
theorem parser_work {job : VisitPath W endAddr} {tail : List Bool}
    (h : (parser D hw hc storage load clock).read node saved bits = some (job,tail)) :
    let x := load node saved
    countProbes job.trace = countProbes x.trace ∧ job.trace.length ≤ x.trace.length+4*clock := by
  intro x
  have append (as bs : List (Event W)) : countProbes (as++bs) = countProbes as+countProbes bs := by
    induction as with
    | nil => simp [countProbes]
    | cons a as ih => cases a <;> simp [countProbes,ih,Nat.add_assoc]
  by_cases hr : Routed (load node saved)
  · by_cases hz : (load node saved).pos.1 = 0
    · let bank := auxiliaryBank D hw hc x.pos x.buffers
      let f := footprint storage auxiliaryCode clock auxiliaryEntry bank bits
      simp only [parser,ite_eq_left hr,ite_eq_left hz] at h
      change (match parse auxiliaryCode clock auxiliaryEntry bank bits with
        | none => none
        | some y => if y.accept then some (⟨node,x.trace++f.events,(· = saved),fun _ => f.applyScratch endAddr x.prepared⟩,y.rest) else none) = some (job,tail) at h
      cases hp : parse auxiliaryCode clock auxiliaryEntry bank bits with
      | none => rw [hp] at h; contradiction
      | some y =>
        rw [hp] at h
        cases ok : y.accept with
        | false => simp only [ok,Bool.false_eq_true,↓reduceIte,reduceCtorEq] at h
        | true =>
          simp only [ok,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at h
          rw [← h.1,append,List.length_append]
          have probes : countProbes f.events = 0 := footprint_probes ..
          have time : f.events.length + 4*y.unused + 3 = 4*clock := (footprint_parse storage hp ok).2
          simp only [probes,Nat.add_zero,true_and]
          omega
    · simp only [parser,ite_eq_left hr,ite_eq_right hz,Option.some.injEq,Prod.mk.injEq] at h
      rw [← h.1]
      exact ⟨rfl,Nat.le_add_right _ _⟩
  · simp only [parser,ite_eq_right hr,reduceCtorEq] at h

end PairSimulation.LeafHandler

end VPVNP
end Computability
end OAI
