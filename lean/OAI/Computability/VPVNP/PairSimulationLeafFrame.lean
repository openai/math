import OAI.Computability.VPVNP.PairSimulationLeafHandler
import OAI.Computability.VPVNP.PairSimulationVertexJobs
import OAI.Computability.VPVNP.PairPendingArguments
import OAI.Computability.VPVNP.PairSimulationLeafArena

/-!
# The private-memory frame of a cursor leaf visit

All writes made by the bounded stack program lie inside its own stack
intervals. In particular a successful leaf preserves the earlier private
histogram and the stored arguments of other pending vertices, cell by cell,
whenever the deterministic input preparation preserves those cells.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.StackMachine

open BurstRAM RAMTape DFS
open scoped Fin.CommRing

variable {W endAddr : ℕ} {K Q : Type} [DecidableEq K]

/-- Even a partial or rejected prefix only writes inside the designated
intervals. Each source step can increase any one stack by at most one. -/
theorem footprint_writes_inside (L : Layout K W) (code : StackCode K Q) (fuel : ℕ)
    (q : Q) (s : Stacks K) (bits : List Bool) (room : ∀ j, (s j).length+fuel ≤ L.capacity) :
    ∀ write ∈ (footprint L code fuel q s bits).writes,
      ∃ j, L.base j ≤ write.1.val ∧ write.1.val < L.base j + L.capacity := by
  induction fuel generalizing q s bits with
  | zero => simp [footprint]
  | succ fuel ih =>
    have dec (j : K) : (s j).length+fuel ≤ L.capacity := Nat.le_trans (by omega) (room j)
    cases op : code q with
    | push j b next =>
      have can : (s j).length < L.capacity := by have := room j; omega
      have after (k : K) : ((Function.update s j (b :: s j)) k).length + fuel ≤ L.capacity := by
        by_cases hk : k = j
        · subst k; simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using room j
        · simpa [Function.update_of_ne hk] using dec k
      intro write mem
      rcases List.mem_cons.mp (show write ∈ (_,_) :: (footprint L code fuel next _ bits).writes from
        by simpa only [footprint, op, Footprint.prepend, List.cons_append, List.nil_append] using mem)
        with first | later
      · subst write
        exact ⟨j, by rw [L.address_val j can.le]; omega, by rw [L.address_val j can.le]; omega⟩
      · exact ih _ _ _ after _ later
    | pop j next =>
      have after (k : K) : ((Function.update s j (s j).tail) k).length + fuel ≤ L.capacity := by
        by_cases hk : k = j
        · subst k; simp only [Function.update_self, List.length_tail]; have := dec j; omega
        · simpa [Function.update_of_ne hk] using dec k
      simpa only [footprint, op, Footprint.prepend, List.nil_append] using
        ih (next (s j).head?) _ bits after
    | goto next =>
      simpa only [footprint, op, Footprint.prepend, List.nil_append] using ih next s bits dec
    | choose low high =>
      cases bits with
      | nil => simp [footprint, op]
      | cons b bs =>
        simpa only [footprint, op, Footprint.prepend, List.nil_append] using ih (if b then high else low) s bs dec
    | halt b => simp [footprint, op]

private theorem applyWrites_away (f : Footprint W) (mem : Word W → Word W) (a : Word W)
    (away : ∀ write ∈ f.writes, a ≠ write.1) : f.applyWrites mem a = mem a := by
  obtain ⟨events,writes⟩ := f
  change ∀ write ∈ writes, a ≠ write.1 at away
  unfold Footprint.applyWrites
  dsimp only
  induction writes generalizing mem with
  | nil => rfl
  | cons write writes ih =>
    rw [List.foldl_cons, ih _ (fun v h => away v (List.mem_cons_of_mem _ h)),
      Function.update_of_ne (away write List.mem_cons_self)]

/-- Cell-level scratch frame on every stream, for use by the DFS histogram
and by any remaining pending argument packets. -/
theorem footprint_scratch_outside (L : Layout K W) (code : StackCode K Q) (fuel : ℕ)
    (q : Q) (s : Stacks K) (bits : List Bool) (room : ∀ j, (s j).length+fuel ≤ L.capacity)
    (saved : Scratch W endAddr) (cell : {a : Word W // endAddr ≤ a.val})
    (outside : ∀ j, cell.val.val < L.base j ∨ L.base j + L.capacity ≤ cell.val.val) :
    (footprint L code fuel q s bits).applyScratch endAddr saved cell = saved cell := by
  unfold Footprint.applyScratch
  rw [applyWrites_away _ _ _ (by
    intro write hw eqn
    obtain ⟨j,lo,hi⟩ := footprint_writes_inside L code fuel q s bits room write hw
    rw [← eqn] at lo hi
    rcases outside j with h | h <;> omega)]
  simp [cell.property]

end PairSimulation.StackMachine

namespace PairSimulation.LeafHandler

open BurstRAM PrivateRAM CursorRouting CursorNetwork LeafStartup StackMachine DFS
open LocalHistory NodeArguments
open scoped Fin.CommRing

variable {d e w W endAddr : ℕ} [NeZero d]
  {L : PrimedInputRAM.Lengths} {n ai H s : ℕ} {Q : PrimedInputRAM.Layout L n ai H w}
  (D : PrimedCounter.Data Q s) (hw : 2 ≤ w) (hc : 2^d*2^e < 2^w)
  (storage : StackMachine.Layout (Port 52 34) W)
  (load : Word W → Scratch W endAddr → Input d e w W endAddr) (clock : ℕ)
  (node : Word W) (saved : Scratch W endAddr) (bits tail : List Bool)
  (job : VisitPath W endAddr)

/-- The leaf's trace, its enabling scratch, and the cells it preserves are
all determined by the actual native stack path. -/
theorem parser_observations
    (hit : (parser D hw hc storage load clock).read node saved bits = some (job,tail))
    (det : choiceBits (load node saved).trace = [])
    (room : ∀ j, (auxiliaryBank D hw hc (load node saved).pos (load node saved).buffers j).length + clock ≤ storage.capacity) :
    job.node = node ∧ (∀ old, job.enabled old ↔ old = saved) ∧ bits = choiceBits job.trace ++ tail ∧
      ∀ cell : {a : Word W // endAddr ≤ a.val},
        (∀ j, cell.val.val < storage.base j ∨ storage.base j + storage.capacity ≤ cell.val.val) →
          job.update saved cell = (load node saved).prepared cell := by
  let x := load node saved
  by_cases route : Routed x
  · by_cases hz : x.pos.1 = 0
    · let bank := auxiliaryBank D hw hc x.pos x.buffers
      let fp := footprint storage auxiliaryCode clock auxiliaryEntry bank bits
      change (if Routed x then _ else none) = some (job,tail) at hit
      rw [ite_eq_left route, ite_eq_left hz] at hit
      change (match parse auxiliaryCode clock auxiliaryEntry bank bits with
        | none => none
        | some y => if y.accept then some (⟨node,x.trace++fp.events,(· = saved),fun _ => fp.applyScratch endAddr x.prepared⟩,y.rest) else none) =
          some (job,tail) at hit
      cases hp : parse auxiliaryCode clock auxiliaryEntry bank bits with
      | none => rw [hp] at hit; contradiction
      | some y =>
        rw [hp] at hit
        cases ok : y.accept with
        | false => simp [ok] at hit
        | true =>
          obtain ⟨rfl,rfl⟩ := (by simpa only [ok,↓reduceIte,Option.some.injEq,Prod.mk.injEq] using hit.symm :
            job = ⟨node,x.trace++fp.events,(· = saved),fun _ => fp.applyScratch endAddr x.prepared⟩ ∧ tail = y.rest)
          refine ⟨rfl, fun _ => Iff.rfl, ?_, fun cell away =>
            footprint_scratch_outside storage auxiliaryCode clock auxiliaryEntry bank bits room x.prepared cell away⟩
          change bits = choiceBits (x.trace ++ fp.events) ++ y.rest
          rw [PrimedInputRAM.Flow.choiceBits_append,show choiceBits x.trace = [] from det,List.nil_append]
          exact (footprint_parse storage hp ok).1
    · have pair : job = ⟨node,x.trace,(· = saved),fun _ => x.prepared⟩ ∧ tail = bits := by
        simpa only [parser,show load node saved = x from rfl,ite_eq_left route,ite_eq_right hz,
          Option.some.injEq,Prod.mk.injEq] using hit.symm
      obtain ⟨rfl,rfl⟩ := pair
      exact ⟨rfl,fun _ => Iff.rfl,by change _ = choiceBits x.trace ++ _; rw [show choiceBits x.trace = [] from det]; rfl,fun _ _ => rfl⟩
  · simp only [parser,show load node saved = x from rfl,ite_eq_right route,reduceCtorEq] at hit


/-- Every other pending packet below the virtual stack intervals retains
the bit values established by the deterministic input preparation. -/
theorem parser_pending
    (hit : (parser D hw hc storage load clock).read node saved bits = some (job,tail))
    (det : choiceBits (load node saved).trace = [])
    (room : ∀ j, (auxiliaryBank D hw hc (load node saved).pos (load node saved).buffers j).length + clock ≤ storage.capacity)
    (arena : Arena) (q : Packet) (fits : q.Fits arena W endAddr)
    (below : ∀ j, arena.base q.node + q.bits.length ≤ storage.base j)
    (prefixStored : q.Stored arena (load node saved).prepared) :
    q.Stored arena (job.update saved) := by
  apply prefixStored.congr
  intro i
  let a : Word W := ((arena.base q.node + i.val : ℕ) : Word W)
  have val : a.val = arena.base q.node+i.val :=
    Nat.mod_eq_of_lt ((Nat.add_lt_add_left i.isLt _).trans_le fits.2.2)
  have above : endAddr ≤ a.val := val ▸ fits.1.trans (Nat.le_add_right _ _)
  have frame := (parser_observations D hw hc storage load clock node saved bits tail job hit det room).2.2.2
    ⟨a,above⟩ (fun j => Or.inl (val ▸ (Nat.add_lt_add_left i.isLt _).trans_le (below j)))
  change rawScratch (job.update saved) a = rawScratch (load node saved).prepared a
  simpa only [rawScratch, dite_eq_left above] using frame


/-- Realize a selected zero-label occurrence after the suffix comparison.
This proof is independent of how the original cursor factors were transported. -/
theorem realizes_zero {Label α : Type} (reader : CompressorRecords.ChoiceReader α)
    (power : α → Label → ℕ) (zero : ∀ x label, power x label = 0) (address : ℕ)
    (addr : node.val = address)
    (accept : ∀ x suffix, ∃ actual, (parser D hw hc storage load clock).read node saved
      (reader.encode x ++ suffix) = some (actual,suffix))
    (cell : Label → {a : Word W // endAddr ≤ a.val})
    (away : ∀ label j, (cell label).val.val < storage.base j ∨
      storage.base j+storage.capacity ≤ (cell label).val.val)
    (det : choiceBits (load node saved).trace = [])
    (prefixFrame : ∀ label, (load node saved).prepared (cell label) = saved (cell label))
    (room : ∀ j, (auxiliaryBank D hw hc (load node saved).pos (load node saved).buffers j).length+clock ≤ storage.capacity)
    (x : α) (suffix : List Bool) :
    ∃ actual, (parser D hw hc storage load clock).read node saved (reader.encode x ++ suffix) = some (actual,suffix) ∧
      actual.enabled saved ∧ RealizesJob (fun old label => (old (cell label)).val) ⟨address,reader.encode x,power x⟩ actual := by
  obtain ⟨actual,hit⟩ := accept x suffix
  obtain ⟨num,enabled,consumed,frame⟩ := parser_observations D hw hc storage load clock node saved
    (reader.encode x ++ suffix) suffix actual hit det room
  refine ⟨actual,hit,(enabled saved).mpr rfl,⟨?_,(List.append_cancel_right consumed).symm,?_⟩⟩
  · change actual.node = (address : Word W)
    rw [num,← addr]
    simp
  · intro old h label
    have eqn := (enabled old).mp h
    subst old
    change (actual.update saved (cell label)).val = (saved (cell label)).val + power x label
    rw [frame (cell label) (away label),prefixFrame label,zero,Nat.add_zero]

end PairSimulation.LeafHandler

namespace PairSimulation.LeafArena

open BurstRAM DFS NodeArguments
open scoped Fin.CommRing

private theorem hist_lt (R : Regions) (i : Fin R.histWords) : R.histBase+i.val < R.stackBase := by
  have h := (Nat.add_lt_add_left i.isLt R.histBase).trans_le R.hist_before
  exact h.trans_le (Nat.le_add_right _ _)

/-- A real histogram cell of the private layout, above the DFS stack and
strictly before the operand cache and all verifier stacks. -/
def Regions.histCell {W endAddr : ℕ} (R : Regions) (h : R.stackBase ≤ 2^W)
    (above : endAddr ≤ R.histBase) (i : Fin R.histWords) : {a : Word W // endAddr ≤ a.val} :=
  ⟨((R.histBase+i.val : ℕ) : Word W), by
    change endAddr ≤ (R.histBase+i.val) % 2^W
    rw [Nat.mod_eq_of_lt ((hist_lt R i).trans_le h)]
    exact above.trans (Nat.le_add_right _ _)⟩

theorem Regions.histCell_below {W endAddr ports : ℕ} {K : Type}
    (R : Regions) (order : K ↪ Fin ports) (capacity : ℕ) (fit : R.stackBase + ports*capacity < 2^W)
    (above : endAddr ≤ R.histBase) (i : Fin R.histWords) (j : K) :
    (R.histCell (W := W) ((Nat.le_add_right _ _).trans fit.le) above i).val.val <
      (R.layout order capacity fit).base j := by
  change (R.histBase+i.val) % 2^W < _
  have lo := hist_lt R i
  rw [Nat.mod_eq_of_lt (lo.trans_le ((Nat.le_add_right _ _).trans fit.le))]
  exact lo.trans_le (R.stack_above order capacity fit j)

/-- A still-pending argument packet is below every verifier stack in the
same allocated layout, regardless of its assigned bits. -/
theorem Regions.packet_below {W endAddr ports : ℕ} {K : Type} (R : Regions) (order : K ↪ Fin ports)
    (capacity : ℕ) (fit : R.stackBase + ports*capacity < 2^W) (q : Packet)
    (hq : q.node < R.nodes) (fitted : q.Fits R.arguments W endAddr) (j : K) :
    R.arguments.base q.node + q.bits.length ≤ (R.layout order capacity fit).base j := by
  apply (le_trans _ (R.stack_above order capacity fit j))
  have h := (Nat.add_le_add_left fitted.2.1 _).trans (R.node_before hq)
  unfold Regions.stackBase Regions.cacheBase
  omega

end PairSimulation.LeafArena

end VPVNP
end Computability
end OAI
