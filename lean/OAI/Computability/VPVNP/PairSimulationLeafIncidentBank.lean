import OAI.Computability.VPVNP.PairSimulationLeafIncidentScratch
import OAI.Computability.VPVNP.PairSimulationLeafFieldCopy

/-!
# Representing the full stack bank after loading the incident bits

The descending native copy stores the head of the logical list at its highest
address. Updating the incident stack's exclusive top therefore installs the
list with exactly the stack representation used by the interpreter.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafIncidentBank

open BurstRAM PrivateRAM RAMTape StackMachine PrimedInputRAM
open scoped Fin.CommRing

variable {K : Type} [DecidableEq K] {W p r : ℕ}

private theorem place_read (lo : ℕ) (xs : List Bool) (old : Word W → Word W)
    (fit : lo+xs.length ≤ 2^W) (i : Fin xs.reverse.length) :
    LeafFieldCopy.place lo xs old (LeafFieldCopy.word W (lo+i.val)) = encodeBit W xs.reverse[i.val] := by
  have hi : i.val < xs.length := by simpa using i.isLt
  let j := xs.length-1-i.val
  have hj : j < xs.length := by dsimp [j]; omega
  let tail := xs.drop (j+1)
  have hx : xs = xs.take j ++ xs[j] :: tail := by
    rw [show xs[j] :: tail = xs.drop j from List.getElem_cons_drop hj, List.take_append_drop]
  have hlen : tail.length = i.val := by simp only [tail,List.length_drop,j]; omega
  have atBit := LeafFieldCopy.place_at lo (xs.take j) xs[j] tail old (by rwa [← hx])
  rw [← hx, hlen] at atBit
  simpa only [List.getElem_reverse, j, PrivateFields.bitValue, encodeBit] using atBit

/-- Install one physical field in its own disjoint stack interval. -/
theorem placed_contents (L : Layout K W) (a : K) (s : Stacks K) (xs : List Bool)
    (old : Word W → Word W) (rep : L.Contents old s)
    (fit : ∀ j, (s j).length ≤ L.capacity) (room : xs.length ≤ L.capacity) :
    L.Contents (LeafFieldCopy.place (L.base a) xs old) (Function.update s a xs) := by
  have bound := ((Nat.add_le_add_left room _).trans_lt (L.fits a)).le
  apply LeafFill.contents_install L a s xs old _ rep fit
  · intro i
    exact place_read _ xs old bound i
  · intro u hu
    exact LeafFieldCopy.place_outside _ xs old u bound (hu.imp_right ((Nat.add_le_add_left room _).trans ·))

/-- Only the incident top pointer needs a new value. Scratch register
contents may change freely; the other base and top pointers keep their values. -/
theorem represents (L : Layout K W) (reg : Register K ↪ Fin r) (a : K) (s : Stacks K)
    (xs : List Bool) (c out : Config W p r) (rep : Represents L reg c s)
    (fit : ∀ j, (s j).length ≤ L.capacity) (room : xs.length ≤ L.capacity)
    (mem : out.privateMem = LeafFieldCopy.place (L.base a) xs c.privateMem)
    (top : out.reg (reg (.top a)) = L.address a xs.length)
    (regs : ∀ j : Register K, j ≠ .tmp → j ≠ .top a → out.reg (reg j) = c.reg (reg j)) :
    Represents L reg out (Function.update s a xs) := by
  refine ⟨(regs .one nofun nofun).trans rep.unit, (regs .zero nofun nofun).trans rep.zero,
    fun j => (regs (.base j) nofun nofun).trans (rep.bases j), ?_, ?_⟩
  · intro j
    by_cases h : j = a
    · subst j; simpa using top
    · simpa [Function.update_of_ne h] using (regs (.top j) nofun (by simpa using h)).trans (rep.tops j)
  · rw [mem]
    exact placed_contents L a s xs _ rep.cells fit room

/-- The exact private memory is determined by the old workspace and the
full bank. Outside both the scalar data and the new incident bits, stale
private cells keep their previous values. -/
theorem placed_memory (L : Layout K W) (a : K) (s : Stacks K) (xs : List Bool)
    (old scalar : Word W → Word W) (rep : L.Contents scalar s)
    (fit : ∀ j, (s j).length ≤ L.capacity) (room : xs.length ≤ L.capacity)
    (blank : s a = []) (hs : scalar = LeafLoadedBank.memory L s old) :
    LeafFieldCopy.place (L.base a) xs scalar = LeafLoadedBank.memory L (Function.update s a xs) old := by
  apply LeafLoadedBank.memory_eq L _ old _ (placed_contents L a s xs scalar rep fit room)
  · intro j
    by_cases hj : j = a <;> simp [hj,room,fit]
  · intro u outside
    have h := outside a
    rw [Function.update_self] at h
    rw [LeafFieldCopy.place_outside _ _ _ _ ((Nat.add_le_add_left room _).trans (L.fits a).le) h, hs]
    apply memory_outside
    intro j
    by_cases hj : j = a
    · subst j; rw [blank]; simp; omega
    · simpa [Function.update_of_ne hj] using outside j

variable {d e w k regs : ℕ}

set_option synthInstance.maxSize 10000 in
/-- Specialize the physical installation to the actual site-port layout.
The incident vector is precisely the field omitted by the scalar startup. -/
theorem fullBank (L : Layout (LeafStartup.Port regs k) W) (reg : Register (LeafStartup.Port regs k) ↪ Fin r)
    (x : VirtualSite.Input d e w) (args : Fin k → Word w) (c out : Config W p r)
    (rep : Represents L reg c (LeafRegisterBank.scalarBank LeafStartup.field x args))
    (fit : ∀ j, (LeafRegisterBank.scalarBank (LeafStartup.field (r := regs)) x args j).length ≤ L.capacity)
    (room : RAMLayout.width d (2^e) w ≤ L.capacity)
    (mem : out.privateMem = LeafFieldCopy.place (L.base (LeafLoadedBank.incidentPort regs k))
      (List.ofFn (RAMLayout.incidentBits x.sends x.v)) c.privateMem)
    (top : out.reg (reg (.top (LeafLoadedBank.incidentPort regs k))) =
      L.address (LeafLoadedBank.incidentPort regs k) (RAMLayout.width d (2^e) w))
    (regsEq : ∀ j : Register (LeafStartup.Port regs k), j ≠ .tmp → j ≠ .top (LeafLoadedBank.incidentPort regs k) →
      out.reg (reg j) = c.reg (reg j))
    (old : Word W → Word W)
    (hs : c.privateMem = LeafLoadedBank.memory L (LeafRegisterBank.scalarBank LeafStartup.field x args) old) :
    Represents L reg out (LeafStartup.bank regs x args) ∧
      out.privateMem = LeafLoadedBank.memory L (LeafStartup.bank regs x args) old := by
  let a := LeafLoadedBank.incidentPort regs k
  let s := LeafRegisterBank.scalarBank (LeafStartup.field (r := regs)) x args
  let xs := List.ofFn (RAMLayout.incidentBits x.sends x.v)
  have hroom : xs.length ≤ L.capacity := by simpa [xs] using room
  have htop : out.reg (reg (.top a)) = L.address a xs.length := by simpa only [a,xs,List.length_ofFn] using top
  have hb : s a = [] := by
    have he := (LeafLoadedBank.field_incident_iff (r := regs) (k := k) a).2 rfl
    simp [s, LeafRegisterBank.scalarBank, he, LeafRegisterBank.scalarField, LeafStartup.fieldBits]
  rw [← LeafLoadedBank.install_incident x args]
  exact ⟨represents L reg a s xs c out rep fit hroom mem htop regsEq,
    mem.trans (placed_memory L a s xs old c.privateMem rep.cells fit hroom hb hs)⟩

end PairSimulation.LeafIncidentBank

end VPVNP
end Computability
end OAI
