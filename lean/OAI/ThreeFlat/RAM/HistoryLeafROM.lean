import OAI.ThreeFlat.RAM.HistoryLeafDispatch
import OAI.ThreeFlat.RAM.TraceEndpointFixed
import OAI.ThreeFlat.RAM.HeaderScan

namespace OAI
/-! # The concrete selected-leaf reader for all trace and motif leaves -/

namespace ThreeFlat.RAM.HistoryLeafDispatch

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr
open scoped Fin.CommRing

/-- `initial` may include the public-suffix projection of the H trace. All
three leaf kinds retain a single row ABI and the same finite table library. -/
def mountedLeaves {w k : ℕ} (initial : Term w k 4) : Term w (k+1) 1 :=
  term (initial.mapPublic Fin.castSucc) (Fin.last k)

theorem mountedLeaves_binds {w k : ℕ} (initial : Term w k 4) :
    (mountedLeaves initial).binds≤ initial.binds+160 := by
  simpa only [mountedLeaves,Term.binds_mapPublic] using
    binds_le (initial.mapPublic Fin.castSucc) (Fin.last k)

/-- The fixed trace decoder consumes its parameter bank, and the last slot
contains the physical address of the current leaf header. -/
def params := TraceEndpointROM.params+1

def allLeaves (w : ℕ) : Term w params 1 := mountedLeaves (TraceEndpointROM.fixed w)

theorem allLeaves_binds (w : ℕ) : (allLeaves w).binds ≤ 1000394 :=
  (mountedLeaves_binds (TraceEndpointROM.fixed w)).trans (by have := TraceEndpointROM.fixed_binds w; omega)

/-- A six-word leaf header extends the five input words by the number of
output words. A persistent current-header pointer supplies the scan bounds. -/
def scan (w : ℕ) (pointer : Word w) := HeaderScan.block (allLeaves w) pointer 4 5

/-- `pointer` itself is used in one boot instruction. Its value and the
public leaf-header address are independent of the row ordinal. -/
theorem scan_run {w P R K : ℕ} (pointer : Word w) (lo n : ℕ) (stop : lo+n<2^w)
    (pc : Fin (13+(allLeaves w).labels) ↪ Fin P) (reg : Fin (4+(allLeaves w).binds) ↪ Fin R)
    (φ : Fin params → Fin K) (exit : Fin P) (M : Machine w P R K)
    (installed : (scan w pointer).Installed M pc reg φ exit)
    (c : Config w P R) (m₀ : Memory w) (start : c.pc=pc (scan w pointer).first)
    (word : ℕ → Word w) (lowWord : m₀ (m₀ pointer.val + (4 : Word w)).val = (lo : Word w))
    (lenWord : m₀ (m₀ pointer.val + (5 : Word w)).val = (n : Word w))
    (correct : ∀ (a : Word w) (m : Memory w), lo≤a.val → a.val<lo+n →
      DescriptorScan.agreesOutside lo (lo+n) m m₀ →
      (allLeaves w).eval (M.publicData ∘ φ) m (fun _ => a) = word a.val) :
    ∃ steps ≤ 13+n*2000792, ∃ out : Config w P R, out.pc=exit ∧
      advance M.program steps c m₀ = some (out,fillSegment lo n word m₀) := by
  obtain ⟨s,hs,out,hpc,hr⟩ := HeaderScan.advance_block (allLeaves w) pointer 4 5 lo n stop pc reg φ exit M installed c m₀ start word lowWord lenWord correct
  exact ⟨s,hs.trans (Nat.add_le_add_left (Nat.mul_le_mul_left n (by have h := allLeaves_binds w; omega)) 13),out,hpc,hr⟩


end ThreeFlat.RAM.HistoryLeafDispatch

end OAI
