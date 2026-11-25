import OAI.Hierarchy.DescentExteriorHopSnapshots
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # The original finite incidence order initializes exterior ancestry -/

namespace Hierarchy.DescentExteriorReplay.Snapshots
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
variable {n w : ℕ}

def seedData (rank : Fin n → ℕ) (i : ℕ) := if h : i<n then rank ⟨i,h⟩ else 0
def seedProgram (w scratch : ℕ) (rank : Fin n → ℕ) :=
  DescentStaticWordColumn.program w scratch (seedData rank) n
def seedImage (scratch : ℕ) (rank : Fin n → ℕ) (input : Memory w) :=
  DescentStaticWordColumn.image scratch (seedData rank) input n

theorem seed_run (scratch : ℕ) (rank : Fin n → ℕ) (input : Memory w)
    (room : scratch+stride n < 2^w) :
    (seedProgram w scratch rank).Exec input (seedImage scratch rank input) (4+10*n) ∧
    CheapCode (seedProgram w scratch rank) ∧
    DescentStaticWordColumn.names (seedProgram w scratch rank)=15*(n+1) := by
  have enough : n+1≤ stride n := Nat.le_pow_clog (by decide) _
  exact ⟨DescentStaticWordColumn.mount scratch n _ input (by omega),
    DescentStaticWordColumn.cheap w scratch _ n,DescentStaticWordColumn.names_mount w scratch _ n⟩

theorem seed_read (scratch : ℕ) (rank : Fin n → ℕ) (input : Memory w)
    (room : scratch+stride n < 2^w) (i : Fin n) :
    (page scratch n 0).read (seedImage scratch rank input) (i.val:Word w)=(rank i:Word w) := by
  have enough : n+1≤ stride n := Nat.le_pow_clog (by decide) _
  have bound : i.val<stride n := lt_of_lt_of_le (by omega) enough
  change (seedImage scratch rank input) (scratch+0*stride n+(i.val:Word w).val%stride n)=_
  rw [Fin.val_cast_of_lt (by omega),Nat.mod_eq_of_lt bound,Nat.zero_mul,Nat.add_zero]
  have value : seedData rank i.val = rank i := by
    unfold seedData
    rw [dite_eq_left i.isLt]
  change DescentStaticWordColumn.image scratch (seedData rank) input n (scratch+i.val) =
    (rank i : Word w)
  exact (DescentStaticWordColumn.read scratch n (seedData rank) input i.isLt).trans
    (congrArg (fun k : ℕ => (k : Word w)) value)

theorem seed_low (scratch : ℕ) (rank : Fin n → ℕ) (input : Memory w) (a : ℕ) (low : a<scratch) :
    seedImage scratch rank input a=input a := DescentStaticWordColumn.frame scratch n _ input a (Or.inl low)

end Hierarchy.DescentExteriorReplay.Snapshots

end OAI
