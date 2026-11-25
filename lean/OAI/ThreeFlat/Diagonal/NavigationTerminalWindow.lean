import OAI.ThreeFlat.Diagonal.NavigationHistoryWindow
import OAI.ThreeFlat.RAM.TerminalWireArchive

namespace OAI
/-! # The original bit window and terminal width-scan room of a navigation archive -/

namespace ThreeFlat.Diagonal.NavigationPass.Archive
open Computability.VPVNP.BurstRAM PrivateRAM RAM NavigationDirectory
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {W : ℕ}

structure RawWindow (A : Archive) (steps : List Stage) (bits : ℕ→Bool) (input : Memory W) : Prop where
  phase : A.phase<A.seed
  old : A.oldHistory+A.pairCapacity≤A.seed
  fresh : A.newHistory+A.pairCapacity≤A.seed
  bits : ∀ j<A.pairCapacity,input ((A.hist steps).source input+j)=(bits j).toNat

theorem RawWindow.terminal {A : Archive} {steps : List Stage} {bits : ℕ→Bool} {input mid : Memory W}
    (edges : ℕ) (h : A.RawWindow steps bits input) (small : 1<2^W)
    (same : ∀i,i<A.seed→mid i=input i) :
    let x:=A.terminal steps edges W
    let tail:=(List.ofFn (fun j : Fin A.pairCapacity=>bits j.val)).drop (W*A.histWords steps)
    ∀ i : Fin tail.length,mid ((if (mid x.phase).val=1 then x.newSource else x.oldSource)+i.val)=0 ↔ tail.get i=false := by
  intro x tail i
  let H:=W*A.histWords steps
  have ix : i.val<A.pairCapacity-H := by simpa [tail,H] using i.isLt
  let j:=H+i.val
  have hj : j<A.pairCapacity := by dsimp [j];omega
  have one : (1:Word W).val=1 := Fin.val_cast_of_lt small
  have iffOne : (input A.phase).val=1 ↔ input A.phase=1 := by rw [←Fin.val_inj,one]
  have value : tail.get i=bits j := by
    change ((List.ofFn (fun n : Fin A.pairCapacity=>bits n.val)).drop H)[i.val]=_
    rw [List.getElem_drop,List.getElem_ofFn]
  have adr : (if (mid x.phase).val=1 then x.newSource else x.oldSource)+i.val=(A.hist steps).source input+j := by
    change (if (mid A.phase).val=1 then A.newHistory+H else A.oldHistory+H)+i.val =
      (if input A.phase=1 then A.newHistory else A.oldHistory)+(H+i.val)
    rw [same A.phase h.phase]
    by_cases tag : input A.phase=1
    · simp only [ite_eq_left tag,ite_eq_left (iffOne.mpr tag),Nat.add_assoc]
    · simp only [ite_eq_right tag,ite_eq_right (fun eq => tag (iffOne.mp eq)),Nat.add_assoc]
  have bound : (A.hist steps).source input+j<A.seed := by
    change (if input A.phase=1 then A.newHistory else A.oldHistory)+j<A.seed
    by_cases tag : input A.phase=1
    · rw [ite_eq_left tag]
      exact (Nat.add_lt_add_left hj _).trans_le h.fresh
    · rw [ite_eq_right tag]
      exact (Nat.add_lt_add_left hj _).trans_le h.old
  rw [adr,same _ bound,h.bits j hj,value]
  have positiveWidth : W ≠ 0 := by
    rintro rfl
    norm_num at small
  cases bits j <;> simp [positiveWidth]

/-- The accepted stage memory remains the witness for the complete chronological
journal. Terminal prefix words can then be read directly in the emitted image. -/
structure TerminalRoom (A : Archive) (steps : List Stage) (edges W : ℕ) : Prop where
  bounds : TerminalWireArchive.Bounds (A.terminal steps edges W) W
  header : (finish A.K steps A.cursor).header < (finish A.K steps A.cursor).heap
  control : (finish A.K steps A.cursor).heap+edges<A.control
  seed : A.seed≤(finish A.K steps A.cursor).heap

def terminalTime (x : TerminalWireArchive.Layout) :=
  (11+(x.edges+1)*(2*(TerminalWireArchive.prefixWord x).work+4))+
    (6+(x.capacity+1)*(2*(TerminalWireArchive.checkWord x).work+4))

end
end ThreeFlat.Diagonal.NavigationPass.Archive

end OAI
