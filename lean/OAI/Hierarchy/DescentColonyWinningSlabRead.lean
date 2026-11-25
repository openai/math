import OAI.Hierarchy.DescentWinningRows
import OAI.Hierarchy.DescentColonyWinningSlabs
import OAI.Hierarchy.DescentColonyMaterialized

namespace OAI
/-! # The winning multiplier's physical slabs after materializing its columns -/

noncomputable section
namespace Hierarchy.DescentColonies.WinningSlabs.Selected
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM NativeBatch
open DescentGL (Bits Nonzero)
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators
variable {G H k w : ℕ}

def flags (base : ℕ) (g : Fin G) (v : Fin H) (d : Fin k) := Materialized.dest base ((g,v),some d)

def amounts (k base : ℕ) (g : Fin G) (v : Fin H) := Materialized.dest (k:=k) base ((g,v),none)

def slabBase (G H k base : ℕ) := Materialized.endAt G H k base

def endAt (G H k base : ℕ) := worldEnd G H k (slabBase G H k base)

def dest (base : ℕ) (i : Slot G H k) := ptr k (slabBase G H k base) i.val

theorem dest_end (base : ℕ) (i : Slot G H k) : dest base i+2^k≤endAt G H k base := slot_end _ i

def code (w G H k base : ℕ) : Code w :=
  let ps := worldPasses k (slabBase G H k base) (flags (G:=G) (H:=H) base) (amounts k base)
  ⟨ProtocolRAM.program w ps,result ps,clock ps⟩

def program (w base : ℕ) (raw : Fin G→Fin H→ℕ) (a : Bits k) :=
  (Materialized.program w base raw a).thenDo (code w G H k base)

private theorem room_before (base : ℕ) (room : endAt G H k base<2^w) : Materialized.endAt G H k base<2^w :=
  (Nat.le_add_right _ _).trans_lt room

private theorem fits (base : ℕ) (s : Materialized.Slot G H k) (room : endAt G H k base<2^w) :
    (Bank.mk (Materialized.dest base s) k).Fits w (slabBase G H k base) := by
  have b := Materialized.dest_end base s
  have r := room_before base room
  exact ⟨Nat.two_pow_pos _,by change 2^k<2^w;omega,b⟩

theorem run (base : ℕ) (raw : Fin G→Fin H→ℕ) (a : Bits k) (m : Memory w)
    (oldRaw : ∀g v,raw g v+2^k≤base) (room : endAt G H k base<2^w) :
    (program w base raw a).text.Exec m ((program w base raw a).after m) (program w base raw a).ticks := by
  intro labels registers slots machine
  exact Procedure.Exec.then (Materialized.run base raw a m oldRaw (room_before base room))
    (world_run _ _ _ _ _ (fun g v d=>fits base ((g,v),some d) room) (fun g v=>fits base ((g,v),none) room) room) machine

/-- Reads the combined program after the seed search, using only raw old tape
values, fit bounds, and the recorded winning seed word. -/
theorem published (base D cap : ℕ) (a : Bits k) (income : Fin H→List (Fin H))
    (loadPtr raw : Fin G→Fin H→ℕ) (m : Memory w) (weight amount : Fin G→Fin H→Block k→ℕ)
    (old : ∀g v,loadPtr g v+2^k≤base) (oldRaw : ∀g v,raw g v+2^k≤base)
    (room : endAt G H k base<2^w) (cf : cap<2^w)
    (inputs : ∀g v (x : Block k),m (loadPtr g v+x.val)=(weight g v x:Word w))
    (values : ∀g v (x : Block k),m (raw g v+x.val)=(amount g v x:Word w))
    («partial» : ∀(ν : Nonzero k) g d,d<k→∀v x,(Scan.readWeights (multiplierLoad (weight g) a ν.val) d v x).sum<2^w)
    (μ : Nonzero k) (found : AllSeedsRAM.afterSearch base D cap a income loadPtr m (WinningColumns.winnerPtr G H k base)=
      (MultiplierMinimumRAM.key μ:Word w)) (i : Slot G H k) (x : Block k) :
    (program w base raw a).after (AllSeedsRAM.afterSearch base D cap a income loadPtr m) (dest base i+x.val)=
      (worldValue (winningRows income weight D cap a μ) (winningAmounts amount a μ) i x:Word w) := by
  have source := Materialized.published base D cap a income loadPtr raw m weight amount old oldRaw
    (room_before base room) cf inputs values «partial» μ found
  apply world_read k (slabBase G H k base) (flags base) (amounts k base)
  · exact fun g v d=>fits base ((g,v),some d) room
  · exact fun g v=>fits base ((g,v),none) room
  · exact fun g v d x=>source ((g,v),some d) x
  · exact fun g v x=>source ((g,v),none) x

theorem support (income : Fin H→List (Fin H)) (weight amount : Fin G→Fin H→Block k→ℕ) (D cap : ℕ)
    (a : Bits k) (μ : Nonzero k) :
    (positive (winningRows income weight D cap a μ) (winningAmounts amount a μ)).card ≤
      ∑ g,Scan.leafScore income (multiplierLoad (weight g) a μ.val) D cap :=
  score_support income (fun g=>multiplierLoad (weight g) a μ.val) (winningAmounts amount a μ) D cap

/-- Execute the multiplier search, select its columns, and emit all dyadic
slabs from the original load and outgoing tapes in one trace. -/
theorem from_inputs (base D cap : ℕ) (a : Bits k) (income : Fin H→List (Fin H))
    (loadPtr raw : Fin G→Fin H→ℕ) (m : Memory w) (weight amount : Fin G→Fin H→Block k→ℕ)
    (hk : 0<k) (old : ∀g v,loadPtr g v+2^k≤base) (oldRaw : ∀g v,raw g v+2^k≤base)
    (room : endAt G H k base<2^w) (cf : cap<2^w) (bill : G*(H*2^k)<2^w)
    (B : ℕ) (reserve : 2^k*B<2^w) (limit : ∀g v x,weight g v x≤B)
    (inputs : ∀g v (x : Block k),m (loadPtr g v+x.val)=(weight g v x:Word w))
    (values : ∀g v (x : Block k),m (raw g v+x.val)=(amount g v x:Word w)) :
    let Q := uniformColonyScore income weight D cap a
    let search := AllSeedsRAM.search w base D cap a income loadPtr
    let cols := Materialized.program w base raw a
    let slabs := code w G H k base
    let tape := (program w base raw a).after (AllSeedsRAM.afterSearch base D cap a income loadPtr m)
    ∃ μ : Nonzero k,((search.1.seq cols.text).seq slabs.text).Exec m tape (search.2+cols.ticks+slabs.ticks) ∧
      (scanMinimum Q (nonzeroWords k)).1=some (μ,Q μ) ∧ (∀ν,Q μ≤Q ν) ∧
      (∀i (x : Block k),tape (dest base i+x.val)=
        (worldValue (winningRows income weight D cap a μ) (winningAmounts amount a μ) i x:Word w)) ∧
      (positive (winningRows income weight D cap a μ) (winningAmounts amount a μ)).card≤Q μ ∧
      ∀z<base,tape z=m z := by
  obtain ⟨μ,exec,pick,best,source,keep⟩ := Materialized.from_inputs base D cap a income loadPtr raw m
    weight amount hk old oldRaw (room_before base room) cf bill B reserve limit inputs values
  have fs := fun (g : Fin G) (v : Fin H) (d : Fin k) => fits base ((g,v),some d) room
  have am := fun (g : Fin G) (v : Fin H) => fits base ((g,v),none) room
  refine ⟨μ,?_,pick,best,?_,support income weight amount D cap a μ,?_⟩
  · intro labels registers slots machine
    exact Procedure.Exec.then exec
      (world_run k (slabBase G H k base) (flags base) (amounts k base) _ fs am room) machine
  · intro i x
    exact world_read k (slabBase G H k base) (flags base) (amounts k base)
      (winningRows income weight D cap a μ) (winningAmounts amount a μ) _ fs am
      (fun g v d y=>source ((g,v),some d) y) (fun g v y=>source ((g,v),none) y) i x
  · intro z hz
    have inputEnd : z<AllSeedsRAM.gatherBase G H k base := hz.trans_le (Nat.le_add_right ..)
    have scoreEnd : z<AllSeedsRAM.winningBase G H k base := inputEnd.trans_le (Nat.le_add_right ..)
    have headerEnd : z<Materialized.first G H k base := scoreEnd.trans_le (Nat.le_add_right ..)
    have before : z<slabBase G H k base := headerEnd.trans_le (Nat.le_add_right ..)
    exact (world_below k (slabBase G H k base) (flags base) (amounts k base) _ before).trans (keep z hz)

theorem ticks_bound (base : ℕ) (raw : Fin G→Fin H→ℕ) (a : Bits k) :
    (program w base raw a).ticks≤
      (4+Materialized.size G H k*(4+2^k*(2*(1+(2^k-1)*(10*2^k+18))+4))) +
      (4+(G*H)*(keys k).length*(4+2^k*(2*(21+10*k)+4))) :=
  Nat.add_le_add (Materialized.ticks_bound ..) (world_clock ..)

end Hierarchy.DescentColonies.WinningSlabs.Selected
end

end OAI
