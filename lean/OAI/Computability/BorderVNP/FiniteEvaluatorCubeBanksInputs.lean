import OAI.Computability.BorderVNP.FiniteEvaluatorCubeBanksTeams
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeTriple
import OAI.Computability.BorderVNP.FiniteEvaluatorCubePost

/-! # Native cube inputs at the published vertex count

The count in frame word 46 indexes the true owned directory. Its native
word-sized owner numbers give exactly the same order as the finite greedy
owners. Each table lookup uses the three emitted words and the corresponding
routed selector and incident payloads, after the cell stage's actual writes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.FieldRawLayout

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Tally Padding.Banks
open FiniteEvaluator RoutingISA VPVNP.BurstRAM DiagonalTallyPacketEmit
open scoped Classical BigOperators

variable {D R w : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
variable {F : Type*} [Field F] [Fintype F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
variable (V : FieldRawLayout L S) (R : ℕ) (raw : V.Raw R) (t : Fin (R+1))

local notation "axis" => chosen L.bitWidth L.supply (Sigma.fst (Prod.fst raw))
local notation "width" => bankWidth L.dimension L.bitWidth L.copies L.alternatives L.supply
local notation "argument" => argumentWidth L.dimension L.bitWidth L.copies L.alternatives L.supply
local notation "number" => Fin.val ∘ V.owners R (Sigma.fst (Prod.fst raw))

omit [Fintype F] in
/-- The native word comparison against the published numeric team identifier
keeps precisely the same ordered roles as the physical finite owner map. -/
theorem numbered_pairs : CubeVisits.teamList axis L.blocks number t.val = V.teamPairs R raw t := by
  unfold teamPairs CubeVisits.teamList
  apply List.flatMap_congr
  intro q _
  simp only [CubeVisits.teamRow,Function.comp_apply,Fin.val_inj]

omit [Fintype F] in
/-- The native emitted triples at the original word addresses are exactly the
three words of the actual semantic field visits, in their original order. -/
theorem team_triples (packetBase singleBase base : ℕ) (mem : Memory w)
    (emitted : let A := V.bankData R raw packetBase singleBase
      let xs := CubeVisits.teamList A.axis L.blocks number t.val
      ∀ j : Fin xs.length, (CubeTriple.visit A.packetBase width A.select A.demand A.supply (xs.get j)).tripleAt
        (readings mem) (base+3*j.val)) :
    ∀ j : Fin (V.teamPairs R raw t).length, (V.teamVisit R raw packetBase t j).tripleAt (readings mem) (base+3*j.val) := by
  let read := fun (pv : Packet L.dimension L.alphabet L.blocks × Vertex (L.dimension+1)) => V.visit R raw packetBase pv.1 pv.2
  let atRows (xs : List (Packet L.dimension L.alphabet L.blocks × Vertex (L.dimension+1))) :=
    ∀ j : Fin xs.length, (read (xs.get j)).tripleAt (readings mem) (base+3*j.val)
  change atRows (CubeVisits.teamList axis L.blocks number t.val) at emitted
  change atRows (V.teamPairs R raw t)
  exact V.numbered_pairs R raw t ▸ emitted

variable (packetBase : ℕ) (f : Frame) (count : f.count=(V.teamPairs R raw t).length)
variable (table : TableEntry L.dimension L.bitWidth L.copies L.alternatives L.supply → F) (fresh dst : ℕ)

local notation "stop" => CubeConstants.arenaEnd fresh (CubeDeck.entry table)
local notation "ptr" => CubeConstants.idBase fresh L.dimension L.bitWidth L.copies L.alternatives L.supply
local notation "frame" => CubeConstants.inArena f fresh L.dimension L.bitWidth L.copies L.alternatives L.supply

/-- Concrete input of the installed evaluator, using the real published count. -/
noncomputable def cubeInputs : CubePacket.Inputs L.dimension L.bitWidth L.copies L.alternatives L.supply F :=
  CubeDeck.inputs table f fresh (fun i => V.teamVisit R raw packetBase t (Fin.cast count i)) dst D

local notation "Y" => cubeInputs V R raw t packetBase f count table fresh dst

omit [Fintype F] in
/-- The field product computed over the published count equals the product
over actual owned packet/vertex ranks, including an empty directory. -/
theorem cubeInputs_product (fixed : ∀ p, L.table p=table) :
    (∏ i, (Y).scalar i) = ∏ j : Fin (V.teamPairs R raw t).length, V.teamEntry R raw packetBase t j := by
  refine (Fintype.prod_equiv (finCongr count) _ _ fun i => ?_)
  change table ((V.teamVisit R raw packetBase t (Fin.cast count i)).entry D) = L.table _ _
  rw [fixed]
  congr 3

/-- The original shared image physically supplies the lookup, before any cell writes. -/
theorem cubeInputs_original {pub : Arg → Word w} {mem : Memory w} (singleBase : ℕ)
    (actual : CubeDeck.At table f fresh (readings mem)) (loaded : Frame.resident frame (readings pub) (readings mem))
    (emitted : ∀ j : Fin (V.teamPairs R raw t).length,
      (V.teamVisit R raw packetBase t j).tripleAt (readings mem) (f.triples+3*j.val))
    (views : ∀ x, V.owners R raw.1.1 (x.row axis).1=t → (V.bankData R raw packetBase singleBase).Holds mem x)
    (tableWord : (mem ((pub 0).val+47)).val=ptr) (dstWord : (mem ((pub 0).val+71)).val=dst)
    (frameRoom : (pub 0).val+112 ≤ fresh) (tableRoom : stop ≤ f.descriptors)
    (tripleRoom : f.triples+3*f.count ≤ f.descriptors)
    (banksRoom : ∀ j, (V.teamVisit R raw packetBase t j).base+width ≤ f.descriptors)
    (outputs : f.descriptors+2*f.count ≤ f.refs) (separate : f.refs+f.count*argument ≤ dst)
    (room : dst+f.count < 2^w) :
    CubePacket.Prepared Y pub mem := by
  let visits (i : Fin f.count) := V.teamVisit R raw packetBase t (Fin.cast count i)
  exact CubeDeck.prepared table f fresh visits dst D pub mem actual loaded (fun i => emitted (Fin.cast count i))
    (fun i => V.team_banks R raw packetBase singleBase mem t views (Fin.cast count i)) tableWord dstWord
    frameRoom tableRoom tripleRoom (fun i => banksRoom (Fin.cast count i)) outputs separate room

/-- A single allocated deck protects its two literal words, its entire fixed
recipe column and the complete scalar table. The ordered triples and packet
banks occupy their own allocated source regions. -/
theorem cubeInputs_sources (l : TypedTaskBuilder.Layout) (deckRange : l.SourceRange fresh (stop-fresh))
    (tripleRange : l.SourceRange f.triples (3*f.count))
    (bankRange : ∀ j, l.SourceRange (V.teamVisit R raw packetBase t j).base width) : CubePacket.Sources Y l := by
  have ends : stop = fresh+2+(CubeConstants.recipes L.dimension L.bitWidth L.copies L.alternatives L.supply).length +
      2^argument := by simp only [CubeConstants.arenaEnd,CubeConstants.idBase,CubeConstants.ids,List.length_ofFn]
  have countPositive := Nat.two_pow_pos argument
  have piece (a k : ℕ) (lo : fresh ≤ a) (hi : a+k ≤ stop) : l.SourceRange a k := by
    have top := deckRange.end_le
    exact ⟨by omega,by rcases deckRange.calls with left|right <;> omega⟩
  refine ⟨piece fresh 1 le_rfl (by omega),piece (fresh+1) 1 (by omega) (by omega),
    piece (fresh+2) _ (by omega) (by omega),piece ptr _ (by unfold CubeConstants.idBase; omega) ?_,
    tripleRange,fun i => bankRange (Fin.cast count i)⟩
  unfold CubeConstants.idBase
  omega

/-- All lookup inputs are genuinely prepared in the final cell memory. The
source regions account for the common fixed deck, the emitted triples and the
addressable banks of the owned vertices. -/
theorem cubeInputs_prepared {pub : Arg → Word w} {mem : Memory w} {n : ℕ}
    (X : Cells.Inputs F) (cells : Cells.Prepared X pub mem n) (singleBase : ℕ)
    (actual : CubeDeck.At table f fresh (readings mem)) (loaded : Frame.resident frame (readings pub) (readings mem))
    (emitted : ∀ j : Fin (V.teamPairs R raw t).length,
      (V.teamVisit R raw packetBase t j).tripleAt (readings mem) (f.triples+3*j.val))
    (views : ∀ x, V.owners R raw.1.1 (x.row axis).1=t → (V.bankData R raw packetBase singleBase).Holds mem x)
    (tableWord : (mem ((pub 0).val+47)).val=ptr) (dstWord : (mem ((pub 0).val+71)).val=dst)
    (frameRoom : (pub 0).val+112 ≤ fresh) (tableRoom : stop ≤ f.descriptors)
    (tripleRoom : f.triples+3*f.count ≤ f.descriptors)
    (banksRoom : ∀ j, (V.teamVisit R raw packetBase t j).base+width ≤ f.descriptors)
    (outputs : f.descriptors+2*f.count ≤ f.refs) (separate : f.refs+f.count*argument ≤ dst)
    (room : dst+f.count < 2^w)
    (deckRange : X.layout.SourceRange fresh (stop-fresh))
    (tripleRange : X.layout.SourceRange f.triples (3*f.count))
    (bankRange : ∀ j, X.layout.SourceRange (V.teamVisit R raw packetBase t j).base width) :
    CubePacket.Prepared Y pub (X.post mem) := by
  exact (V.cubeInputs_original R raw t packetBase f count table fresh dst singleBase actual loaded emitted
    views tableWord dstWord frameRoom tableRoom tripleRoom banksRoom outputs separate room).post X cells Y
    (V.cubeInputs_sources R raw t packetBase f count table fresh dst X.layout deckRange tripleRange bankRange)

end FiniteDiagonal.FieldRawLayout

end BorderVNP
end Computability
end OAI
