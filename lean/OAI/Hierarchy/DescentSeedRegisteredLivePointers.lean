import OAI.Hierarchy.DescentSeedRegisteredOperandRows
import OAI.Hierarchy.DescentSeedSignedPlane

namespace OAI
/-! # The four initial pointer digits at each actual original operand in startup memory -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler Catalyst DescentInitialHost DescentPackedSeed DescentDatedSeedStartup
open DescentKernelHistory Computability.BorderVNP.Crossing
open DescentSeedRoot DescentSeedInitialTable DescentColonies DescentDyadicSpan DescentRotor
open DescentDatedSeedStartup.Input DescentDatedPriorOperand DescentOperandStateBanks
open DescentPackedColony DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {S : AtomSchedule} (G : PoweredGadget F) (op : RotorSpec)
    {k cp p H : ℕ} (X : Approximation F cp p)
    (digits : Fin S.copies≃Fin (S.groupCount 0)×Block k)
    (publicWide : Fintype.card (Vertex X)≤H) (l : DescentDatedSeedStartup.Layout) (header payload Z : ℕ)
local notation "g₀" => S.groupCount 0
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "top" => DescentDatedSeedStartup.endAddress X l H g₀ k
local notation "chart" => nodeChart l k H g₀
local notation "Q" => nodeArities X publicWide l
local notation "finish" => (chart).seedEnd top
local notation "lanes" => DescentDatedSeedStartup.Primitive.paletteLanes G op l.seedWidth Z payload k
local notation "limit" => DescentDatedSeedStartup.Primitive.initialEnd X S.copies l.seedWidth payload k H g₀ lanes finish
local notation "jobs" => DescentPackedSeed.Primitive.Source.jobs X S.copies l.seedWidth payload
local notation "ports" => initial G op X S.copies l k H g₀ payload Z
local notation "final" => completeImage G op X digits publicWide l header payload Z
local notation "ob" => operandBase X l H g₀
local notation "db" => directoryBase X l H g₀ k
local notation "argBase" => Seed.Physical.bankStart X ob k g₀ l.operandLanes
local notation "L" => (ports).rangeLayout

theorem seed_single_digit (b term : ℕ) (n : Fin 1) (fit : term<2^b) :
    (((encode b 1).symm (term:Cell (b*1))) n).val=term :=by
  have head:=digit_encode ((encode b 1).symm (term:Cell (b*1))) n
  rw [Equiv.apply_symm_apply] at head
  have zero : n.val=0:=by omega
  simpa [digit,zero,Nat.mod_eq_of_lt fit] using head.symm

private theorem initial_header_lt {R b : ℕ} (room : 3<2^b) (copies : R≤2^b)
    (v : Vertex X) (e : LocalBoundary X v) (copy : Fin R) (chunk : ℕ) (short : chunk<2^b) (f : Fin 4) :
    (Seed.originalAt X v e copy.val chunk).header f<2^b :=by
  rcases e with edge | pin
  · have peer : Signed.seedPeer X v edge.val < 3 := Signed.Plane.peer_short X v edge.val edge.property
    have serial : Signed.seedParallel X v edge.val ≤ 3 := Signed.parallel_short X v edge.val
    fin_cases f
    · exact (by decide : 1 < 3).trans room
    · exact peer.trans room
    · exact serial.trans_lt room
    · exact short
  · fin_cases f
    · exact (by decide : 2 < 3).trans room
    · exact (by decide : 0 < 3).trans room
    · exact copy.isLt.trans_le copies
    · exact short

theorem seed_pointer_digit {s : ℕ} (c : (initialGroup X S.copies s).Choice)
    (room : 3<2^l.operandBits) (copies : S.copies≤2^l.operandBits)
    (quota : l.groupsPerNode≤2^l.operandBits) (j : Fin S.copies) (v : Vertex X)
    (u : (initialRecipe X S.copies s c ⟨j,v⟩).Node) (arg : Fin ((initialRecipe X S.copies s c ⟨j,v⟩).arity u))
    (chunk : Fin l.groupsPerNode) (f : Fin 4) :
    let i:=Fin.castLE (DescentBundleHistory.initial_arity X S.copies s c ⟨j,v⟩ u) arg
    let slot:=finProdFinEquiv (i,chunk)
    let face:=f.castLE (by decide : 4≤7)
    let ptr:=Seed.originalAt X v (leg X v (Fin.cast (recipe_arity X c j v u) arg)) j.val chunk.val
    let cells:=Seed.Physical.value X hs (Equiv.refl _) digits l.groupsPerNode l.operandBits 1 slot.val face (digits j).2
    ∀n : Fin 1,(((encode l.operandBits 1).symm (cells (hs v) (digits j).1)) n).val=ptr.header f :=by
  intro i slot face ptr cells n
  have at_:=Seed.Physical.value_live X hs (Equiv.refl _) digits l.groupsPerNode 1 l.operandBits
    (by decide) (3*l.groupsPerNode) (digits j).2 v i chunk (digits j).1 face
  have copy : digits.symm ((Equiv.refl _).symm (digits j).1,(digits j).2)=j:=digits.symm_apply_apply j
  have liveLeg : i.val < legArity X v := (recipe_arity X c j v u) ▸ arg.isLt
  have scalar : Seed.Columns.scalar X v i chunk.val j.val face = ptr.fields ⟨0,1,1⟩ face := by
    simp only [Seed.Columns.scalar, Seed.Columns.leg?, dite_eq_left liveLeg, Option.elim_some]; rfl
  rw [copy,scalar] at at_
  have code : ptr.fields ⟨0,1,1⟩ face=ptr.header f:=by
    simp [Pointer.fields,face,f.isLt]
  change cells (hs v) (digits j).1=(ptr.fields ⟨0,1,1⟩ face : Cell (l.operandBits*1)) at at_
  rw [code] at at_
  change _=ptr.header f
  rw [at_]
  apply seed_single_digit l.operandBits (ptr.header f) n
  exact initial_header_lt X room copies v _ j chunk.val (chunk.isLt.trans_le quota) f

theorem seed_live_pointer {s w : ℕ} (c : (initialGroup X S.copies s).Choice)
    (m : Memory w) (fields : l.operandBits*l.operandLanes≤w) (early : header<l.base)
    (sourceSpace : publicWords X+DescentDyadicSpan.span jobs≤finish) (live : 0<lanes) (machine : payload≤w)
    (space : limit<2^w) (room : 3<2^l.operandBits) (copies : S.copies≤2^l.operandBits)
    (quota : l.groupsPerNode≤2^l.operandBits) (j : Fin S.copies) (v : Vertex X)
    (u : (initialRecipe X S.copies s c ⟨j,v⟩).Node) (arg : Fin ((initialRecipe X S.copies s c ⟨j,v⟩).arity u))
    (chunk : Fin l.groupsPerNode) (f : Fin 4) :
    let i:=Fin.castLE (DescentBundleHistory.initial_arity X S.copies s c ⟨j,v⟩ u) arg
    let slot:=finProdFinEquiv (i,chunk)
    let face:=f.castLE (by decide : 4≤7)
    let ptr:=Seed.originalAt X v (leg X v (Fin.cast (recipe_arity X c j v u) arg)) j.val chunk.val
    ∃cells : Fin H→Fin g₀→Cell (l.operandBits*1),
      Reads (previousBank L (ports).archive.arguments (digits j).2 (page face slot)) cells l.operandLanes ((final) m) ∧
      ∀n:Fin 1,(((encode l.operandBits 1).symm (cells (hs v) (digits j).1)) n).val=ptr.header f :=by
  intro i slot face ptr
  let cells:=Seed.Physical.value X hs (Equiv.refl _) digits l.groupsPerNode l.operandBits 1 slot.val face (digits j).2
  refine ⟨cells,seed_operand_cells G op X digits publicWide l header payload Z m fields early sourceSpace live machine space
    face slot (digits j).2,?_⟩
  exact seed_pointer_digit X digits publicWide l c room copies quota j v u arg chunk f

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
