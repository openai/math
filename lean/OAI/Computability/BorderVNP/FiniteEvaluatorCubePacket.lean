import OAI.Computability.BorderVNP.FiniteEvaluatorCubeWord
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeScan
import OAI.Computability.BorderVNP.DiagonalTallyPacketResult

/-! # Native cube table lookup and field multiplication

The real packet reference emitter and gather inspect the assigned incident
bits. The common finite deck contains a one-word encoding of each field value,
so a second pass consumes exactly the selected words with one private call
per owned vertex, retaining a successful zero-valued entry.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubePacket

open VPVNP.BurstRAM RoutingISA TeamRAM TeamContraction FieldProcessor
open DiagonalTallyPacketEmit BorderVNP.Cube BorderVNP.Cube.Tally FiniteScalarLibrary
open scoped BigOperators Classical
open private noBursts from OAI.Computability.BorderVNP.RoutingISAFiniteScalarBatch

variable {n b h K s w m : ℕ} {Q : Type} {F : Type*} [Field F] [Fintype F]

/-- The fixed packet table lookup followed immediately by the actual scalar calls. -/
def code : Code := .seq producePacketIDs CubeScan.code

/-- Physical source of the selected cube entries owned by one team. -/
structure Inputs (n b h K s : ℕ) (F : Type*) where
  /-- Header addresses and owned vertex count. -/
  frame : DiagonalTallyPacketEmit.Frame
  /-- Native visit triples with their actual selectors, vertices and attached bit inputs. -/
  visits : Fin frame.count → Visit n b h K s
  /-- The fixed finite scalar of each cube table row. -/
  entry : TableEntry n b h K s → F
  /-- Start of the scalar table words in shared memory. -/
  table : ℕ
  /-- Start of the owned selected-word column. -/
  dst : ℕ
  /-- Antipodal demand offset. -/
  demand : ℕ

variable (X : Inputs n b h K s F)

/-- Actual frame, incident bits, recipes and fixed lookup words before the native
selection scan. Each entry maps to its own ordinary natural word. -/
structure WordPrepared (id : TableEntry n b h K s → ℕ) (pub : Arg → Word w) (mem : Memory w) : Prop where
  frame : X.frame.resident (readings pub) (readings mem)
  fits : X.frame.Fits (readings mem) w (pub 0).val
  recipe : X.frame.recipeAt (readings mem) n b h K s
  triples : ∀ i, (X.visits i).tripleAt (readings mem) (X.frame.triples+3*i.val)
  banks : ∀ i, VertexAt mem (X.visits i).base (X.visits i).selector (X.visits i).vertex (X.visits i).ends (X.visits i).supply
  zero : (mem X.frame.zeroAddr).val=0
  one : (mem X.frame.oneAddr).val=1
  below : ∀ i, ∀ r ∈ Cube.Tally.recipe (X.visits i).selector (X.visits i).vertex b s,
    r.address (X.visits i).base X.frame.zeroAddr X.frame.oneAddr<X.frame.descriptors
  tableWord : (mem ((pub 0).val+47)).val=X.table
  dstWord : (mem ((pub 0).val+71)).val=X.dst
  deck : ∀ k < 2^argumentWidth n b h K s, (mem (X.table+k)).val =
    idTable (selectorOrder n K h) (vertexOrder _) id k
  tableFit : X.table+2^argumentWidth n b h K s ≤ X.frame.descriptors
  separate : X.frame.refs+X.frame.count*X.frame.width ≤ X.dst
  room : X.dst+X.frame.count < 2^w

/-- The finite scalar program consumes the one-hot framing of each selected field value. -/
abbrev Prepared (pub : Arg → Word w) (mem : Memory w) :=
  WordPrepared X (fun e => CubeWord.encode (X.entry e)) pub mem

/-- Total actual work of the reference generation, lookup and scalar scan. -/
def Inputs.cost :=
  DiagonalTallyPacketEmit.setup.slots+DiagonalTallyPacket.setup.slots+4+
    X.frame.count*(2*(descStep.slots+1)+11)+(X.frame.count*X.frame.width)*(refStep.slots+1+8) +
    (CubeScan.setup.slots+5*X.frame.count+1)

/-- Native value of one visit read from its real selector and vertex arguments. -/
def Inputs.scalar (i : Fin X.frame.count) : F := X.entry ((X.visits i).entry X.demand)

/-- One genuine chronological native return on the true lookup deck, with the
exact field product of the assigned vertex entries. It consumes no private
choices, makes only one-word private calls, and is the only successful trace. -/
theorem run (pub : Arg → Word w) (lib : Fin 8 → TeamSite.Macro Q (Option Bool) m AlphabetWidth)
    (old : Returns Q (Option Bool) F m 8) (fuel : ℕ) (bank : Bank w) (mem : Memory w)
    (prepared : Prepared X pub mem) (wide : 2*Fintype.card F<w) (clock : 2*Fintype.card F<fuel) :
    let mac := TeamSiteEvents.macros (combine F lib) fuel
    ∃ es z mz, Runs pub mac code bank mem es z mz ∧ Within X.cost 1 0 es ∧
      weight pub (combine F lib) (returns F lib old) fuel code bank es = ∏ i, X.scalar i ∧
      (∀ a < X.frame.descriptors, mz a = mem a) ∧
      ∀ fs t mt, Runs pub mac code bank mem fs t mt → fs=es ∧ t=z ∧ mt=mz := by
  intro mac
  obtain ⟨pre,t,mt,look,cost,atWord,keep,ordinary⟩ := producePacketIDs_runs pub mac bank mem X.frame X.visits
    (fun e => CubeWord.encode (X.entry e)) X.table X.dst X.demand prepared.frame prepared.fits prepared.recipe prepared.triples
    prepared.banks prepared.zero prepared.one prepared.below prepared.tableWord prepared.dstWord prepared.deck prepared.tableFit prepared.separate prepared.room
  have bounds := prepared.fits.frameBefore
  have finish := prepared.fits.room
  have outputs := prepared.fits.outputs
  have froom : (pub 0).val+71<2^w := by omega
  have num : (mt ((pub 0).val+46)).val = X.frame.count := (congrArg Fin.val (keep _ (by omega))).trans prepared.frame.1
  have ptr : (mt ((pub 0).val+71)).val = X.dst := (congrArg Fin.val (keep _ (by omega))).trans prepared.dstWord
  have read (i : Fin X.frame.count) := CubeWord.returned lib old (X.scalar i) (mt (X.dst+i.val))
    (CubeScan.event mt (X.dst+i.val)) wide (atWord i) rfl fuel clock
  obtain ⟨post,z,scan,scost,events,clean,unique⟩ := CubeScan.run pub mac t mt froom num ptr prepared.room.le
    (fun i hi => (read ⟨i,hi⟩).1)
  have fields : weight pub (combine F lib) (returns F lib old) fuel CubeScan.code t post = ∏ i, X.scalar i := by
    rw [positive_weight 1 pub _ _ fuel scan (by decide) (fun e he => (clean e he).2)]
    have flags : (burst (w := w)) = FiniteScalarBatch.isBurst := by
      funext e; rcases e with ⟨a,bs,ys,sg⟩; cases a <;> rfl
    rw [flags]
    change ((FiniteScalarBatch.bursts post).map _).prod = _
    rw [events,List.map_map]
    let out (i : ℕ) := (FieldProcessor.returned (combine F lib 1) (returns F lib old 1) fuel (CubeScan.event mt (X.dst+i))).getD 0
    have col : (List.range X.frame.count).map out = List.ofFn X.scalar := by
      apply List.ext_getElem
      · simp
      · intro i hi hj
        have bi : i < X.frame.count := by simpa using hi
        simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
        have v := (read ⟨i,bi⟩).2
        change FieldProcessor.returned _ _ _ _ = some (X.scalar ⟨i,bi⟩) at v
        simp [out,v]
    change ((List.range X.frame.count).map out).prod = _
    rw [col,List.prod_ofFn]
  have neutral : weight pub (combine F lib) (returns F lib old) fuel producePacketIDs bank pre = 1 := by
    rw [positive_weight 1 pub _ _ fuel look (by decide) (fun e he => (ordinary e he).2.1)]
    have empty := noBursts look (by decide)
    have flags : (burst (w := w)) = FiniteScalarBatch.isBurst := by
      funext e; rcases e with ⟨a,bs,ys,sg⟩; cases a <;> rfl
    rw [flags]
    change ((FiniteScalarBatch.bursts pre).map _).prod = _
    rw [empty]; rfl
  refine ⟨pre++post,z,mt,look.seq scan,⟨?_,?_,?_⟩,?_,keep,?_⟩
  · exact (VPVNP.RAMBuckets.cost_append ..).trans_le (Nat.add_le_add cost scost)
  · intro e he
    exact (List.mem_append.mp he).elim (fun h => (ordinary e h).2.2 ▸ Nat.zero_le 1) (CubeScan.burst_bound events e)
  · intro e he
    rcases List.mem_append.mp he with h | h
    · rw [(ordinary e h).1]; rfl
    · rw [(clean e h).1]; rfl
  · rw [code,weight_seq pub _ _ fuel look scan,neutral,one_mul,fields]
  · intro fs u mu other
    obtain ⟨v,mv,gs,ss,rfl,first,last⟩ := Runs.seq_iff.mp other
    obtain ⟨rfl,rfl,rfl⟩ := look.unique_of_deterministic (by decide : producePacketIDs.deterministic=true) first
    obtain ⟨rfl,rfl,rfl⟩ := unique ss u mu last
    exact ⟨rfl,rfl,rfl⟩

end FiniteEvaluator.CubePacket

end BorderVNP
end Computability
end OAI
