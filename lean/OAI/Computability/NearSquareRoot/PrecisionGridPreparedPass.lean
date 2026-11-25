import OAI.Computability.NearSquareRoot.PrecisionGridBlockPass
import OAI.Computability.NearSquareRoot.PrecisionPreparedPacket

/-! # The synchronized phase layer from an ordinary setup header

The preparation program enumerates and rounds each small local block table.
The array pass reads the resulting raw nested records and applies their tensor
in physical order. A single additional polynomial in the descriptor scale
covers preparing the local entries, including all required copies.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace FixedPoint

open IntegerMultiplication Code Strip Staff PhaseStream PhaseTable BoxFin SynchronizedBlocks ShortFourier

private def lookupDefault {β : Type*} {d : ℕ} {r : Fin d → ℕ} (v : (j : Fin d) → Fin (r j) → β)
    (z : β) (p : ℕ × ℕ) : β :=
  if h : p.1 < d then
    if g : p.2 < r ⟨p.1,h⟩ then v ⟨p.1,h⟩ ⟨p.2,g⟩ else z
  else z

@[simp] private theorem lookupDefault_on {β : Type*} {d : ℕ} {r : Fin d → ℕ}
    (v : (j : Fin d) → Fin (r j) → β) (z : β) (j : Fin d) (t : Fin (r j)) :
    lookupDefault v z (j.val,t.val) = v j t := by
  simp [lookupDefault,j.isLt,t.isLt]

private def labels {d : ℕ} (r : Fin d → ℕ) (j : Fin d) (t : Fin (r j)) : ℕ × ℕ := (j.val,t.val)

private theorem mappedLabelRows {β : Type*} {d : ℕ} {r : Fin d → ℕ}
    (v : (j : Fin d) → Fin (r j) → β) (z : β) :
    (List.range d).map (fun t => (radixTable (labels r) t).map (lookupDefault v z)) = radixRows v := by
  rw [show (fun t => (radixTable (labels r) t).map (lookupDefault v z)) =
    (List.map (lookupDefault v z)) ∘ radixTable (labels r) from rfl,
    ← List.map_map,radixTable_range]
  simp [radixRows,List.map_reverse,List.map_ofFn,Function.comp_def,labels]

/-- Local phase indexed by its padded block rank. The effective local
spectator/axis lookup only needs to realize this finite table. -/
def phaseAtBlockRank {k l : ℕ} {b : List (ℕ × ℕ)} (hb : BoxShape.Valid k l b)
    (phase : ∀ j, BlockAddress (BoxAxis b) j → ℂ) (j : Fin (b.length/4)) (t : Fin (blockRadix b j)) : ℂ :=
  letI := modulus_neZero hb
  phase j ((blockAddressRank hb j).symm t)

/-- The adapter, prefix sweep, and multiplication are one bounded program
on the raw numerical tables. On entry the array is parked next to the raw
table payload. On return it contains the specified block-diagonal result. -/
theorem rawSynchronizedPhasePass {I : Type} (k l : I → ℕ) (b : I → List (ℕ × ℕ))
    (hb : ∀ i, BoxShape.Valid (k i) (l i) (b i)) (hd : ∀ i, 4 ≤ (b i).length)
    (phase : ∀ i j, BlockAddress (BoxAxis (b i)) j → ℂ) (unit : ∀ i j a, ‖phase i j a‖ = 1)
    (v : ∀ i j, Fin (blockRadix (b i) j) → Record (guardedK (k i)))
    (err : ∀ i j t, ‖value _ (v i j t) - phaseAtBlockRank (hb i) (phase i) j t‖ ≤
      1/(2:ℝ)^(70*guardedK (k i)))
    (x : (i : I) → Fin (2^k i) → Record (k i)) (hk : ∀ i, 1 ≤ k i)
    (hx : ∀ i, ‖recordArray (x i)‖ ≤ (2 : ℝ)^(13*k i)) :
    ∃ (out : (i : I) → Fin (2^k i) → Record (k i))
      (hu : ∀ i z, ‖blockCoefficient (hb i) (hd i) (phase i) z‖ = 1),
      Space.BoundedTask (fun i => (2^k i+1)*GridTask.recordCost (k i))
        (fun i => (2^k i+1)*(k i+1))
        (fun i => .fork (send (List.ofFn fun z => Dusk.mark (x i z)))
          (phaseTablePacket (guardedK (k i)) (radixRows (v i))))
        (fun i => send (List.ofFn fun z => Dusk.mark (out i z))) ∧
      ∀ i, ‖recordArray (out i) -
        phaseLayerIsometry (blockCoefficient (hb i) (hd i) (phase i)) (hu i) (recordArray (x i))‖ ≤
          1 / (2 : ℝ)^(50*k i) := by
  let d i := (b i).length/4
  let keys i := labels (blockRadix (b i))
  let store i := lookupDefault (v i) (digitRecord _ 1)
  let ideal i := lookupDefault (phaseAtBlockRank (hb i) (phase i)) 1
  let data i := send (List.ofFn fun z => Dusk.mark (x i z))
  have localMatch (i) : blockLabelsMatch (hb i) (keys i) (ideal i) (phase i) := by
    intro j a
    simp [ideal,keys,labels,phaseAtBlockRank]
  obtain ⟨out,hu,applyTable,accurate⟩ := synchronizedPhasePass k l b hb hd keys ideal phase localMatch store
    (fun i j t => by simp [ideal,keys,labels,phaseAtBlockRank,unit])
    (fun i j t => by simpa [ideal,keys,labels,store] using err i j t) x hk hx
  let row i t := (radixTable (keys i) t).map (store i)
  have rows (i) : (List.range (d i)).map (row i) = radixRows (v i) := mappedLabelRows ..
  have count (i) : ((List.range (d i)).map (fun t => (row i t).length)).prod = 2^k i := by
    simp only [row,List.length_map]
    exact (radixTable_count _).trans (prod_blockRadix (hb i) (hd i))
  have prep := phaseTableInput_indexed k d row (fun i j hj => by
    obtain ⟨a,e⟩ := radixTable_row (keys i) hj
    simpa [row,e] using (blockRadix_bounds (hb i) a).1)
  simp_rw [rows] at prep
  have physical := (prep.right data).compose applyTable
  refine ⟨out,hu,physical.bound 1000 1000 ?_ ?_,accurate⟩
  · intro i
    have hw := ProductPass.streamSize (fun j => Dusk.mark (x i j)) (fun j => (record_size _ _).le)
    change (data i).count ≤ _ at hw
    have hh := Nat.mul_le_mul_left (2^k i) (GridTask.width_le_recordCost (k i))
    change (data i).count + _ + _ + 1 ≤ _
    rw [count i]
    nlinarith only [hw,hh,GridTask.width_le_recordCost (k i),Nat.zero_le (GridTask.recordCost (k i)),Nat.zero_le (2^k i)]
  · intro i
    have hw := ProductPass.streamSize (fun j => Dusk.mark (x i j)) (fun j => (record_size _ _).le)
    change (data i).count ≤ _ at hw
    simp only [count]
    apply Nat.succ_le_of_lt
    rw [max_lt_iff]
    constructor <;> nlinarith only [hw,Nat.zero_le (k i),Nat.zero_le (2^k i)]

/-- Prepare a small payload, preserve the original header, and run one array
pass. The setup clock is a polynomial in the descriptor scale and accounts
for transferring the payload and the header between the finite registers. -/
theorem passPreparedHeader {I : Type} {s : Regime I} {time space : I → ℕ}
    {packet data output : I → Tree} (ready : s.Small packet)
    (consume : Space.BoundedTask time space (fun i => .fork (data i) (packet i)) output) :
    ∃ setup : I → ℕ, Dom s.scale setup ∧
      Space.BoundedTask (fun i => setup i + (data i).count + time i)
        (fun i => setup i + (data i).count + space i)
        (fun i => .fork (s.header i) (data i)) (fun i => .fork (s.header i) (output i)) := by
  have volume := ready.extent
  obtain ⟨t,bound,build⟩ := ready
  let query i := Tree.fork (s.header i) (data i)
  let setup i := (s.header i).count + (packet i).count + t i
  have copied := Space.BoundedTask.of_time (Task.copy query)
  have keep := (Space.BoundedTask.of_time (Task.dropRight s.header data)).left query
  have compute := (Space.BoundedTask.of_time build).left data
  have switch := Space.BoundedTask.swap packet data
  have process := ((compute.compose switch).compose consume).right s.header
  have run := (copied.compose keep).compose process
  refine ⟨setup,(s.gauge.add volume).add bound,run.bound 50 50 ?_ ?_⟩
  · intro i
    dsimp [query,setup,Tree.count]
    omega
  · intro i
    dsimp [query,setup,Tree.count]
    omega

/-- A single fixed framed program prepares the block tables from its actual
descriptor, applies the synchronized tensor phase, and preserves the
descriptor for the subsequent array passes. -/
theorem preparedSynchronizedPhasePass {I : Type} (s : Regime I) (k l : I → ℕ)
    (b : I → List (ℕ × ℕ)) (hb : ∀ i, BoxShape.Valid (k i) (l i) (b i)) (hd : ∀ i, 4 ≤ (b i).length)
    (phase : ∀ i j, BlockAddress (BoxAxis (b i)) j → ℂ) (unit : ∀ i j a, ‖phase i j a‖ = 1)
    (K : Realizes s k) (D : Realizes s (fun i => (b i).length/4))
    (N : Realizes (signal _ D) (fun i : Across (fun t => (b t).length/4) => blockRadix (b i.1) i.2))
    (prepared : Prepared (signal _ N) (fun t => 70 * guardedK (k t.1.1) + 3)
      (fun t => phaseAtBlockRank (hb t.1.1) (phase t.1.1) t.1.2 t.2))
    (x : (i : I) → Fin (2^k i) → Record (k i)) (hk : ∀ i, 1 ≤ k i)
    (hx : ∀ i, ‖recordArray (x i)‖ ≤ (2 : ℝ)^(13*k i)) :
    ∃ (setup : I → ℕ) (out : (i : I) → Fin (2^k i) → Record (k i))
      (hu : ∀ i z, ‖blockCoefficient (hb i) (hd i) (phase i) z‖ = 1),
      Dom s.scale setup ∧
      Space.BoundedTask (fun i => setup i + (2^k i+1)*GridTask.recordCost (k i))
        (fun i => setup i + (2^k i+1)*(k i+1))
        (fun i => .fork (s.header i) (send (List.ofFn fun z => Dusk.mark (x i z))))
        (fun i => .fork (s.header i) (send (List.ofFn fun z => Dusk.mark (out i z)))) ∧
      ∀ i, ‖recordArray (out i) -
        phaseLayerIsometry (blockCoefficient (hb i) (hd i) (phase i)) (hu i) (recordArray (x i))‖ ≤
          1 / (2 : ℝ)^(50*k i) := by
  obtain ⟨v,build,err⟩ := prepareGuardedPacket D K _ N
    (fun i t => phaseAtBlockRank (hb i.1) (phase i.1) i.2 t) (fun i t => unit i.1 i.2 _) prepared
  obtain ⟨out,hu,pass,accurate⟩ := rawSynchronizedPhasePass k l b hb hd phase unit v err x hk hx
  obtain ⟨setup,clock,complete⟩ := passPreparedHeader build pass
  refine ⟨setup,out,hu,clock,complete.bound 500 500 ?_ ?_,accurate⟩
  · intro i
    have hw := ProductPass.streamSize (fun j => Dusk.mark (x i j)) (fun j => (record_size _ _).le)
    have hwc := GridTask.width_le_recordCost (k i)
    have hm := Nat.mul_le_mul_left (2^k i) hwc
    change size (List.ofFn _) ≤ _ at hw
    change setup i + size (List.ofFn _) + _ + 1 ≤ _
    nlinarith only [hw,hwc,hm,Nat.zero_le (setup i),Nat.zero_le (2^k i)]
  · intro i
    have hw := ProductPass.streamSize (fun j => Dusk.mark (x i j)) (fun j => (record_size _ _).le)
    change size (List.ofFn _) ≤ _ at hw
    change setup i + size (List.ofFn _) + _ + 1 ≤ _
    nlinarith only [hw,Nat.zero_le (setup i),Nat.zero_le (2^k i),Nat.zero_le (k i)]

end FixedPoint

end

end NearSquareRoot
end Computability
end OAI
