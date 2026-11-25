import OAI.Computability.BorderVNP.CubeScatterSingleton
import OAI.Computability.BorderVNP.CubeScatterStreams
import OAI.Computability.BorderVNP.RoutingISAOrdinaryCost

/-! # Complete singleton callback and uniqueness of the physical guess trace -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM DiagonalResidueRAM

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- Positions in the actual bank interval, using the current row's group equality. -/
def singlePositions (same : Bool) (bs : List Bool) : List Position :=
  bs.map (if same then Position.localBit else Position.crossing)

/-- A diagonal singleton family consumes no routed crossing bits. An off-diagonal
family consumes its full width, in endpoint-label order. -/
theorem single_advance (same : Bool) (bs : List Bool) (c : Cursor) :
    advance (singlePositions same bs) c =
      ⟨c.selector,c.crossing+(if same then 0 else bs.length),c.dest+bs.length⟩ := by
  rw [advance_counts]
  cases same <;> induction bs with
    | nil => simp [singlePositions]
    | cons x xs ih =>
      simp [singlePositions] at ih
      simp [singlePositions,List.filterMap_cons,Position.selectorBit,Position.crossBit]

/-- Complete singleton execution, including two actual frame reads, destination
arithmetic, the public diagonal test and all guessed or copied bit stores. -/
theorem scatterSingle_run (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (src : Set ℕ) (bs : List Bool)
    (bank alphabet u v sel cross : ℕ) (r : Bank w) (m : Memory w)
    (ru : readings r 24 = u) (rv : readings r 25 = v) (rl : readings r 21 = bs.length)
    (rsel : r 36 = word w sel) (rcross : r 37 = word w cross)
    (alphabetAt : readings m ((pub 0).val+56) = alphabet) (bankAt : readings m ((pub 0).val+88) = bank)
    (frameFit : (pub 0).val+88 < 2^w) (keyFit : u*alphabet+v < 2^w)
    (destFit : singleBase bank alphabet bs.length u v+bs.length < 2^w)
    (input : Prepared src (singlePositions (decide (r 14 = r 15)) bs)
      ⟨sel,cross,singleBase bank alphabet bs.length u v⟩ m) :
    let ps := singlePositions (decide (r 14 = r 15)) bs
    let c : Cursor := ⟨sel,cross,singleBase bank alphabet bs.length u v⟩
    ∃ t es, Runs pub mac scatterSingle r m es t (image ps c.dest m) ∧
      TraceOK es ((ps.map Position.digit).flatMap Digit.choices) es.length ∧
      traceCost es ≤ startSingle.slots+5*bs.length+2 ∧ (advance ps c).loaded t ∧
      ∀ j : Reg, j ∉ ([36,37,38,55,56,57,59,60,62,63] : List Reg) → t j = r j := by
  intro ps c
  obtain ⟨pre,t0,run,cost,h38,h57,h59,keep⟩ :=
    startSingle_run pub mac r m bank alphabet bs.length u v ru rv rl alphabetAt bankAt frameFit keyFit destFit
  let ds := ps.map Position.digit
  let final := result ds t0 m
  let path := walkTrace ds t0 m
  have hc : c.loaded t0 := ⟨(keep 36 (by decide)).trans rsel,(keep 37 (by decide)).trans rcross,h38,h59⟩
  have modes : ds.map Digit.mode =
      List.replicate bs.length (if t0 14 = t0 15 then Mode.privateBit else Mode.crossing) := by
    rw [keep 14 (by decide),keep 15 (by decide)]
    by_cases eq : r 14 = r 15 <;> simp [ds,ps,singlePositions,eq,List.map_map,Function.comp_def,Position.digit,Digit.mode]
  obtain ⟨ready,img,regs⟩ := result_image src ps c t0 m hc input
  have body : Runs pub mac singleBody t0 m (tick w::path) final.bank final.mem :=
    (singleBody_iff bs.length c.dest t0 m h59 h38 h57 destFit).mpr ⟨ds,modes,rfl,rfl,rfl⟩
  have headEvents := run.unsigned_events (by decide)
  have head : TraceOK pre [] pre.length := ⟨rfl,by
    apply List.flatMap_eq_nil_iff.mpr
    exact fun e he => (headEvents e he).1, fun e he => (headEvents e he).2⟩
  obtain ⟨trace,bound⟩ := walk_cost ds t0 m
  have len : ds.length = bs.length := by simp [ds,ps,singlePositions]
  refine ⟨final.bank,pre++(tick w::path),img ▸ run.seq body,?_,?_,ready,?_⟩
  · simpa [path] using head.append trace.cons_tick
  · change VPVNP.RAMBuckets.cost _ _ ≤ _
    rw [VPVNP.RAMBuckets.cost_append]
    change traceCost pre + (1+traceCost path) ≤ _
    change traceCost path ≤ 5*ds.length+1 at bound
    rw [len] at bound
    omega
  · intro j hj
    simp at hj
    exact (regs j (by simp [hj])).trans (keep j (by simp [hj]))

/-- Even for arbitrary returning runs, a fixed sequence of private bits fixes the
registers, memory and all probe events of the entire singleton callback. -/
theorem scatterSingle_unique {r : Bank w} {m : Memory w} {bank alphabet u v len : ℕ}
    (ru : readings r 24 = u) (rv : readings r 25 = v) (rl : readings r 21 = len)
    (alphabetAt : readings m ((pub 0).val+56) = alphabet) (bankAt : readings m ((pub 0).val+88) = bank)
    (frameFit : (pub 0).val+88 < 2^w) (keyFit : u*alphabet+v < 2^w)
    (destFit : singleBase bank alphabet len u v+len < 2^w) {es fs t mt t' mt'}
    (he : Runs pub mac scatterSingle r m es t mt) (hf : Runs pub mac scatterSingle r m fs t' mt')
    (choices : es.flatMap TeamRAM.Event.choices = fs.flatMap TeamRAM.Event.choices) :
    es = fs ∧ t = t' ∧ mt = mt' := by
  obtain ⟨pre,t0,run,_,h38,h57,h59,_⟩ :=
    startSingle_run pub mac r m bank alphabet len u v ru rv rl alphabetAt bankAt frameFit keyFit destFit
  obtain ⟨_,_,_,_,rfl,p₁,b₁⟩ := Runs.seq_iff.mp he
  obtain ⟨rfl,rfl,rfl⟩ := run.unique_of_deterministic (by decide) p₁
  obtain ⟨_,_,_,_,rfl,p₂,b₂⟩ := Runs.seq_iff.mp hf
  obtain ⟨rfl,rfl,rfl⟩ := run.unique_of_deterministic (by decide) p₂
  obtain ⟨xs,hxs,rfl,rfl,rfl⟩ := (singleBody_iff len _ _ _ h59 h38 h57 destFit).mp b₁
  obtain ⟨ys,hys,rfl,rfl,rfl⟩ := (singleBody_iff len _ _ _ h59 h38 h57 destFit).mp b₂
  have a := (walk_cost xs t0 m).1.2.1
  have b := (walk_cost ys t0 m).1.2.1
  simp only [List.flatMap_append,List.flatMap_cons,List.append_cancel_left_eq] at choices
  have eq := choices_injective (hxs.trans hys.symm) (a.symm.trans (choices.trans b))
  subst ys
  exact ⟨rfl,rfl,rfl⟩

end Cube.Scatter

end BorderVNP
end Computability
end OAI
