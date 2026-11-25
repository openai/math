import OAI.Computability.BorderVNP.CubeScatterStreams
import OAI.Computability.BorderVNP.CubeScatterDispatch

/-! # Native scatter of an actual selected cube packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open RoutingISA VPVNP.BurstRAM VPVNP.MotifBase DiagonalResidueRAM Tally

variable {n b h K s w : ℕ}

/-- Initialize the packet-bank cursor and the constant needed by both scatter calls. -/
def startPacket : Code := .block [.copy 38 24,.constant 59 1]

/-- The first call copies the complete common selector into its reserved prefix. -/
def copySelectors (n K h : ℕ) : Code :=
  .seq startPacket (program (List.replicate (selectorWidth n K h) .selector))

private theorem selectorModes (u : Selector n K h) :
    (selectorPositions u).map (fun p => p.digit.mode) = List.replicate (selectorWidth n K h) .selector := by
  simp only [selectorPositions,List.map_ofFn,Function.comp_def,Position.digit,Digit.mode,List.ofFn_const]

/-- The reserved selector prefix has one position per selector digit. -/
theorem selectors_advance (u : Selector n K h) (c : Cursor) :
    advance (selectorPositions u) c = ⟨c.selector+selectorWidth n K h,c.crossing,c.dest+selectorWidth n K h⟩ := by
  rw [advance_counts]
  let bs := List.ofFn fun j : Fin (selectorWidth n K h) =>
    VPVNP.RAMSerialization.wordBits _ ⟨(selectorOrder n K h u).val,
      (selectorOrder n K h u).isLt.trans_le (Nat.le_pow_clog (by decide) _)⟩ j
  have eq : selectorPositions u = bs.map Position.selector := by simp [selectorPositions,bs,Function.comp_def]
  have fields (l : List Bool) : (l.map Position.selector).filterMap Position.selectorBit = l ∧
      (l.map Position.selector).filterMap Position.crossBit = [] := by
    induction l with
    | nil => exact ⟨rfl,rfl⟩
    | cons b l ih => simp [List.filterMap_cons,Position.selectorBit,Position.crossBit,ih]
  rw [eq,(fields bs).1,(fields bs).2]
  simp [bs]

/-- Copy the selector from routed source words before the ordinary selector reader decodes its radix index. -/
theorem copySelectors_run (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (src : Set ℕ)
    (u : Selector n K h) (c : Cursor) (r : Bank w) (m : Memory w)
    (sel : r 36 = word w c.selector) (cross : r 37 = word w c.crossing) (base : r 24 = word w c.dest)
    (input : Prepared src (selectorPositions u) c m) :
    ∃ t es, Runs pub mac (copySelectors n K h) r m es t (image (selectorPositions u) c.dest m) ∧
      TraceOK es [] es.length ∧ traceCost es ≤ 4*selectorWidth n K h+3 ∧
      (advance (selectorPositions u) c).loaded t ∧
      ∀ j : Reg, j ∉ ([36,37,38,59,60] : List Reg) → t j = r j := by
  let pre := effect false r m startPacket
  have runs := effect_runs pub mac false r m startPacket (by decide)
  have hm : pre.mem = m := rfl
  have hc : c.loaded pre.bank := by
    simp (config := {decide := true}) [pre,startPacket,Code.block,effect,Cursor.loaded,Function.update,sel,cross,base]
    rfl
  let ps := selectorPositions u
  let ds := ps.map Position.digit
  let tail := result ds pre.bank m
  have rt := program_run pub mac ds pre.bank m
  have modes : ds.map Digit.mode = List.replicate (selectorWidth n K h) .selector := by
    simpa [ds,ps,List.map_map,Function.comp_def] using selectorModes u
  rw [modes] at rt
  obtain ⟨ready,mem,keep⟩ := result_image src ps c pre.bank m hc input
  have trace := result_trace ds pre.bank m
  have empty : ds.flatMap Digit.choices = [] := by simp [ds,ps,selectorPositions,Position.digit,Digit.choices]
  have len : ds.length = selectorWidth n K h := by simp [ds,ps,selectorPositions]
  have head : TraceOK pre.trace [] pre.trace.length := by simp [pre,startPacket,Code.block,effect,TraceOK,tick]
  have cost : traceCost pre.trace = 2 := rfl
  refine ⟨tail.bank,pre.trace++tail.trace,?_,?_,?_,ready,?_⟩
  · exact mem ▸ runs.seq (hm ▸ rt)
  · simpa [tail,empty] using head.append trace.1
  · change VPVNP.RAMBuckets.cost _ _ ≤ _
    rw [VPVNP.RAMBuckets.cost_append]
    change traceCost pre.trace + traceCost tail.trace ≤ _
    dsimp only [tail]
    rw [cost]
    have bound := trace.2
    rw [len] at bound
    omega
  · intro j hj
    simp at hj
    have eq := keep j (by simp [hj])
    exact eq.trans (by simp [pre,startPacket,Code.block,effect,Function.update,hj])

/-- A fixed table of opcode sequences for every finite selector, axis and owned bit. -/
def scatterPacket (n b h K s : ℕ) : Code :=
  dispatch (fun k i owner => program (bodyModes b s ((selectorOrder n K h).symm k) i owner))

/-- Running the actual finite dispatcher, followed by its selected opcode list, realizes
the prescribed owned packet with exactly the local private bits and the indicated word budget. -/
theorem scatterPacket_run (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (src : Set ℕ)
    (u : Selector n K h) (i : Fin (n+1)) (owner : Bool) (r : Bank w) (m : Memory w)
    (c : Cursor) (hc : c.loaded r) (key : r 43 = word w (selectorOrder n K h u).val)
    (place : r 44 = word w (2^i.val)) (side : r 45 = wordBit w owner)
    (fit : max (Fintype.card (Selector n K h)) (2^(n+1)) < 2^w)
    (x : Ends n → Fin (h*b) → Bool) (z : (e : Edge (n+1)) → Fin (payload (onEdge s) u.2 e) → Bool)
    (input : Prepared src (bodyPositions u i owner x z) c m) :
    let ps := bodyPositions u i owner x z
    ∃ t es, Runs pub mac (scatterPacket n b h K s) r m es t (image ps c.dest m) ∧
      TraceOK es ((ps.map Position.digit).flatMap Digit.choices) es.length ∧
      traceCost es ≤ 2*(Fintype.card (Selector n K h)+(n+1))+4*bodyWidth n b h s+4 ∧
      (advance ps c).loaded t ∧ ∀ j : Reg, j ∉ ([36,37,38,58,60] : List Reg) → t j = r j := by
  intro ps
  let u' := Function.update r (58 : Reg) 0
  have reg : c.loaded u' := by simpa (config := {decide := true}) [u',Cursor.loaded,Function.update] using hc
  let ds := ps.map Position.digit
  let tail := result ds u' m
  have rt := program_run pub mac ds u' m
  have modes : ds.map Digit.mode = bodyModes b s u i owner := by
    simpa [ds,ps,List.map_map,Function.comp_def] using bodyModes_eq u i owner x z
  rw [modes] at rt
  obtain ⟨ready,mem,keep⟩ := result_image src ps c u' m reg input
  obtain ⟨trace,cost⟩ := result_trace ds u' m
  let k := selectorOrder n K h u
  let pre := List.replicate (dispatchTicks k i owner) (tick w)
  have head : TraceOK pre [] pre.length := by simp [pre,TraceOK,tick]
  have repCost (j : ℕ) : traceCost (List.replicate j (tick w)) = j := by
    induction j with
    | zero => rfl
    | succ j ih =>
      change 1+traceCost (List.replicate j (tick w)) = j+1
      omega
  have headcost : traceCost pre = dispatchTicks k i owner := repCost _
  have len : ds.length = bodyWidth n b h s := by simp [ds,ps,bodyPositions]
  refine ⟨tail.bank,pre++tail.trace,?_,?_,?_,ready,?_⟩
  · apply (dispatch_iff _ _ _ hc.2.2.2 fit).mpr
    refine ⟨k,i,owner,key,place,side,tail.trace,rfl,?_⟩
    have ht : tail.mem = image ps c.dest m := mem
    rw [← ht]
    simpa only [k,Equiv.symm_apply_apply] using rt
  · simpa [tail] using head.append trace
  · change VPVNP.RAMBuckets.cost _ _ ≤ _
    rw [VPVNP.RAMBuckets.cost_append]
    change traceCost pre + traceCost tail.trace ≤ _
    have h := dispatchTicks_le k i owner
    rw [headcost]
    dsimp only [tail]
    rw [len] at cost
    omega
  · intro j hj
    simp at hj
    simpa [u',Function.update,hj] using keep j (by simp [hj])

end Cube.Scatter

end BorderVNP
end Computability
end OAI
