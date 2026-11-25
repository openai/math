import OAI.Computability.BorderVNP.CubeLabelISANodes
import OAI.Computability.BorderVNP.CubeLabelISAEdge
import OAI.Computability.BorderVNP.RoutingISAOrdinaryCost

/-! # Scanning only the cables incident at the cell being assigned

Registers 26 and 27 sum the conditional numerators before and after one label trial.
The pointer guard stops on the actual zero link in memory. No counter ranges over all
the cables in the grid.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LabelTrial

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Current cell, candidate, ordered bin and two directory bases. -/
structure Query where
  /-- Alphabet size. -/
  Z : ℕ
  /-- Cell being assigned. -/
  cell : ℕ
  /-- Candidate label. -/
  cand : ℕ
  /-- Source bin. -/
  src : ℕ
  /-- Destination bin. -/
  dst : ℕ
  /-- Labels array address. -/
  labels : ℕ
  /-- Incidence-node array address. -/
  nodes : ℕ

/-- The physical parameters that are common to every cable in a bin. -/
def Query.loaded (q : Query) (z : NatState) := z.reg 0 = q.Z ∧ z.reg 1 = q.cell ∧
  z.reg 2 = q.cand ∧ z.reg 3 = q.src ∧ z.reg 4 = q.dst ∧ z.reg 20 = 1 ∧
  z.reg 21 = q.labels ∧ z.reg 23 = 0 ∧ z.reg 29 = q.nodes ∧ z.reg 30 = 4

/-- The two incident contributions read from the label of the opposite endpoint. -/
def Query.weights (q : Query) (m : ℕ → ℕ) (e : Incident) : ℕ × ℕ :=
  let otherBin := if e.dir = 0 then q.dst else q.src
  let ownBin := if e.dir = 0 then q.src else q.dst
  let old := edgeBefore q.Z q.cell e.other (m (q.labels+e.other)) otherBin e.width
  (old, edgeAfter q.Z q.cand ownBin old)

/-- Bounds for each visited row address and its indirectly read label. -/
def Query.room (q : Query) (w : ℕ) (m : ℕ → ℕ) : ℕ → List Incident → Prop
  | _, [] => True
  | ptr, e :: es => nodeAddr q.nodes ptr + 3 < 2^w ∧ q.labels+e.other < 2^w ∧
      e.width * q.Z^2 < 2^w ∧ q.room w m (m (nodeAddr q.nodes ptr)) es

/-- The two sums of all rows in this incident list. -/
def Query.sums (q : Query) (m : ℕ → ℕ) (es : List Incident) : ℕ × ℕ :=
  ((es.map (fun e => (q.weights m e).1)).sum, (es.map (fun e => (q.weights m e).2)).sum)

/-- Add both contributions returned by the single-row kernel. -/
def addWeights : Code := .seq (.binary .add 26 26 9) (.binary .add 27 27 10)

/-- Read, evaluate, and add one actual incidence node. -/
def scanStep : Code := .seq readNode (.seq edgeContrib addWeights)

/-- Follow physical successor links to the first null pointer. -/
def scan : Code := .whileLt 23 24 scanStep

private theorem stable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} {s m tr t mt} (r : Runs pub macros c s m tr t mt) (q : Query)
    (h : q.loaded (.ofWords s m))
    (keep : ∀ k ∈ ([0,1,2,3,4,20,21,23,29,30] : List Reg), c.keeps k = true) :
    q.loaded (.ofWords t mt) := by
  rcases h with ⟨h₀,h₁,h₂,h₃,h₄,h₂₀,h₂₁,h₂₃,h₂₉,h₃₀⟩
  unfold Query.loaded NatState.ofWords readings at *
  simp only [r.keepsReg (keep 0 (by decide)),r.keepsReg (keep 1 (by decide)),
    r.keepsReg (keep 2 (by decide)),r.keepsReg (keep 3 (by decide)),
    r.keepsReg (keep 4 (by decide)),r.keepsReg (keep 20 (by decide)),r.keepsReg (keep 21 (by decide)),
    r.keepsReg (keep 23 (by decide)),r.keepsReg (keep 29 (by decide)),r.keepsReg (keep 30 (by decide))]
  exact ⟨h₀,h₁,h₂,h₃,h₄,h₂₀,h₂₁,h₂₃,h₂₉,h₃₀⟩

private theorem cost_append {w : ℕ} (a b : List (TeamRAM.Event w)) :
    traceCost (a++b) = traceCost a + traceCost b := VPVNP.RAMBuckets.cost_append ..

private theorem same_memory {w : ℕ} {a b : Memory w} (h : readings a = readings b) : a = b := by
  funext k; exact Fin.ext (congrFun h k)

private theorem row_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (q : Query) (hz : 0 < q.Z) (s : Bank w) (m : Memory w) (h : q.loaded (.ofWords s m))
    (e : Incident) (ptr : ℕ) (hp : (s 24).val = ptr) (live : 0 < ptr)
    (dir : readings m (nodeAddr q.nodes ptr+1) = e.dir)
    (other : readings m (nodeAddr q.nodes ptr+2) = e.other)
    (width : readings m (nodeAddr q.nodes ptr+3) = e.width)
    (room : nodeAddr q.nodes ptr + 3 < 2^w) (lab : q.labels+e.other < 2^w)
    (mass : e.width*q.Z^2 < 2^w)
    (lo : (s 26).val + (q.weights (readings m) e).1 < 2^w)
    (hi : (s 27).val + (q.weights (readings m) e).2 < 2^w) :
    ∃ tr t, Runs pub macros scanStep s m tr t m ∧ traceCost tr ≤ 23 ∧
      q.loaded (.ofWords t m) ∧ (t 24).val = readings m (nodeAddr q.nodes ptr) ∧
      (t 26).val = (s 26).val + (q.weights (readings m) e).1 ∧
      (t 27).val = (s 27).val + (q.weights (readings m) e).2 := by
  let z := NatState.ofWords s m
  have hzload : q.loaded z := h
  obtain ⟨h₀,h₁,h₂,h₃,h₄,h₂₀,h₂₁,_,h₂₉,h₃₀⟩ := hzload
  change z.mem _ = _ at dir other width
  have hptr : z.reg 24 = ptr := hp
  have safe := readNode_safe w (readings pub) z h₂₀ h₃₀ (hptr ▸ live)
    (by simpa only [h₂₉,hptr] using room) (by simpa only [h₂₁,h₂₉,hptr,other] using lab)
  obtain ⟨gs,b,mb,read,rcost,he⟩ := readNode.runFixed pub macros s m safe
  obtain ⟨next,hd,ho,hw,hl,hm,_⟩ := readNode_eval (readings pub) z h₂₀ h₃₀
  rw [← he] at next hd ho hw hl hm
  have me : mb = m := same_memory hm
  subst mb
  rw [h₂₉,hptr] at next hd ho hw hl
  rw [h₂₁,other] at hl
  rw [dir] at hd
  rw [other] at ho
  rw [width] at hw
  have hb := stable read q h (by decide)
  obtain ⟨b₀,b₁,b₂,b₃,b₄,_⟩ := hb
  obtain ⟨u,edge,old,new,_⟩ := edgeContrib_run (pub := pub) (macros := macros) (m := m) b
    (by change 0 < (NatState.ofWords b m).reg 0; simpa only [b₀] using hz)
    (by change (NatState.ofWords b m).reg 8 * (NatState.ofWords b m).reg 0 ^ 2 < _; simpa only [hw,b₀] using mass)
  change (b 0).val = _ at b₀
  change (b 1).val = _ at b₁
  change (b 2).val = _ at b₂
  change (b 3).val = _ at b₃
  change (b 4).val = _ at b₄
  change (b 5).val = _ at hd
  change (b 6).val = _ at ho
  change (b 7).val = _ at hl
  change (b 8).val = _ at hw
  change (b 24).val = _ at next
  simp only [b₀,b₁,b₂,b₃,b₄,hd,ho,hl,hw] at old new
  have a : (u 9).val = (q.weights (readings m) e).1 := old
  have d : (u 10).val = (q.weights (readings m) e).2 := new
  have e26 : u 26 = s 26 := (edge.keepsReg (by decide)).trans (read.keepsReg (by decide))
  have e27 : u 27 = s 27 := (edge.keepsReg (by decide)).trans (read.keepsReg (by decide))
  have usafe : addWeights.fixedSafe w (readings pub) (.ofWords u m) := by
    simpa [addWeights, Code.fixedSafe, Code.fixedEval, Code.safeReadOnly, Code.evalNat,
      addressOpFits, NatState.ofWords, readings, Function.update, a,d,e26,e27] using And.intro lo hi
  obtain ⟨fs,t,mt,add,acost,ae⟩ := addWeights.runFixed pub macros u m usafe
  have mt' : mt = m := same_memory (congrArg NatState.mem ae)
  subst mt
  have values : (t 26).val = (s 26).val + (q.weights (readings m) e).1 ∧
      (t 27).val = (s 27).val + (q.weights (readings m) e).2 := by
    have eqr := congrArg NatState.reg ae
    simpa [addWeights, Code.fixedEval, Code.evalNat, addressOp, NatState.ofWords, readings,
      Function.update, a,d,e26,e27] using And.intro (congrFun eqr 26) (congrFun eqr 27)
  have rr : Runs pub macros scanStep s m _ t m := read.seq (edge.seq add)
  have ce := edge.deterministic_cost edgeContrib_deterministic
  simp only [List.length_replicate] at ce
  refine ⟨_,t,rr,?_,stable rr q h (by decide),?_,values⟩
  ·
    rw [cost_append,cost_append]
    change traceCost gs ≤ 12 at rcost
    change traceCost fs ≤ 2 at acost
    omega
  · rw [add.keepsReg (k := 24) (by decide),edge.keepsReg (k := 24) (by decide)]
    exact next

/-- The actual loop returns the sum of the old and new scaled contributions in
registers 26 and 27. Each visited node costs at most 24 ticks including its guard. -/
theorem scan_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (q : Query) (hz : 0 < q.Z) (s : Bank w) (m : Memory w) (h : q.loaded (.ofWords s m))
    {ptr : ℕ} {es : List Incident} (hp : (s 24).val = ptr)
    (chain : Chain (readings m) q.nodes ptr es) (room : q.room w (readings m) ptr es)
    (lo : (s 26).val + (q.sums (readings m) es).1 < 2^w)
    (hi : (s 27).val + (q.sums (readings m) es).2 < 2^w) :
    ∃ tr t, Runs pub macros scan s m tr t m ∧ traceCost tr ≤ 24*es.length+1 ∧
      (t 26).val = (s 26).val + (q.sums (readings m) es).1 ∧
      (t 27).val = (s 27).val + (q.sums (readings m) es).2 := by
  induction chain generalizing s with
  | nil =>
    have hz' := h.2.2.2.2.2.2.2.1
    exact ⟨_,s,.whileDone (show ¬ (s 23).val < (s 24).val by omega),by change 1 ≤ 24*0+1; decide,
      by simp [Query.sums], by simp [Query.sums]⟩
  | @cons ptr e es live hd ho hw _ ih =>
    rcases room with ⟨hr,hl,hm,rest⟩
    have sums : q.sums (readings m) (e::es) =
      ((q.weights (readings m) e).1+(q.sums (readings m) es).1,
       (q.weights (readings m) e).2+(q.sums (readings m) es).2) := by simp [Query.sums]
    rw [sums] at lo hi ⊢
    obtain ⟨gs,b,run,cost,loaded,next,old,new⟩ := row_run pub macros q hz s m h e ptr hp
      live hd ho hw hr hl hm (by omega) (by omega)
    obtain ⟨fs,t,tail,tc,t₁,t₂⟩ := ih b loaded next rest (by omega) (by omega)
    have zero : (s 23).val = 0 := h.2.2.2.2.2.2.2.1
    refine ⟨_,t,.whileStep (show (s 23).val < (s 24).val by omega) run tail,?_,by omega,by omega⟩
    change 1+traceCost (gs++fs) ≤ _
    rw [cost_append,List.length_cons,Nat.mul_succ]
    omega

end RoutingISA.LabelTrial

end BorderVNP
end Computability
end OAI
