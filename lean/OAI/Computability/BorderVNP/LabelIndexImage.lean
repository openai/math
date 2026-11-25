import OAI.Computability.BorderVNP.LabelIndexChains
import OAI.Computability.BorderVNP.LabelIndexRuns

/-! # Contents of the incidence and data directories reconstructed from public rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.LabelIndex

open RoutingISA.LabelTrial

/-- The chooser's input table describes one oriented cable per public row. -/
structure Cable where
  /-- Source cell in the public order. -/
  src : ℕ
  /-- Destination cell in the public order. -/
  dst : ℕ
  /-- Bit width of the compressed cable. -/
  width : ℕ

/-- The three words of a processed cable. -/
def cableAt (l : Layout) (m : ℕ → ℕ) (i : ℕ) : Cable :=
  let b := l.cables+i*3
  ⟨m b,m (b+1),m (b+2)⟩

/-- Destination cell and interval width in the original seven-word delivery. -/
def deliveryAt (l : Layout) (m : ℕ → ℕ) (i : ℕ) : ℕ × ℕ :=
  let b := l.deliveries+i*7
  (m (b+4),m (b+6))

/-- A live row contributes one node per endpoint; absorbed cables are skipped. -/
def Cable.prepend (e : Cable) (c : ℕ) (xs : List Incident) : List Incident :=
  if e.src = e.dst then xs else
    let ys := if c = e.src then ⟨0,e.dst,e.width⟩ :: xs else xs
    if c = e.dst then ⟨1,e.src,e.width⟩ :: ys else ys

/-- Reverse cable order at each cell, as obtained by linked prepend. -/
def incidents (rows : ℕ → Cable) (c : ℕ) : ℕ → List Incident
  | 0 => []
  | i+1 => (rows i).prepend c (incidents rows c i)

/-- Summed width of a descriptor prefix, before any division into bits. -/
def sumWidth (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => sumWidth f i + f i

/-- Live cable volume, excluding same-cell rows already absorbed. -/
def liveWidth (r : Cable) := if r.src = r.dst then 0 else r.width

/-- Allocation of disjoint output intervals after both public input tables. -/
structure Allocated (l : Layout) : Prop where
  /-- Cable input finishes before chooser scratch. -/
  cables : l.cables+l.cableCount*3 ≤ l.heads
  /-- Data input finishes before chooser scratch. -/
  deliveries : l.deliveries+l.deliveryCount*7 ≤ l.heads
  /-- End of the per-cell heads. -/
  heads : l.heads+l.cells ≤ l.nodes
  /-- End of the paired four-word incidence nodes. -/
  nodes : l.nodes+l.cableCount*8 ≤ l.data
  /-- End of the per-cell demand words. -/
  data : l.data+l.cells ≤ l.cableMean
  /-- End of the directed-pair mean table. -/
  cableMean : l.cableMean+l.labels*l.labels ≤ l.dataMean

/-- Valid cell ordinals in the actual descriptors. -/
structure Endpoints (l : Layout) (m : ℕ → ℕ) : Prop where
  /-- Both endpoints of every cable row belong to the layout. -/
  cables : ∀ i < l.cableCount, (cableAt l m i).src < l.cells ∧ (cableAt l m i).dst < l.cells
  /-- Each delivery addresses one of the cells. -/
  deliveries : ∀ i < l.deliveryCount, (deliveryAt l m i).1 < l.cells

/-- The two source tables agree with the unmodified input. -/
def Inputs (l : Layout) (before mem : ℕ → ℕ) : Prop :=
  ∀ k < l.heads, mem k = before k

/-- The three decoded cable columns survive all scratch writes. -/
theorem Inputs.cable {l : Layout} {m t : ℕ → ℕ} (h : Inputs l m t) (al : Allocated l)
    {i : ℕ} (hi : i < l.cableCount) : cableAt l t i = cableAt l m i := by
  dsimp only [cableAt]
  have b := al.cables
  rw [h _ (by omega),h _ (by omega),h _ (by omega)]

/-- The two delivery columns used for aggregation survive all scratch writes. -/
theorem Inputs.delivery {l : Layout} {m t : ℕ → ℕ} (h : Inputs l m t) (al : Allocated l)
    {i : ℕ} (hi : i < l.deliveryCount) : deliveryAt l t i = deliveryAt l m i := by
  dsimp only [deliveryAt]
  have b := al.deliveries
  rw [h _ (by omega),h _ (by omega)]

/-- State of the directory after clearing a prefix of cells, processing cable and
delivery prefixes, and filling prefixes of the two mean arrays. -/
structure View (l : Layout) (m : ℕ → ℕ) (a : Acc) (cells cables deliveries pairs bins : ℕ) : Prop where
  /-- Unmodified source region. -/
  input : Inputs l m a.mem
  /-- The list at each initialized head has the specified incident rows. -/
  lists : ∀ c < cells, Linked a.mem l.nodes (2*cables) (a.mem (l.heads+c))
    (incidents (cableAt l m) c cables)
  /-- Total deliveries to each initialized cell. -/
  data : ∀ c < cells, a.mem (l.data+c) = sumWidth
    (fun i => if (deliveryAt l m i).1 = c then (deliveryAt l m i).2 else 0) deliveries
  /-- Original total of live cable widths. -/
  cableTotal : a.cableTotal = sumWidth (liveWidth ∘ cableAt l m) cables
  /-- Original total of delivery widths. -/
  dataTotal : a.dataTotal = sumWidth (Prod.snd ∘ deliveryAt l m) deliveries
  /-- Initialized cable bins scaled by the common denominator. -/
  pairs : ∀ k < pairs, a.mem (l.cableMean+k) = a.cableTotal
  /-- Initialized data bins scaled by the common denominator. -/
  bins : ∀ k < bins, a.mem (l.dataMean+k) = a.dataTotal*l.labels

/-- Empty directories satisfy all prefix claims before initialization. -/
theorem View.empty (l : Layout) (m : ℕ → ℕ) : View l m ⟨m,0,0⟩ 0 0 0 0 0 :=
  ⟨fun _ _ => rfl,by simp,by simp,rfl,rfl,by simp,by simp⟩

/-- Zeroing both words of the next cell initializes its head and its data demand. -/
theorem View.clear {l m a i} (v : View l m a i 0 0 0 0) (al : Allocated l) (hi : i < l.cells) :
    View l m (Phase.clear.step l i a) (i+1) 0 0 0 0 := by
  have sep := al.heads
  have nn := al.nodes
  constructor
  · intro k hk
    simpa only [Phase.step,Function.update_of_ne (show k ≠ l.data+i by omega),
      Function.update_of_ne (show k ≠ l.heads+i by omega)] using v.input k hk
  · intro k hk
    change Function.update (Function.update a.mem (l.heads+i) 0) (l.data+i) 0 (l.heads+k) = 0
    rw [Function.update_of_ne (by omega)]
    by_cases eq : k = i
    · simp [eq]
    · rw [Function.update_of_ne (by omega)]
      exact v.lists k (by omega)
  · intro k hk
    change Function.update (Function.update a.mem (l.heads+i) 0) (l.data+i) 0 (l.data+k) = 0
    by_cases eq : k = i
    · simp [eq]
    · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
      exact v.data k (by omega)
  · exact v.cableTotal
  · exact v.dataTotal
  · simp
  · simp

private theorem view_push_input {l : Layout} {m t : ℕ → ℕ} (h : Inputs l m t)
    (al : Allocated l) (c n : ℕ) (e : Incident) :
    Inputs l m (push t l.heads l.nodes n c e.dir e.other e.width) := by
  intro k hk
  have sep := al.heads
  exact (push_outside _ _ _ _ _ _ _ _ _ (by omega) (Or.inl (by omega))).trans (h k hk)

/-- One live cable is added to exactly its two cells in the correct orientations.
An absorbed cable leaves the lists and volumes intact. -/
theorem View.cable {l m a i} (v : View l m a l.cells i 0 0 0)
    (al : Allocated l) (ep : Endpoints l m) (hi : i < l.cableCount) :
    View l m (Phase.cable.step l i a) l.cells (i+1) 0 0 0 := by
  let e := cableAt l m i
  have same := v.input.cable al hi
  have s : a.mem (l.cables+i*3) = e.src := congrArg Cable.src same
  have d : a.mem (l.cables+i*3+1) = e.dst := congrArg Cable.dst same
  have w : a.mem (l.cables+i*3+2) = e.width := congrArg Cable.width same
  have endpoints := ep.cables i hi
  change e.src < l.cells ∧ e.dst < l.cells at endpoints
  by_cases eq : e.src = e.dst
  · simp only [Phase.step,s,d,ite_eq_left eq]
    refine ⟨v.input,?_,v.data,?_,v.dataTotal,by simp,by simp⟩
    · intro c hc
      simp only [incidents,Cable.prepend,show cableAt l m i = e from rfl,ite_eq_left eq]
      exact (v.lists c hc).copy (by omega) (fun _ _ _ => rfl)
    · simpa only [sumWidth,Function.comp_apply,show cableAt l m i = e from rfl,liveWidth,ite_eq_left eq,Nat.add_zero] using v.cableTotal
  · let m1 := push a.mem l.heads l.nodes (i*2) e.src 0 e.dst e.width
    let m2 := push m1 l.heads l.nodes (i*2+1) e.dst 1 e.src e.width
    simp only [Phase.step,s,d,w,ite_eq_right eq]
    refine ⟨view_push_input (view_push_input v.input al e.src (i*2) ⟨0,e.dst,e.width⟩)
      al e.dst (i*2+1) ⟨1,e.src,e.width⟩,?_,?_,?_,v.dataTotal,by simp,by simp⟩
    · let ls c := incidents (cableAt l m) c i
      have old : ∀ k < l.cells, Linked a.mem l.nodes (i*2) (a.mem (l.heads+k)) (ls k) := by
        simpa only [Nat.mul_comm i 2] using v.lists
      let e1 : Incident := ⟨0,e.dst,e.width⟩
      let e2 : Incident := ⟨1,e.src,e.width⟩
      have added := push_lists e1 old al.heads endpoints.1
      intro c hc
      have twice := push_lists e2 added al.heads endpoints.2 c hc
      simpa only [incidents,Cable.prepend,show cableAt l m i = e from rfl,ite_eq_right eq,
        show 2*(i+1) = i*2+1+1 by omega] using twice
    · intro c hc
      have hh := al.heads
      have nn := al.nodes
      have outside1 : m1 (l.data+c) = a.mem (l.data+c) := by apply push_outside <;> omega
      have outside2 : m2 (l.data+c) = m1 (l.data+c) := by apply push_outside <;> omega
      exact outside2.trans (outside1.trans (v.data c hc))
    · simp only [sumWidth,Function.comp_apply,show cableAt l m i = e from rfl,liveWidth,
        ite_eq_right eq,v.cableTotal]

end Cube.LabelIndex

end BorderVNP
end Computability
end OAI
