import OAI.ThreeFlat.Diagonal.PhysicalNodeTape

namespace OAI
/-! # The sixteen node-publisher fields computed from two adjacent physical stage headers -/

namespace ThreeFlat.Diagonal.NavigationPass.TraceNodeHeaders

open RAM RAM.NavigationNodeRows NavigationDirectory CompressorPacking.Native
open scoped Classical

/-- The next chronological ID is the end of the input site interval. -/
def nextId (words : ℕ → ℕ) := words 6 + words 5

/-- Both directory formats publish five kernel-header words per successor site. -/
def outputCount (words : ℕ → ℕ) := words 35 / 5

def decodeLayer (address : ℕ) (words : ℕ → ℕ) : Layer :=
  ⟨nextId words, outputCount words, if words 33 = 1 then 1 else 2,
   if words 33 = 1 then words 5 / outputCount words else 1,
   words 42, words 34, words 38, address⟩

def decodeParent (words : ℕ → ℕ) : Parent := ⟨false, nextId words, words 44⟩

theorem nextId_allocate (K : ℕ) (c : Cursor) (op : Stage) :
    nextId (allocate K c op).words = (allocate K c op).next.node := by
  cases op <;> rfl

theorem outputCount_allocate (K : ℕ) (c : Cursor) (op : Stage) :
    outputCount (allocate K c op).words = successors op := by
  cases op with
  | shrink x =>
    change (5 * x.outputSites) / 5 = x.outputSites
    omega
  | refresh v m l h p =>
    change (5 * (RefreshStageLayout.counts v m l h p).nodes) / 5 = _
    change (5 * (RefreshStageLayout.counts v m l h p).nodes) / 5 =
      (RefreshStageLayout.counts v m l h p).nodes
    omega

theorem decodeLayer_allocate (K : ℕ) (c : Cursor) (op : Stage) (populated : 0 < successors op) :
    decodeLayer c.header (allocate K c op).words = nodeLayer K c op := by
  unfold decodeLayer nodeLayer
  rw [nextId_allocate, outputCount_allocate]
  cases op with
  | refresh v m l h p => rfl
  | shrink x =>
    have ratio : x.originalSites = x.outputSites * (x.oldDegree * 2^x.colorBits) := by
      unfold ShrinkStage.Dimensions.originalSites ShrinkStage.Dimensions.originalLanes
        ShrinkStage.Dimensions.outputSites ShrinkStage.Dimensions.newBase
      ac_rfl
    change 0 < x.outputSites at populated
    have arity : x.originalSites / x.outputSites = x.oldDegree * 2^x.colorBits := by
      rw [ratio, Nat.mul_div_cancel_left _ populated]
    change Layer.mk _ _ 1 (x.originalSites / x.outputSites) _ _ _ _ =
      Layer.mk _ _ 1 (x.oldDegree * 2^x.colorBits) _ _ _ _
    rw [arity]

theorem decodeParent_allocate (K : ℕ) (c : Cursor) (op : Stage) :
    decodeParent (allocate K c op).words =
      ⟨false,(allocate K c op).next.node,(allocate K c op).words 44⟩ := by
  unfold decodeParent
  rw [nextId_allocate]

/-- The source table is the installed 64-word navigation directory. -/
def MountedAt (m : ℕ → ℕ) (K : ℕ) : List Stage → Cursor → Prop
  | [], _ => True
  | op :: ops, c =>
    (∀ j < 64, j ≠ 27 → m (c.header+j) = (allocate K c op).words j) ∧
      MountedAt m K ops (allocate K c op).next

theorem MountedAt.of_splits (m : ℕ → ℕ) (K : ℕ) (ops : List Stage) (c : Cursor)
    (each : ∀ pre op post, ops=pre++op::post → ∀ j<64, j≠27 →
      m ((finish K pre c).header+j)=(allocate K (finish K pre c) op).words j) :
    MountedAt m K ops c := by
  induction ops generalizing c with
  | nil => trivial
  | cons op ops ih =>
    refine ⟨each [] op ops rfl,?_⟩
    apply ih
    intro pre t post hs j hj hq
    apply each (op::pre) t post _ j hj hq
    simp [hs]

def readLayer (m : ℕ → ℕ) (address : ℕ) :=
  decodeLayer address (fun j => m (address+j))

def readParent (m : ℕ → ℕ) (address : ℕ) :=
  decodeParent (fun j => m (address+j))

theorem readLayer_at {m : ℕ → ℕ} {K : ℕ} {c : Cursor} {op : Stage}
    (hit : ∀ j < 64, j ≠ 27 → m (c.header+j) = (allocate K c op).words j) (hs : 0 < successors op) :
    readLayer m c.header = nodeLayer K c op := by
  rw [← decodeLayer_allocate K c op hs]
  simp [readLayer, decodeLayer, nextId, outputCount, hit]

theorem readParent_at {m : ℕ → ℕ} {K : ℕ} {c : Cursor} {op : Stage}
    (hit : ∀ j < 64, j ≠ 27 → m (c.header+j) = (allocate K c op).words j) :
    readParent m c.header = ⟨false,(allocate K c op).next.node,(allocate K c op).words 44⟩ := by
  rw [← decodeParent_allocate]
  simp [readParent, decodeParent, nextId, hit]

/-- A physical source cursor and a compact destination cursor advance by 64 and 16 words. -/
def compactTape (b : Banks) (m : ℕ → ℕ) : ℕ → ℕ → ℕ → Layer → List ℕ
  | 0, _, dst, s =>
    List.ofFn (fun j : Fin 16 => header b s ⟨true,0,0⟩ (dst+16) j.val)
  | t+1, src, dst, s =>
    List.ofFn (fun j : Fin 16 => header b s (readParent m src) (dst+16) j.val) ++
      compactTape b m t (src+64) (dst+16) (readLayer m src)

theorem compactTape_exact (b : Banks) (m : ℕ → ℕ) (K : ℕ)
    (ops : List Stage) (c : Cursor) (dst : ℕ) (seed : Layer) (mounted : MountedAt m K ops c)
    (live : ∀ op ∈ ops, 0 < successors op) :
    compactTape b m ops.length c.header dst seed = nodeTape b dst (nodeLayers K ops c seed) := by
  induction ops generalizing c dst seed with
  | nil => simp [compactTape,nodeLayers,nodeTape]
  | cons op ops ih =>
    obtain ⟨head,tail⟩ := mounted
    have step : (allocate K c op).next.header = c.header+64 := by cases op <;> rfl
    simp only [List.length_cons,compactTape,nodeLayers,nodeTape]
    rw [readParent_at head,readLayer_at head (live op (List.mem_cons_self ..)),←step]
    rw [ih _ _ _ tail (fun q hq => live q (List.mem_cons_of_mem _ hq))]


end ThreeFlat.Diagonal.NavigationPass.TraceNodeHeaders

end OAI
