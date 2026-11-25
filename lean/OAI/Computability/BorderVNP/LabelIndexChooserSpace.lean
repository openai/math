import OAI.Computability.BorderVNP.LabelIndexTrialRoom
import OAI.Computability.BorderVNP.CubeLabelISAPassRoom

/-! # Static words of the indexed label chooser at every cell and bin -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LabelTrial

/-- Completed cell decisions alter only cache words and the labels already assigned. -/
theorem Frame.prefix_off (p : Frame) (z : ℕ) (rows : ℕ → List Incident) (m : ℕ → ℕ) (c a : ℕ)
    (cache : ∀ i < p.Z^2+p.Z, a ≠ p.cacheAddr i) (lab : ∀ j < c, a ≠ p.labels+j) :
    p.prefix z rows m c a = m a := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [Frame.prefix,Function.update_of_ne (lab c (Nat.lt_succ_self _))]
    unfold Frame.updated
    rw [PassBins.image_off _ _ _ a cache]
    exact ih fun j hj => lab j (Nat.lt_succ_of_lt hj)

private theorem sums_congr (q : Query) (m n : ℕ → ℕ) (es : List Incident)
    (labels : ∀ e ∈ es, m (q.labels+e.other) = n (q.labels+e.other)) : q.sums m es = q.sums n es := by
  have eq : es.map (q.weights m) = es.map (q.weights n) := List.map_congr_left fun e he =>
    by simp only [Query.weights,labels e he]
  simpa only [Query.sums,List.map_map,Function.comp_def] using congrArg (fun xs : List (ℕ×ℕ) =>
    ((xs.map Prod.fst).sum,(xs.map Prod.snd).sum)) eq

/-- Numerators are functions only of the incident endpoint labels and the cell's own demand. -/
theorem Frame.incident_congr (p : Frame) (c v i : ℕ) (m n : ℕ → ℕ) (es : List Incident)
    (labs : ∀ e ∈ es, m (p.labels+e.other) = n (p.labels+e.other))
    (data : m (p.demands+c) = n (p.demands+c)) :
    p.incident c v i m es = p.incident c v i n es := by
  unfold incident
  split
  · exact sums_congr _ m n es labs
  · rw [data]

end RoutingISA.LabelTrial

namespace Cube.LabelIndex

open RoutingISA.LabelTrial

/-- A cache word always belongs to one of the two allocated bin segments. -/
theorem cache_between (l : Layout) (al : Allocated l) (lab i : ℕ) (hi : i < l.labels^2+l.labels) :
    l.cableMean ≤ (l.trialFrame lab).cacheAddr i ∧ (l.trialFrame lab).cacheAddr i < l.dataMean+l.labels := by
  have sep := al.cableMean
  rw [← pow_two] at sep
  change l.cableMean ≤ (if i < l.labels^2 then l.cableMean+i else l.dataMean+(i-l.labels^2)) ∧ _
  dsimp only [Layout.trialFrame,Frame.cacheAddr]
  split <;> omega

/-- The output label array can be placed before the heads or after the final cache. -/
def LabelSegment (l : Layout) (lab : ℕ) : Prop :=
  lab+l.cells ≤ l.heads ∨ l.dataMean+l.labels ≤ lab

/-- The endpoint label of any real cell is outside the whole bin cache. -/
theorem LabelSegment.off_cache {l : Layout} {lab : ℕ} (placement : LabelSegment l lab)
    (al : Allocated l) {c i : ℕ} (hc : c < l.cells) (hi : i < l.labels^2+l.labels) :
    lab+c ≠ (l.trialFrame lab).cacheAddr i := by
  have bounds := cache_between l al lab i hi
  have heads := al.heads
  have nodes := al.nodes
  have data := al.data
  unfold LabelSegment at placement
  omega

/-- Words between the heads and the first cache survive every completed cell. -/
theorem prefix_directory {l : Layout} (al : Allocated l) {lab : ℕ} (placement : LabelSegment l lab)
    (z : ℕ) (rows : ℕ → List Incident) (m : ℕ → ℕ) (c a : ℕ) (hc : c ≤ l.cells)
    (lo : l.heads ≤ a) (hi : a < l.cableMean) :
    (l.trialFrame lab).prefix z rows m c a = m a := by
  apply Frame.prefix_off
  · intro i h
    have bounds := cache_between l al lab i h
    omega
  · intro j hj
    change a ≠ lab+j
    have sep := al.cableMean
    unfold LabelSegment at placement
    omega

/-- Public word bounds for the source directory and its cable and demand sums. -/
structure ChooserSpace (l : Layout) (m : ℕ → ℕ) (lab w : ℕ) : Prop where
  /-- The final cache segment fits in the word address space. -/
  endAddr : l.dataMean+l.labels ≤ 2^w
  /-- All label words fit in the same address space. -/
  labelAddr : lab+l.cells ≤ 2^w
  /-- All cable subtotals, scaled by the common denominator, fit. -/
  cableCap : sumWidth (Cable.width ∘ cableAt l m) l.cableCount*l.labels^2 < 2^w
  /-- All scaled demand subtotals fit. -/
  dataCap : sumWidth (Prod.snd ∘ deliveryAt l m) l.deliveryCount*l.labels^2 < 2^w

/-- Native scan guards and numerators on a partially written bin pass agree with those on
the current prefix. The addresses come from the initialized sparse directory. -/
theorem indexed_pass_space {l : Layout} {m : ℕ → ℕ} {a : Acc}
    (view : View l m a l.cells l.cableCount l.deliveryCount (l.labels*l.labels) l.labels)
    (al : Allocated l) (ep : Endpoints l m) {lab w : ℕ} (placement : LabelSegment l lab)
    (space : ChooserSpace l m lab w) (z c v i : ℕ) (commit : Bool)
    (hz : 0 < l.labels) (hc : c < l.cells) (hi : i < l.labels^2+l.labels) :
    let p := l.trialFrame lab
    let rows := fun j => incidents (cableAt l m) j l.cableCount
    let t := p.prefix z rows a.mem c
    let cur := (p.bins c v t (rows c)).memory commit t i
    p.room w c v i cur (rows c) ∧ p.incident c v i cur (rows c) = p.incident c v i t (rows c) := by
  intro p rows t cur
  have untouched (x : ℕ) (off : ∀ j < i, x ≠ p.cacheAddr j) : cur x = t x := by
    cases commit with
    | false => rfl
    | true => exact (p.bins c v t (rows c)).image_off t i x off
  have prev (x : ℕ) (lo : l.heads ≤ x) (high : x < l.cableMean) : cur x = a.mem x := by
    rw [untouched x (fun j hj eq => by have hlow : l.cableMean ≤ p.cacheAddr j := (cache_between l al lab j (hj.trans hi)).1; omega)]
    exact prefix_directory al placement z rows a.mem c x hc.le lo high
  have heads := al.heads
  have nodes := al.nodes
  have data := al.data
  have de := untouched (l.data+c) (fun j hj eq => by
    have hlow : l.cableMean ≤ p.cacheAddr j := (cache_between l al lab j (hj.trans hi)).1; omega)
  refine ⟨frame_room view al ep cur lab w c v i hz hc hi (prev _ (by omega) (by omega))
    (fun x lo high => prev x (by omega) (by omega)) (prev _ (by omega) (by omega))
    space.endAddr space.labelAddr space.cableCap space.dataCap, p.incident_congr c v i cur t (rows c) ?_ de⟩
  intro e he
  have hb := (incidents_bounded l m ep c le_rfl).1 e he
  exact untouched _ (fun j hj => placement.off_cache al hb (hj.trans hi))

end Cube.LabelIndex

end BorderVNP
end Computability
end OAI
