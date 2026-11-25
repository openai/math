import OAI.Computability.BorderVNP.CubeRoutePinnedEntry
import OAI.Computability.BorderVNP.CubeTeamOwnedGroupImage

/-! # A common team assignment from the actual public data, labels and declaration -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube LocalRow CubeArena Transmission Packing.Directory

variable (a : CubeArena.Layout) (frame : ℕ) (axis : Fin (a.n+1)) (R : ℕ)
local notation "weights" => weightLayout a frame axis.val

private theorem array_word (m : ℕ → ℕ) (saved : ℕ) {x : ℕ} (lo : a.publicBase ≤ x) (hi : x < a.powerBase) :
    powerHeaderImage a saved m x = m x := by
  change headerImage a.header a.n _ _ (CubePowers.image a.header.d a.powerBase (a.n+1) m) x = _
  rw [headerImage_outside _ _ _ _ _ _ (.inr ((arena_label_arrays a).1.trans lo))]
  simp [CubePowers.image,show ¬a.powerBase ≤ x by omega]

/-- The power and header passes retain precisely the label and incoming demand of every cell. -/
theorem cell_words_after_header (m : ℕ → ℕ) (saved c : ℕ) (hc : c < a.cells) :
    powerHeaderImage a saved m (a.publicBase+c) = m (a.publicBase+c) ∧
      powerHeaderImage a saved m (a.demands+c) = m (a.demands+c) := by
  obtain ⟨_,endLabels,startData,endData,widths⟩ := arena_label_arrays a
  exact ⟨array_word a m saved (by omega) (by omega),array_word a m saved (by omega) (by omega)⟩

/-- The shared dense declaration seen by the physical group schedule is exactly the table
in the pinned nine-stage return. This holds through both intervening directory writers. -/
theorem NativeEntry.stored_rows {w controls : ℕ} {input orig final : ℕ → ℕ} {P : (ℕ → ℕ) → Prop}
    (entry : NativeEntry a frame controls axis R input orig final)
    (sources : DirectorySources a frame controls axis P w final)
    (rows : Sym2 (Fin a.header.d) → Fin (a.n+1) → ℕ) (axes : a.header.a=a.n+1)
    (table : ∀ m, P m → CubeLengths.StoredRows m (a.header.header+13+a.header.entries) rows) :
    CubeLengths.StoredRows input (a.header.header+13+a.header.entries) rows := by
  obtain ⟨assigned,res,im⟩ := entry.image
  obtain ⟨ms,mc,prop,cells,pairs⟩ := sources
  have stored := table (readings ms) prop
  intro u v j
  let x := a.header.header+13+a.header.entries+(CubeLengths.entryOrder a.header.d (a.n+1) ((u,v),j)).val
  have rowLt := (CubeLengths.entryOrder a.header.d (a.n+1) ((u,v),j)).isLt
  have below : x < a.header.packetBase := by
    change _ < a.header.d*a.header.d*(a.n+1) at rowLt
    simp only [x,CubeHeaderInstall.Inputs.packetBase,CubeHeaderInstall.Inputs.entries,axes]
    omega
  obtain ⟨hh,lab,grp,own,pair,host,rec,stop⟩ := a.writer_order
  have hp := (arena_label_arrays a).1
  have actual := scheduled_before a res im.pairRows ⟨rfl,rfl,rfl,rfl,rfl⟩ (x:=x) (by omega)
  have after := pairs.outside x (Or.inl (by change x < a.pairDirectory; omega))
  have c := (a.cellWriter frame controls axis).written_outside (readings ms) (a.cellWriter frame controls axis).cells x
    (Or.inl (by change x < a.hostDirectory; omega))
  change input x = _
  rw [← actual,after,congrFun cells x,c]
  exact stored u v j

private theorem row_word {m : ℕ → ℕ} {rows : Sym2 (Fin a.header.d) → Fin (a.n+1) → ℕ}
    (stored : CubeLengths.StoredRows m (a.header.header+13+a.header.entries) rows)
    (s t : ℕ) (hs : s < a.header.d) (ht : t < a.header.d) :
    m ((weights).rowAddr s t) = rows (Sym2.mk ⟨min s t,(min_le_left s t).trans_lt hs⟩ ⟨max s t,max_lt hs ht⟩) axis := by
  let x : Fin a.header.d := ⟨min s t,(min_le_left s t).trans_lt hs⟩
  let y : Fin a.header.d := ⟨max s t,max_lt hs ht⟩
  have le : x ≤ y := (min_le_left s t).trans (le_max_left s t)
  have read := stored x y axis
  rw [CubeLengths.entryOrder_val,ite_eq_left le] at read
  simpa only [x,y,weightLayout,GroupWeights.Layout.rowAddr,Nat.add_assoc] using read

private theorem loads_prefix (left right : ℕ → ℕ) (k : ℕ) (eq : ∀ j < k, left j=right j) :
    TeamNative.loads R left k=TeamNative.loads R right k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [TeamNative.loads,TeamNative.loads,ih (fun j hj => eq j (by omega)),eq k (by omega)]

/-- The same physical declaration and actual native per-cell words force the same integer
histogram, greedy owner of each symbol and receiving team of each placed cell. -/
theorem common_owners {u v : ℕ → ℕ} (positive : 0 < a.header.d)
    (rows : Sym2 (Fin a.header.d) → Fin (a.n+1) → ℕ)
    (first : CubeLengths.StoredRows u (a.header.header+13+a.header.entries) rows)
    (second : CubeLengths.StoredRows v (a.header.header+13+a.header.entries) rows)
    (cells : ∀ c < a.cells, u (a.publicBase+c)=v (a.publicBase+c) ∧ u (a.demands+c)=v (a.demands+c)) :
    (∀ s < a.header.d, (weights).weight u s=(weights).weight v s) ∧
      (∀ s : Fin a.header.d, TeamNative.owner R ((weights).weight u) s.val =
        TeamNative.owner R ((weights).weight v) s.val) ∧
      ∀ c < a.cells, a.receivingOwner frame axis R u c = a.receivingOwner frame axis R v c := by
  have symbol (c : ℕ) (hc : c < a.cells) : (weights).symbol u c = (weights).symbol v c := by
    change u (a.publicBase+c)/_ % _ = v (a.publicBase+c)/_ % _
    rw [(cells c hc).1]
  have same (s : ℕ) (hs : s < a.header.d) : (weights).weight u s=(weights).weight v s := by
    unfold GroupWeights.Layout.weight
    congr 1
    · apply Finset.sum_congr rfl
      intro q _
      have modLt := Nat.mod_lt q positive
      unfold GroupWeights.Layout.rowCharge
      rw [show (weights).groups = a.header.d from rfl]
      rw [row_word a frame axis first s (q%a.header.d) hs modLt,row_word a frame axis second s (q%a.header.d) hs modLt]
    · apply Finset.sum_congr rfl
      intro c hc
      have inside : c < a.cells := Finset.mem_range.mp hc
      unfold GroupWeights.Layout.dataCharge
      rw [symbol c inside]
      change (if _ then u (a.demands+c) else 0) = if _ then v (a.demands+c) else 0
      rw [(cells c inside).2]
  have owners (s : Fin a.header.d) : TeamNative.owner R ((weights).weight u) s.val =
      TeamNative.owner R ((weights).weight v) s.val :=
    congrArg firstMinimum (loads_prefix R _ _ s.val (fun j hj => same j (hj.trans s.isLt)))
  refine ⟨same,owners,fun c hc => ?_⟩
  unfold CubeArena.Layout.receivingOwner
  rw [symbol c hc]
  exact owners ⟨(weights).symbol v c,Nat.mod_lt _ positive⟩

/-- Reindex the data compiler's placement by the common receiver assignment, using
only cell numbers that actually occur in its positive-width directory. -/
theorem DemandInput.congr_owner {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {w : ℕ}
    {pub : Arg → Word w} {m : Memory w} {u v : ℕ → Fin (R+1)} (h : DemandInput a D pp lp u pub m)
    {I : Type*} [Fintype I] {cell : I → Fin a.cells} {id : I ↪ ℕ} {width : I → ℕ}
    (place : Packing.Directory.BankPlacement D pp lp I cell id width) (bounds : D.DestinationBounds)
    (same : ∀ c < a.cells, u c=v c) : DemandInput a D pp lp v pub m := by
  refine ⟨h.ready,h.records,h.count,h.raw,fun i => ?_⟩
  have eq := same _ (BankPlacement.populated_cell_lt place bounds i)
  exact ⟨(h.cells i).1.trans (congrArg Fin.val eq),(h.cells i).2⟩

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
