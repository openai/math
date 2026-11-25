import OAI.Optimization.LinearProgramming.Geometry.BorderLayout
import OAI.Optimization.LinearProgramming.Geometry.BorderScatter

/-! Persistent array invariants for streaming signed minors, prices, and online replies into
the actual three-word layout consumed by the deterministic pivot maximization loop. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM BorderScatter

variable {r n : ℕ}

/-- The packet computation and reply decoding leave both the scan cursors and all live arrays
below the scratch region untouched. -/
structure Holding (base : ℕ) (a b : Memory ℚ) : Prop where
  indices (p) : p=84 ∨ p=85 ∨ p=86 ∨ p=90 ∨ 128 ≤ p → b.index p=a.index p
  data (p) : 32 ≤ p → p < base → b.data p=a.data p

theorem Holding.trans {base : ℕ} {m u t : Memory ℚ} (a : Holding base m u) (b : Holding base u t) :
    Holding base m t := ⟨fun p hp => (b.indices p hp).trans (a.indices p hp),
      fun p hp hbase => (b.data p hp hbase).trans (a.data p hp hbase)⟩

structure PackedCell (t : Memory ℚ) (base i : ℕ) (raw log price : ℚ) : Prop where
  first : t.data (base+3*i)=raw
  second : t.data (base+3*i+1)=log
  third : t.data (base+3*i+2)=price

/-- Cells external to the current triple tape survive every prefix, including a restart. -/
structure ScanFrame (L : Layout r n) (m t : Memory ℚ) : Prop where
  indices (p) : 128 ≤ p → p ≠ 139 → t.index p=m.index p
  data (p) : 32 ≤ p → p < L.scratch → (p < L.triples ∨ L.triples+3*n ≤ p) → t.data p=m.data p

structure ScanStopped (L : Layout r n) (m t : Memory ℚ) : Prop extends ScanFrame L m t where
  status : t.index 139=1
  finished : t.index 90=n
  width : t.index 130=n

/-- The values at the remaining entries are still zero. In particular skipping a zero minor
stores zero exactly, without inventing a compression-service request. -/
structure ScanReady (L : Layout r n) (m : Memory ℚ) (raw price : Fin n → ℚ) (A : ℚ → Prop)
    (i : ℕ) (values : Fin n → ℚ) (t : Memory ℚ) : Prop extends ScanFrame L m t where
  cursor : t.index 90=i
  status : t.index 139=0
  minorPointer : t.index 84=L.answers+i
  pricePointer : t.index 85=L.prices+i
  destPointer : t.index 86=L.triples+3*i
  cells (j : Fin n) (earlier : j.val < i) : PackedCell t L.triples j.val (raw j) (values j) (price j)
  untouched (j : Fin n) (later : i ≤ j.val) : values j=0
  bounded (j : Fin n) : A (values j)

variable {L : Layout r n} {m u t : Memory ℚ} {A : ℚ → Prop} {raw price vals : Fin n → ℚ} {i : ℕ}

theorem ScanFrame.afterHold (old : ScanFrame L m u) (h : Holding L.scratch u t) : ScanFrame L m t :=
  ⟨fun p hp hn => (h.indices p (by omega)).trans (old.indices p hp hn),
   fun p hp hs hr => (h.data p hp hs).trans (old.data p hp hs hr)⟩

theorem ScanReady.hold (old : ScanReady L m raw price A i vals u) (h : Holding L.scratch u t) :
    ScanReady L m raw price A i vals t := by
  refine ⟨old.toScanFrame.afterHold h,(h.indices 90 (by decide)).trans old.cursor,
    (h.indices 139 (by decide)).trans old.status,(h.indices 84 (by decide)).trans old.minorPointer,
    (h.indices 85 (by decide)).trans old.pricePointer,(h.indices 86 (by decide)).trans old.destPointer,?_,
    old.untouched,old.bounded⟩
  intro j ltj
  obtain ⟨a,b,c⟩ := old.cells j ltj
  have lo := L.source_ge; have s := L.source_end; have p := L.prices_end
  have x := L.triples_end; have y := L.rounded_end; have z := L.answers_end; have jj := j.isLt
  exact ⟨(h.data _ (by omega) (by omega)).trans a,(h.data _ (by omega) (by omega)).trans b,
    (h.data _ (by omega) (by omega)).trans c⟩

theorem scanInit {k : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {J : Fin k → Fin n}
    (h : L.Ready D J m) (raw price : Fin n → ℚ) (A : ℚ → Prop) (hz : A 0) :
    ScanReady L m raw price A 0 0 (initState m) := by
  obtain ⟨h84,h85,h86,h90,h139,hd,hi⟩ := init_out m
  refine ⟨⟨fun p hp hn => hi p (by omega) (by omega) (by omega) (by omega) hn,
    fun _ _ _ _ => congrFun hd _⟩,h90,h139,?_,?_,?_,?_,fun _ _ => rfl,fun _ => hz⟩
  · simp [h84,h.answerAddr]
  · simp [h85,h.priceAddr]
  · simp [h86,h.tripleAddr]
  · intro j hj; omega

theorem scanLoad (old : ScanReady L m raw price A i vals u) : Holding L.scratch u (loadState u) := by
  have hh := L.source_ge; have hs := L.source_end
  obtain ⟨_,_,_,_,hi,hd⟩ := load_out u (by rw [old.pricePointer]; omega)
  exact ⟨fun _ _ => congrFun hi _,fun p hp _ => hd p (by omega) (by omega) (by omega) (by omega)⟩

theorem scanValueHold (s : Memory ℚ) : Holding L.scratch s (valueState s) := by
  obtain ⟨_,_,hd,hi⟩ := value_out s
  exact ⟨fun p hp => hi p (by omega),fun p hp _ => hd p (by omega)⟩

theorem scanTagHold (s : Memory ℚ) : Holding L.scratch s (loadTagState s) := by
  obtain ⟨_,hi,hd⟩ := loadTag_out s
  exact ⟨fun _ _ => congrFun hi _,fun p hp _ => hd p (by omega)⟩

/-- The raw and price words in the current live input arrays agree with the immutable
start-of-stage tapes and are really read into the two scalar registers. -/
theorem loaded_inputs (old : ScanReady L m raw price A i vals u) (j : Fin n) (hj : j.val=i)
    (hm : m.data (L.answers+i)=raw j) (hp : m.data (L.prices+i)=price j) :
    let v := loadState u
    v.data 27=raw j ∧ v.data 28=price j ∧ v.data 2=0 ∧ v.data 29=0 := by
  have lo := L.source_ge; have sr := L.source_end; have pr := L.prices_end
  have tr := L.triples_end; have rr := L.rounded_end; have ar := L.answers_end; have ji := j.isLt
  obtain ⟨r,p,z,t,_,_⟩ := load_out u (by rw [old.pricePointer]; omega)
  rw [old.minorPointer,old.data _ (by omega) (by omega) (Or.inr (by omega)),hm] at r
  rw [old.pricePointer,old.data _ (by omega) (by omega) (Or.inl (by omega)),hp] at p
  exact ⟨r,p,z,t⟩

theorem ScanReady.append {j : Fin n} (old : ScanReady L m raw price A j.val vals u)
    (q : ℚ) (hq : A q) (hr : u.data 27=raw j) (hv : u.data 29=q) (hp : u.data 28=price j) :
    ScanReady L m raw price A (j.val+1) (Function.update vals j q) (appendState u) := by
  have hh := L.source_ge; have hs := L.source_end; have ht := L.prices_end; have jj := j.isLt
  obtain ⟨r,v,p,h84,h85,h86,h90,hd,hi⟩ := append_out u (by rw [old.destPointer]; omega)
  rw [old.destPointer] at r v p h86 hd
  have frame : ScanFrame L m (appendState u) :=
    ⟨fun a ha hn => (hi a (by omega) (by omega) (by omega) (by omega)).trans (old.indices a ha hn),
      fun a ha hb outside => (hd a (by omega)).trans (old.data a ha hb outside)⟩
  refine ⟨frame,h90.trans (congrArg (·+1) old.cursor),(hi 139 (by decide) (by decide) (by decide) (by decide)).trans old.status,
    ?_,?_,?_,?_,?_,?_⟩
  · simpa [old.minorPointer,Nat.add_assoc] using h84
  · simpa [old.pricePointer,Nat.add_assoc] using h85
  · simpa [Nat.mul_add,Nat.add_assoc] using h86
  · intro a ha
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ ha) with lt | eq
    · have ne : a ≠ j := by intro he; subst a; omega
      obtain ⟨r₀,v₀,p₀⟩ := old.cells a lt
      rw [Function.update_of_ne ne]
      exact ⟨(hd _ (Or.inl (by omega))).trans r₀,(hd _ (Or.inl (by omega))).trans v₀,
        (hd _ (Or.inl (by omega))).trans p₀⟩
    · have : a=j := Fin.ext eq
      subst a
      simpa using (show PackedCell (appendState u) L.triples j.val (raw j) q (price j) from
        ⟨r.trans hr,v.trans hv,p.trans hp⟩)
  · intro a ha
    have ne : a ≠ j := by intro he; subst a; omega
    simpa [ne] using old.untouched a (by omega)
  · intro a
    by_cases he : a=j
    · simpa [he] using hq
    · simpa [he] using old.bounded a

theorem ScanReady.skip {j : Fin n} (old : ScanReady L m raw price A j.val vals u)
    (hz : A 0) (hr : u.data 27=raw j) (hv : u.data 29=0) (hp : u.data 28=price j) :
    ScanReady L m raw price A (j.val+1) vals (appendState u) := by
  have x := old.append 0 hz hr hv hp
  have zero := old.untouched j (by rfl)
  simpa [← zero] using x

theorem ScanReady.restart (old : ScanReady L m raw price A i vals u) (width : m.index 130=n) :
    ScanStopped L m (restartState u) := by
  obtain ⟨status,finished,hd,hi⟩ := restart_out u
  have w := (old.indices 130 (by decide) (by decide)).trans width
  exact ⟨⟨fun p hp hn => (hi p hn (by omega)).trans (old.indices p hp hn),fun p hp hs hr => (congrFun hd p).trans (old.data p hp hs hr)⟩,
    status,finished.trans w,(hi 130 (by decide) (by decide)).trans w⟩

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
