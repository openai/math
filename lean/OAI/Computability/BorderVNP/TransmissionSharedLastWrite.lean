import OAI.Computability.BorderVNP.TransmissionLastWriteLayout
import OAI.Computability.BorderVNP.TransmissionScheduled
import OAI.Computability.BorderVNP.CubeSharedRowsLoad

/-! # Last writes to the two ordered banks of each shared symbol pair -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.SharedRows

open RoutingISA RoutingISA.Transmission VPVNP.BurstRAM
open private square_key from OAI.Computability.BorderVNP.CubeSharedRowsLoad
open private addFieldVal cursorVal from OAI.Computability.BorderVNP.TransmissionScheduled

variable {w : ℕ}

/-- The physical ranges carry the shared writer's ordered endpoint banks, with each
declared shared width bounded by their common stride. -/
structure Layout.LastWriteFields (l : Layout) (rows : ℕ → Range w) : Prop where
  /-- First endpoint of the original pair. -/
  first : ∀ t < l.groups, ∀ s < t, (rows (l.rowIndex s t)).dstA.val = l.view s t
  /-- Second endpoint in the reverse bank. -/
  second : ∀ t < l.groups, ∀ s < t, (rows (l.rowIndex s t)).dstB.val = l.view t s
  /-- The stride covers the complete shared payload, including selectors. -/
  width : ∀ t < l.groups, ∀ s < t, (rows (l.rowIndex s t)).width.val ≤ l.stride

/-- All shared descriptor columns survive the scheduler. This applies directly to
the emitted record words after the count update and also to the image before it. -/
theorem Layout.shared_range_fields (l : Layout) {tab : TableLayout} {row : ℕ → TableRow}
    {src before : ℕ → ℕ} {m : Memory w} (image : tab.Image row before (readings m))
    (al : tab.Allocated w) (recordBase : tab.records = l.records)
    (count : tab.count = l.dataCount + l.groups.choose 2)
    (records : ∀ t < l.groups, ∀ s < t, ∀ j : Fin 7,
      before (l.address (l.rowIndex s t)+j.val) = l.row src s t j)
    {s t : ℕ} (hs : s < t) (ht : t < l.groups) :
    let r := tableRange tab m (l.rowIndex s t)
    r.kind.val = 0 ∧ r.teamA.val = src (l.owners+s) ∧ r.teamB.val = src (l.owners+t) ∧
      r.width.val = l.selectors+l.crossWidth src s t ∧ r.source.val = 0 ∧
      r.dstA.val = l.view s t ∧ r.dstB.val = l.view t s := by
  let i := l.rowIndex s t
  have hi : i < tab.count := count ▸ l.index_lt hs ht
  let base := cursorAt (Fin.ofNat _ tab.records : Word w) 7 i
  have cap := al.address (tab.contains_record hi (by decide : 6 < 7))
  have bv : base.val = tab.records+i*7 := cursorVal tab.records 7 i (by omega)
  have column (j : Fin 7) : readings m (base + Fin.ofNat _ j.val).val = l.row src s t j := by
    have inside := tab.contains_record hi j.isLt
    rw [addFieldVal _ _ (by have := j.isLt; omega), bv,
      show tab.records+i*7+j.val = 7*i+tab.records+j.val by omega,
      image.outside _ (al.separate .records .widths _ (by decide) inside)
        (al.separate .records .ordinals _ (by decide) inside)
        (al.separate .records .offsets _ (by decide) inside)
        (al.separate .records .used _ (by decide) inside)]
    simpa only [Layout.address,← recordBase,Nat.add_comm (7*i) tab.records] using records t ht s hs j
  refine ⟨?_,column 1,column 2,column 3,column 4,column 5,column 6⟩
  change readings m base.val = 0
  simpa [Layout.row] using column 0

/-- The actual scheduler image and the shared emitter's exact seven-word rows supply
all fields needed for last-writer reconstruction. -/
theorem Layout.LastWriteFields.of_scheduled {l : Layout} {tab : TableLayout} {row : ℕ → TableRow}
    {src before : ℕ → ℕ} {m : Memory w} (image : tab.Image row before (readings m))
    (al : tab.Allocated w) (fit : l.Fits w src) (recordBase : tab.records = l.records)
    (count : tab.count = l.dataCount + l.groups.choose 2)
    (records : ∀ t < l.groups, ∀ s < t, ∀ j : Fin 7,
      before (l.address (l.rowIndex s t)+j.val) = l.row src s t j) :
    l.LastWriteFields (tableRange tab m) := by
  have cols t ht s hs := l.shared_range_fields image al recordBase count records (s := s) (t := t) hs ht
  exact ⟨fun t ht s hs => (cols t ht s hs).2.2.2.2.2.1,
    fun t ht s hs => (cols t ht s hs).2.2.2.2.2.2,
    fun t ht s hs => (cols t ht s hs).2.2.2.1 ▸ fit.widthFit t ht s hs⟩

/-- The shared pass's completed image supplies all recorded columns for the scheduler. -/
theorem Layout.LastWriteFields.of_image {l : Layout} {tab : TableLayout} {row : ℕ → TableRow}
    {src before : ℕ → ℕ} {m : Memory w} (shared : l.Image src (l.dataCount+l.groups.choose 2) before)
    (image : tab.Image row before (readings m)) (al : tab.Allocated w) (fit : l.Fits w src)
    (recordBase : tab.records = l.records) (count : tab.count = l.dataCount+l.groups.choose 2) :
    l.LastWriteFields (tableRange tab m) :=
  of_scheduled image al fit recordBase count (fun t ht s hs => shared.rows t ht s hs (l.index_lt hs ht))

private theorem index_covered (l : Layout) {i : ℕ} (hi : l.dataCount ≤ i)
    (endAt : i < l.dataCount+l.groups.choose 2) : ∃ t < l.groups, ∃ s < t, i = l.rowIndex s t := by
  have find (n : ℕ) (lt : i < l.dataCount+n.choose 2) : ∃ t < n, ∃ s < t, i = l.rowIndex s t := by
    induction n with
    | zero => simp at lt; omega
    | succ n ih =>
      by_cases prior : i < l.dataCount+n.choose 2
      · obtain ⟨t,ht,s,hs,eq⟩ := ih prior
        exact ⟨t,ht.trans n.lt_succ_self,s,hs,eq⟩
      · rw [choose_succ_two] at lt
        exact ⟨n,n.lt_succ_self,i-(l.dataCount+n.choose 2),by omega,by dsimp [Layout.rowIndex]; omega⟩
  exact find l.groups endAt

private theorem key_inj {g u v x y : ℕ} (hv : v < g) (hy : y < g) (eq : u*g+v = x*g+y) :
    u = x ∧ v = y := by
  have hdiv := congrArg (· / g) eq
  rw [Nat.mul_comm u g,Nat.mul_comm x g] at hdiv
  have hmod := congrArg (· % g) eq
  have hg : 0 < g := Nat.zero_lt_of_lt hv
  simpa only [Nat.mul_add_div hg, Nat.div_eq_of_lt hv,Nat.div_eq_of_lt hy,Nat.add_zero,
    Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hv,Nat.mod_eq_of_lt hy] using And.intro hdiv hmod

private theorem destination_key {l : Layout} {rows : ℕ → Range w} (fields : l.LastWriteFields rows)
    (team : Word w) {s t : ℕ} (hs : s < t) (ht : t < l.groups) {mode : Role} {d : Reg}
    (hd : d ∈ mode.destinations) : ∃ k < l.groups^2,
    ((rows (l.rowIndex s t)).bank team d).val = l.banks+l.stride*k ∧
      (k = s*l.groups+t ∨ k = t*l.groups+s) := by
  have cases : d = 13 ∨ d = 14 := by cases mode <;> simp_all [Role.destinations]
  rcases cases with rfl | rfl
  · exact ⟨_,square_key (hs.trans ht) ht,fields.first t ht s hs,Or.inl rfl⟩
  · exact ⟨_,square_key ht (hs.trans ht),fields.second t ht s hs,Or.inr rfl⟩

private theorem ordered_span {l : Layout} {a b : ℕ} (h : a < b) :
    l.banks+l.stride*a+l.stride ≤ l.banks+l.stride*b := by
  have n := Nat.mul_le_mul_left l.stride h
  rw [Nat.mul_succ] at n
  omega

/-- Every selected destination of the pair has this bit as its last writer. This applies
to both local shared stores and the single store of either remote receiving role. -/
theorem Layout.shared_lastWrite {l : Layout} {rows : ℕ → Range w} (fields : l.LastWriteFields rows)
    (room : l.banks+l.stride*l.groups^2 ≤ 2^w) (team : Word w) {s t j : ℕ}
    (hs : s < t) (ht : t < l.groups) {mode : Role}
    (sel : (rows (l.rowIndex s t)).selected team = some (some mode))
    (hj : j < (rows (l.rowIndex s t)).width.val) (d : Reg) (hd : d ∈ mode.destinations) :
    LastWrite rows team (l.dataCount+l.groups.choose 2) (l.rowIndex s t) mode j
      (((rows (l.rowIndex s t)).bank team d).val+j) := by
  obtain ⟨k,hk,bk,orient⟩ := destination_key fields team hs ht hd
  have width := fields.width t ht s hs
  apply LastWrite.of_intervals (l.index_lt hs ht) hj sel d hd rfl
  · intro e he
    obtain ⟨v,hv,be,_⟩ := destination_key fields team hs ht he
    have before := ordered_span (l := l) hv
    omega
  · intro e he
    obtain ⟨v,hv,be,_⟩ := destination_key fields team hs ht he
    rcases lt_trichotomy v k with h | h | h
    · have before := ordered_span (l := l) h
      omega
    · rw [be,bk,h]
      exact Or.inl rfl
    · have before := ordered_span (l := l) h
      omega
  · intro n hin hn next hnsel e he
    have begins : l.dataCount ≤ l.rowIndex s t := by dsimp [Layout.rowIndex]; omega
    obtain ⟨t',ht',s',hs',rfl⟩ := index_covered l (begins.trans hin.le) hn
    obtain ⟨v,hv,be,orient'⟩ := destination_key fields team hs' ht' he
    have w' := fields.width t' ht' s' hs'
    have endFit := ordered_span (l := l) hv
    refine ⟨by omega,?_⟩
    have ne : k ≠ v := by
      intro eq
      rcases orient with hk' | hk' <;> rcases orient' with hv' | hv' <;> rw [hk',hv'] at eq
      · obtain ⟨rfl,rfl⟩ := key_inj ht ht' eq
        exact Nat.lt_irrefl _ hin
      · have ⟨_,_⟩ := key_inj ht (hs'.trans ht') eq
        omega
      · have ⟨_,_⟩ := key_inj (hs.trans ht) ht' eq
        omega
      · obtain ⟨rfl,rfl⟩ := key_inj (hs.trans ht) (hs'.trans ht') eq
        exact Nat.lt_irrefl _ hin
    rcases Nat.lt_or_gt_of_ne ne with h | h <;> have := ordered_span (l := l) h <;> omega


/-- The first endpoint's actual store is final at the forward ordered view. -/
theorem Layout.shared_lastWrite_A {l : Layout} {rows : ℕ → Range w} (fields : l.LastWriteFields rows)
    (room : l.banks+l.stride*l.groups^2 ≤ 2^w) (team : Word w) {s t j : ℕ}
    (hs : s < t) (ht : t < l.groups) {mode : Role}
    (sel : (rows (l.rowIndex s t)).selected team = some (some mode))
    (hj : j < (rows (l.rowIndex s t)).width.val) (writesA : 13 ∈ mode.destinations) :
    LastWrite rows team (l.dataCount+l.groups.choose 2) (l.rowIndex s t) mode j (l.view s t+j) := by
  rw [← fields.first t ht s hs]
  exact shared_lastWrite fields room team hs ht sel hj 13 writesA

/-- The second endpoint's actual store is final at the reverse ordered view. -/
theorem Layout.shared_lastWrite_B {l : Layout} {rows : ℕ → Range w} (fields : l.LastWriteFields rows)
    (room : l.banks+l.stride*l.groups^2 ≤ 2^w) (team : Word w) {s t j : ℕ}
    (hs : s < t) (ht : t < l.groups) {mode : Role}
    (sel : (rows (l.rowIndex s t)).selected team = some (some mode))
    (hj : j < (rows (l.rowIndex s t)).width.val) (writesB : 14 ∈ mode.destinations) :
    LastWrite rows team (l.dataCount+l.groups.choose 2) (l.rowIndex s t) mode j (l.view t s+j) := by
  rw [← fields.second t ht s hs]
  exact shared_lastWrite fields room team hs ht sel hj 14 writesB

end Cube.SharedRows

end BorderVNP
end Computability
end OAI
