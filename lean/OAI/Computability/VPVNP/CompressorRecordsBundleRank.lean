import OAI.Computability.VPVNP.CompressorRecordSlots
import OAI.Computability.VPVNP.SlotBundleNumbering

/-!
# Ranks of the CD pieces and the old thick wires in an absolute bundle

Appendix E collects two bounded lists at each packed bundle. The old arc label
distinguishes parallel wires. A CD piece is ranked by its old arc after
discarding the residual lane. A thick wire is ranked by its color and slot.
Translating either list to role-A lane zero preserves these comparisons, so
the native unsigned rank scan computes the numbers used in the shrinking step.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleRank

open Compression Compression.PackingData Slots

variable {V H Tag L : Type} {d c N J : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)

/-- Numeric key of an absolute CD occurrence, independent of its residual lane. -/
def motifKey (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (m : P.Motif) :
    Fin (N * (J * (d * (2 ^ c * d)))) :=
  P.baseMotifIndex vertices tags (P.baseMotif m)

/-- Numeric key in the old thick-wire concatenation, in outgoing numbering. -/
def thickKey (a : P.ThickWire) : Fin (2 ^ c * d) :=
  finProdFinEquiv (bitWordFinEquiv c a.1.2.1, P.slotLabel a.1.2.2)

theorem thickKey_val (a : P.ThickWire) :
    (thickKey P a).val = (bitWordFinEquiv c a.1.2.1).val * d + (P.slotLabel a.1.2.2).val := by
  change _ + d * _ = _
  ring

theorem motifKey_val (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (m : P.Motif) :
    (motifKey P vertices tags m).val =
      ((((vertices m.1.1.1.1).val * J + (tags m.1.1.1.2.1).val) * d + m.1.1.2.val) *
        2 ^ c + (bitWordFinEquiv c m.1.2.1).val) * d + (P.slotLabel m.1.2.2).val := by
  change (((_ + d * _) + (2 ^ c * d) * _) + (d * (2 ^ c * d)) * _) + (J * (d * (2 ^ c * d))) * _ = _
  dsimp only [baseMotif, translateMotif, translateArc, translateSite]
  ring

private theorem row_length {E S : Type*} [Fintype E] [DecidableEq E] [DecidableEq S]
    {port : E → S} {b : S} (r : IncidentRow port b) :
    r.ids.length = Fintype.card {e // port e = b} := by
  rw [← List.toFinset_card_of_nodup r.nodup, Fintype.card_subtype]
  congr 1
  ext e
  simp [r.complete]

private theorem count_rank {E S : Type*} [Fintype E] [DecidableEq E] [DecidableEq S]
    {port : E → S} {b : S} (r : IncidentRow port b) {n k : ℕ} (key : E → Fin k)
    (num : {a // port a = b} ≃ Fin n)
    (hlt : ∀ x y, num x < num y ↔ key x.1 < key y.1) (a : {e // port e = b}) :
    (num a).val = r.ids.countP (fun e ↦ decide (key e < key a.1)) := by
  let lower := num.subtypeEquiv (p := fun x ↦ key x.1 < key a.1)
    (q := fun i ↦ i.val < (num a).val) (fun x ↦ (hlt x a).symm)
  let ids := r.ids.toFinset.filter (fun e ↦ key e < key a.1)
  let members : {x : {e // port e = b} // key x.1 < key a.1} ≃ ids := {
    toFun := fun x ↦ ⟨x.1.1, Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr ((r.complete _).mpr x.1.2), x.2⟩⟩
    invFun := fun x ↦ ⟨⟨x.1, (r.complete _).mp (List.mem_toFinset.mp (Finset.mem_filter.mp x.2).1)⟩,
      (Finset.mem_filter.mp x.2).2⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }
  rw [← Fintype.card_fin_lt_of_le (num a).isLt.le, ← Fintype.card_congr lower,
    Fintype.card_congr members, Fintype.card_coe]
  exact r.nodup.card_eq_countP

variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]

theorem motifRow_length (hc : 2 ≤ c) (b : Site V Tag L × Fin d) (r : IncidentRow P.bundle b) :
    r.ids.length = 3 * (2 ^ c * d) / 4 := by
  classical
  exact (row_length r).trans (P.card_motifs_bundle hc b)

theorem thickRow_length (hc : 2 ≤ c) (b : Site V Tag L × Fin d)
    (r : IncidentRow (fun e : P.ThickWire ↦ e.1.1) b) :
    r.ids.length = 2 ^ c * d / 4 := by
  classical
  exact (row_length r).trans (P.card_thick_fiber hc b)

/-- The piece numbers of Appendix C compare by the relative keys even at an
arbitrary absolute bundle. Transport back uses the lane of role A. -/
theorem sortedBundle_lt (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (hc : 2 ≤ c)
    (b : Site V Tag L × Fin d) (x y : P.MotifFiber b) :
    P.sortedBundleNumbering vertices tags hc b x < P.sortedBundleNumbering vertices tags hc b y ↔
      motifKey P vertices tags x.1 < motifKey P vertices tags y.1 := by
  let z : Site V Tag L × Fin d := ((b.1.1, b.1.2.1, 0), b.2)
  let toZero (u : P.MotifFiber b) : P.MotifFiber z :=
    ⟨P.translateMotif u.1 (-b.1.2.2), by simp [z, u.2, translateSite]⟩
  let key := fun u : P.MotifFiber z ↦ motifKey P vertices tags u.1
  let := LinearOrder.lift' key (P.motifFiberIndex_injective vertices tags z)
  let e := (Fintype.orderIsoFinOfCardEq (P.MotifFiber z) (P.card_motifs_bundle hc z)).symm
  change e (toZero x) < e (toZero y) ↔ _
  rw [e.lt_iff_lt]
  change motifKey P vertices tags (P.translateMotif x.1 _) <
    motifKey P vertices tags (P.translateMotif y.1 _) ↔ _
  simp [motifKey]

theorem sortedThick_lt (hc : 2 ≤ c) (b : Site V Tag L × Fin d) (x y : P.ThickFiber b) :
    P.sortedThickNumbering hc b x < P.sortedThickNumbering hc b y ↔ thickKey P x.1 < thickKey P y.1 := by
  let z : Site V Tag L × Fin d := ((b.1.1, b.1.2.1, 0), b.2)
  let toZero (u : P.ThickFiber b) : P.ThickFiber z :=
    ⟨P.translateThickWire u.1 (-b.1.2.2), by
      change (translateSite u.1.1.1.1 _, u.1.1.1.2) = _
      simp [z, u.2, translateSite]⟩
  let := LinearOrder.lift' (P.thickFiberIndex z) (P.thickFiberIndex_injective z)
  let e := (Fintype.orderIsoFinOfCardEq (P.ThickFiber z) (P.card_thick_fiber hc z)).symm
  change e (toZero x) < e (toZero y) ↔ _
  rw [e.lt_iff_lt]
  rfl

/-- Count smaller keys in the collected CD row to recover its piece number. -/
theorem motif_rank (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (hc : 2 ≤ c)
    (b : Site V Tag L × Fin d) (r : IncidentRow P.bundle b) (x : P.MotifFiber b) :
    (P.sortedBundleNumbering vertices tags hc b x).val =
      r.ids.countP (fun y ↦ decide (motifKey P vertices tags y < motifKey P vertices tags x.1)) := by
  classical
  exact count_rank r _ _ (sortedBundle_lt P vertices tags hc b) x

/-- Count smaller keys in the collected thick row to recover its concatenation number. -/
theorem thick_rank (hc : 2 ≤ c) (b : Site V Tag L × Fin d)
    (r : IncidentRow (fun a : P.ThickWire ↦ a.1.1) b) (x : P.ThickFiber b) :
    (P.sortedThickNumbering hc b x).val =
      r.ids.countP (fun a ↦ decide (thickKey P a < thickKey P x.1)) := by
  classical
  exact count_rank r _ _ (sortedThick_lt P hc b) x

open BurstRAM

/-- The native call ranks the pivot, writes the designated field and has a fixed
number of dispatches and probes for a row of this length. -/
def RankWrite {w : ℕ} (n : ℕ) (pub : Fin 2 → Word w) (mem : Memory w) (pivot rank : Word w) : Prop :=
  ∃ es, rankExecution n pub pivot mem es rank ∧
    after mem es = writeMemory mem (pub 1) rank ∧
    countProbes es = n + 1 ∧ es.length + 1 = 6 * n + 6

private theorem rank_write {E : Type*} {w K n : ℕ} (key : E → Fin K) (hfit : K < 2 ^ w)
    (ids : List E) (i : E) (rank : Fin n)
    (hl : ids.length = n) (hr : rank.val = ids.countP (fun e ↦ decide (key e < key i)))
    (hcap : n ≤ K) (pub : Fin 2 → Word w) (mem : Memory w)
    (hread : ∀ j : Fin ids.length, mem ((pub 0).val + j.val) = (key ids[j.val]).castLE hfit.le)
    (haddr : (pub 0).val + n ≤ 2 ^ w) :
    RankWrite n pub mem ((key i).castLE hfit.le) (Fin.ofNat _ rank.val) := by
  let word := fun e ↦ (key e).castLE hfit.le
  let row := ids.map word
  have hlen : row.length = n := (List.length_map _).trans hl
  have hmem (j : Fin row.length) : mem ((pub 0).val + j.val) = row[j.val] := by
    simpa [row, word] using hread ⟨j.val, by simpa [row] using j.isLt⟩
  have hheadroom (k : Word w) (hk : k ∈ row) : k.val + 1 < 2 ^ w := by
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hk
    exact (Nat.succ_le_of_lt (key e).isLt).trans_lt hfit
  have heq : (row.filter fun x ↦ decide (x < word i)).length = rank.val := by
    rw [← List.countP_eq_length_filter, List.countP_map, hr]
    rfl
  have run := SlotRankRAM.rank_native pub (word i) mem row hmem (hlen ▸ haddr)
    (hlen ▸ hcap.trans_lt hfit) hheadroom
  change RankWrite row.length pub mem (word i) (Fin.ofNat _ (row.filter fun x ↦ decide (x < word i)).length) at run
  rwa [hlen, heq] at run

/-- Rank and write the actual CD piece number from the bundle's unsorted row. -/
theorem motif_rank_native {w : ℕ} (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (hc : 2 ≤ c)
    (hfit : N * (J * (d * (2 ^ c * d))) < 2 ^ w) (b : Site V Tag L × Fin d)
    (r : IncidentRow P.bundle b) (x : P.MotifFiber b)
    (pub : Fin 2 → Word w) (mem : Memory w)
    (hread : ∀ j : Fin r.ids.length, mem ((pub 0).val + j.val) =
      (motifKey P vertices tags r.ids[j.val]).castLE hfit.le)
    (haddr : (pub 0).val + 3 * (2 ^ c * d) / 4 ≤ 2 ^ w) :
    RankWrite (3 * (2 ^ c * d) / 4) pub mem ((motifKey P vertices tags x.1).castLE hfit.le)
      (Fin.ofNat _ (P.sortedBundleNumbering vertices tags hc b x).val) := by
  have cap := Fintype.card_le_of_injective _ (P.motifFiberIndex_injective vertices tags b)
  rw [P.card_motifs_bundle hc b, Fintype.card_fin] at cap
  exact rank_write _ hfit _ _ _ (motifRow_length P hc b r) (motif_rank P vertices tags hc b r x)
    cap pub mem hread haddr

/-- Rank and write the actual thick wire's position in the concatenation. -/
theorem thick_rank_native {w : ℕ} (hc : 2 ≤ c) (hfit : 2 ^ c * d < 2 ^ w)
    (b : Site V Tag L × Fin d) (r : IncidentRow (fun a : P.ThickWire ↦ a.1.1) b)
    (x : P.ThickFiber b) (pub : Fin 2 → Word w) (mem : Memory w)
    (hread : ∀ j : Fin r.ids.length, mem ((pub 0).val + j.val) =
      (thickKey P r.ids[j.val]).castLE hfit.le)
    (haddr : (pub 0).val + (2 ^ c * d) / 4 ≤ 2 ^ w) :
    RankWrite (2 ^ c * d / 4) pub mem ((thickKey P x.1).castLE hfit.le)
      (Fin.ofNat _ (P.sortedThickNumbering hc b x).val) :=
  rank_write _ hfit _ _ _ (thickRow_length P hc b r) (thick_rank P hc b r x)
    (Nat.div_le_self _ _) pub mem hread haddr

end CompressorRecords.BundleRank

end VPVNP
end Computability
end OAI
