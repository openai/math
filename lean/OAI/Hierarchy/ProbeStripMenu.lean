import OAI.Hierarchy.ProbeStrip
import OAI.Hierarchy.ProbeCatalogue

namespace OAI
/-! # Actual finite packet catalogues for the two physical strip test geometries -/

namespace Hierarchy.Probe
open LinearAlgebra.SpectralBooks.ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped BigOperators Classical
noncomputable section

variable {F E A : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A] {s : ℕ} [Nonempty (Fin s)]

/-- Fixed immutable advice, uniform over all inventory values and batch sizes. The
index names retain the original demanded occurrences, including repeated pairs. -/
structure FixedMenu (F : Type*) [Field F] (edge : E→Chord s) (req : A→E)
    (box : Set (E→ℝ)) (ε tree : ℝ) (N : ℕ) where
  index : Finset {p : E→ℝ // p∈box ∧ ε≤discrepancy F edge req p}
  packet : (j : index) → Packet F edge (fun a : PositiveDemand req j.val.val => req a.val)
  margin : ℝ
  positive : 0 < margin
  wide : ∀ j, N<(packet j).width
  select : {p : E→ℝ // p∈box ∧ ε≤discrepancy F edge req p} → index
  adequate : ∀ p (a : PositiveDemand req (select p).val.val), margin ≤ p.val (req a.val)
  paid : ∀ p t (hist : Histogram (Fin (packet (select p)).terms) t),
    (∑ e, (histWidth (packet (select p)).count hist e:ℝ)*p.val e) + t*(tree*(packet (select p)).selectorBits) ≤
      t*((packet (select p)).width*((∑ a : PositiveDemand req (select p).val.val, p.val (req a.val))-margin))

def fixedMenu (edge : E→Chord s) (req : A→E) (conn : Connected edge) (box : Set (E→ℝ))
    (compact : IsCompact box) (nonneg : ∀ p∈box, ∀e,0≤p e) {ε : ℝ} (he : 0<ε)
    (tree : ℝ) (ht : 0≤tree) (N : ℕ) : FixedMenu F edge req box ε tree N := by
  classical
  apply Classical.choice
  obtain ⟨S,packet,γ,positive,wide,all⟩ := discrepancy_catalogue (F:=F) edge req conn box compact nonneg he tree ht N
  exact ⟨⟨S,packet,γ,positive,wide,fun p => (all p).choose,fun p => (all p).choose_spec.1,fun p => (all p).choose_spec.2⟩⟩

namespace FixedMenu
variable {box : Set (E→ℝ)} {ε tree : ℝ} {N : ℕ} {edge : E→Chord s} {req : A→E}
    (m : FixedMenu F edge req box ε tree N)

/-- Mixed-radix price LUT data entry. Code zero skips a passing test; a positive
word names the original precomputed packet. -/
def word {Y : Type*} (price : Y→E→ℝ) (legal : ∀u, price u∈box) (u : Y) : ℕ :=
  if failed : ε≤discrepancy F edge req (price u) then
    (Fintype.equivFin m.index (m.select ⟨price u,legal u,failed⟩)).val+1 else 0

theorem word_pass {Y : Type*} (price : Y→E→ℝ) (legal : ∀u,price u∈box) (u : Y) :
    m.word price legal u=0 ↔ discrepancy F edge req (price u)<ε := by
  by_cases failed : ε≤discrepancy F edge req (price u) <;> simp [word,failed,lt_iff_not_ge]

theorem word_spec {Y : Type*} (price : Y→E→ℝ) (legal : ∀u,price u∈box) (u : Y)
    (failed : ε≤discrepancy F edge req (price u)) :
    let p := (⟨price u,legal u,failed⟩ : {p : E→ℝ // p∈box ∧ ε≤discrepancy F edge req p})
    let j := m.select p
    m.word price legal u=(Fintype.equivFin m.index j).val+1 ∧
    (∀ a : PositiveDemand req j.val.val, m.margin≤price u (req a.val)) ∧
    ∀ t (h : Histogram (Fin (m.packet j).terms) t),
      (∑ e, (histWidth (m.packet j).count h e:ℝ)*price u e)+t*(tree*(m.packet j).selectorBits) ≤
      t*((m.packet j).width*((∑ a : PositiveDemand req j.val.val, price u (req a.val))-m.margin)) := by
  exact ⟨by simp [word,failed],m.adequate _,m.paid _⟩

end FixedMenu

end
end Hierarchy.Probe

namespace Hierarchy.AdaptiveProbe.Strip
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Classical
noncomputable section

variable {F A B : Type*} [Field F] [Fintype A] [Fintype B] {n k : ℕ}

/-- Instantiate the catalogue using the strip's printed links, ordinary payload or
signed measurements, and optional purchased chord. The rounded lookup always uses
this same finite catalogue at the given physical site order. -/
def formatMenu [SiteNaming (ColumnSite (TestColumns (steps n) 0 n) k)]
    (hk : 0<k) (d : A→LocalCommodity (TestColumns (steps n) 0 n) k)
    (buy : B→DistinctPair (TestColumns (steps n) 0 n)) (M : ℝ) (hM : 0≤M)
    (len : Fin n→ℝ) (cost : ∀ e,0≤len e ∧ len e≤1) (cap : A→ℝ)
    {ε : ℝ} (he : 0<ε) (tree : ℝ) (ht : 0≤tree) (N : ℕ) :
    let I := TestColumns (steps n) 0 n
    letI : Nonempty (ColumnWires.Role I (Fin n) (A⊕B) k) := ⟨.catalyst (column n 0) ⟨0,hk⟩⟩
    Probe.FixedMenu F (ColumnWires.wires (horizontal n) (LocalCommodity.extraEnds d buy))
      (ColumnWires.demand (I:=I) (H:=Fin n) (k:=k) (Sum.inl (α:=A) (β:=B)))
      ((fun y:A→ℝ => ColumnWires.quote (I:=I) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) '' Set.Icc 0 cap)
      ε tree N := by
  classical
  let I := TestColumns (steps n) 0 n
  letI : Nonempty (ColumnWires.Role I (Fin n) (A⊕B) k) := ⟨.catalyst (column n 0) ⟨0,hk⟩⟩
  apply Probe.fixedMenu _ _ _ _ (LocalCommodity.compact_quotes (I:=I) (B:=B) (k:=k) M len cap) _ he tree ht N
  · apply ColumnWires.connected (testBase (steps n) 0 n)
    apply test_connects
    intro x y near
    obtain ⟨e,_,ends⟩ := hosts len (fun e => (cost e).2) x y near
    exact ⟨e,ends⟩
  · rintro _ ⟨y,box,rfl⟩ r
    cases r with
    | catalyst => dsimp [ColumnWires.quote]; positivity
    | radius => exact hM
    | cross => dsimp [ColumnWires.quote]; positivity
    | horizontal e _ => exact (cost e).1
    | extra i => cases i with
      | inl a => exact box.1 a
      | inr b => exact zero_le_one

end
end Hierarchy.AdaptiveProbe.Strip

end OAI
