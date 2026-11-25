import OAI.Hierarchy.DescentPackedMatchGhosts
import OAI.Hierarchy.DescentPackedMatchPortInventory
import OAI.Hierarchy.DescentPackedInputNumber
import OAI.Hierarchy.DescentPackedLocalMatchSource

namespace OAI
/-! # The physical whole thin-item requests at each authentic occupied source -/
namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup
open scoped Classical
noncomputable section
private theorem amount_map_on {I J : Type*} (f : I→J) (old : I→ℕ) (w : J→ℕ) (xs : List I)
    (same : ∀z∈xs,w (f z)=old z) : DescentPacking.amount w (xs.map f)=DescentPacking.amount old xs := by
  unfold DescentPacking.amount
  rw [List.map_map]
  exact congrArg List.sum (List.map_congr_left (fun z hz => (same z hz : (w ∘ f) z = old z)))

private theorem packs_map_on {I J : Type*} (f : I→J) (old : I→ℕ) (w : J→ℕ) (B : ℕ) (xs : List I)
    (same : ∀z∈xs,w (f z)=old z) : thinPacks w B (xs.map f)=(thinPacks old B xs).map (List.map f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons,thinPacks,ih (fun z hz=>same z (List.mem_cons_of_mem _ hz)),thinPacks]
    cases ps : thinPacks old B xs with
    | nil => rfl
    | cons p rest =>
      have ok (z) (hz : z∈p) : w (f z)=old z := by
        apply same
        apply List.mem_cons_of_mem
        rw [←thinPacks_flatten old B xs,ps]
        simp [hz]
      simp only [List.map_cons,amount_map_on f old w p ok]
      split <;> rfl

private theorem unpack_site_ticket {width : ℕ} (z : Cell width) (key : ℕ) (side : Bool)
    (value : z.val = 1 + 2 * key + side.toNat) :
    z ≠ 0 ∧ leaf z.val = key ∧ decide (thick z.val) = side := by
  constructor
  · intro z0
    have zero : z.val = 0 := congrArg Fin.val z0
    omega
  · rw [value]
    cases side <;> constructor <;> simp [leaf, thick]; omega

private theorem member_from_site_tickets {U C H : Type} {r D p width k : ℕ}
    (panels : H → Panel r D p width) (pos : U → H) (block : U → Fin r)
    (addressOf : C ↪ H × (ℕ × ℕ)) (groupOf : U → C) (shadeOf : U → Bool)
    (legal : ∀ c, (addressOf c).2 ∈ DescentHostDirectory.codes k)
    (hostAt : ∀ u, (addressOf (groupOf u)).1 = pos u)
    (ticket : ∀ u, ((panels (pos u)).winner (block u)).val =
      1 + 2 * heap (addressOf (groupOf u)).2 + (shadeOf u).toNat)
    (vacant : ∀ h x, (¬ ∃ u, pos u = h ∧ block u = x) → (panels h).winner x = 0)
    (c : C) (shade : Bool) (x : Fin r) :
    x ∈ sites (panels (addressOf c).1) (heap (addressOf c).2) shade ↔
      ∃ u, groupOf u = c ∧ shadeOf u = shade ∧ block u = x := by
  classical
  have readAt (u : U) := unpack_site_ticket ((panels (pos u)).winner (block u))
    (heap (addressOf (groupOf u)).2) (shadeOf u) (ticket u)
  simp only [sites, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨active, keyAt, shadeAt⟩
    by_cases present : ∃ u, pos u = (addressOf c).1 ∧ block u = x
    · obtain ⟨u, hostEq, blockEq⟩ := present
      have seen := readAt u
      rw [hostEq, blockEq] at seen
      have keyEq := heap_inj (k := k) (legal (groupOf u)) (legal c) (seen.2.1.symm.trans keyAt)
      exact ⟨u, addressOf.injective (Prod.ext ((hostAt u).trans hostEq) keyEq),
        seen.2.2.symm.trans shadeAt, blockEq⟩
    · exact (active (vacant _ _ present)).elim
  · rintro ⟨u, rfl, rfl, rfl⟩
    rw [hostAt u]
    exact readAt u

namespace Stage
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (names : DescentSharedCableNames.Stage.Host J V k↪ℕ) (win : J×V→Fin (2^k)→Cell a)
    (next : (J×V)→Fin A.degree→Option (J×V)) (he : 0≤ε)
local notation "panel" => terrain (short:=short) A native S ready names win next
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "T" => nativeTraffic W.graph W.core home
local notation "Dest" => target A native S ready names
variable (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀ u : W.graph.Site, (win (A.pos u) (A.block u)).val =
      1 + 2 * heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2 +
        (scanColorAt he A.stage u).toNat)
include fit winner

theorem site_member (c : ScanColonies he A.stage) (shade : Bool) (x : Fin (2^k)) :
    x∈sites (panel (addr c).1) (heap (addr c).2) shade ↔
      ∃u,home u=c ∧ color u=shade ∧ A.block u=x := by
  refine member_from_site_tickets (U := W.graph.Site) (C := ScanColonies he A.stage)
    (H := J × V) (r := 2^k) (D := A.degree) (p := 2*A.cap) (width := short) (k := k)
    (panel) A.pos A.block (addr) (home) (color) ?_ (source_host A he)
    ?_ (empty_winner (short := short) (a := a) A native S ready names win next) c shade x
  · intro j
    exact (Finset.mem_product.mp (Finset.mem_product.mp (nativeAddress_legal he A.stage j)).2).1
  · intro u
    exact (real_winner (short := short) (a := a) A native S ready names win next u (fit u)).trans
      (winner u)

/-- The compact ordering of old sites on a single host is increasing old block.
It is checked on the actually named input graph before the selector runs. -/
theorem source_sites (order : ∀u v,A.pos u=A.pos v→ originalId W.graph.Site u<originalId W.graph.Site v→A.block u<A.block v)
    (c : ScanColonies he A.stage) (shade : Bool) :
    sites (panel (addr c).1) (heap (addr c).2) shade=(colorSites home color shade c).map A.block := by
  let l := sites (panel (addr c).1) (heap (addr c).2) shade
  let t := colorSites home color shade c
  have left : l.Pairwise (·<·) := (List.pairwise_ofFn.mpr (fun i j h=>h) : (List.finRange (2^k)).Pairwise (·<·)).filter _
  have place {u} (hu : u∈t) : A.pos u=(addr c).1 := by
    have hc := (mem_colorSites home color shade c u).mp hu
    rw [←source_host A he u,hc.1]
  have right : (t.map A.block).Pairwise (·<·) := by
    apply List.pairwise_map.mpr
    exact (colorSites_ordered home color shade c).imp_of_mem (fun hu hv lt=>order _ _ ((place hu).trans (place hv).symm) lt)
  apply List.Perm.eq_of_pairwise (fun _ _ _ _ h₁ h₂=>(asymm h₁ h₂).elim) left right
  apply (List.perm_ext_iff_of_nodup (left.imp (fun h=>h.ne)) (right.imp (fun h=>h.ne))).mpr
  intro x
  have member := site_member (short:=short) A native S ready names win next he fit winner c shade x
  constructor
  · intro hx
    obtain ⟨u, atHome, paint, block⟩ := member.mp hx
    exact List.mem_map.mpr ⟨u,(mem_colorSites home color shade c u).mpr ⟨atHome,paint⟩,block⟩
  · intro hx
    obtain ⟨u, hu, block⟩ := List.mem_map.mp hx
    obtain ⟨atHome, paint⟩ := (mem_colorSites home color shade c u).mp hu
    exact member.mpr ⟨u,atHome,paint,block⟩

theorem physical_packs (s : Shape) (coord : Function.Injective (fun z=>(A.pos z,A.block z)))
    (order : ∀u v,A.pos u=A.pos v→ originalId W.graph.Site u<originalId W.graph.Site v→A.block u<A.block v)
    (df : A.degree<2^short) (room : ∀h x (e : PackedCensus.Out W A.pos A.block h x),bin (panel h) (Dest (h,x) e) x<s.bins)
    (c : ScanColonies he A.stage) :
    packs (panel (addr c).1) s.bins A.cap (heap (addr c).2)=
      (thinPacks (live T) A.cap (thinList home color c)).map (List.map A.block) := by
  let xs : List W.graph.Site := thinList home color c
  let w : Fin (2^k)→ℕ := countAt (panel (addr c).1) s.bins
  have same (z : W.graph.Site) (hz : z∈xs) : w (A.block z)=live T z := by
    have homeAt := (mem_colorSites home color false c z).mp hz
    have place : A.pos z=(addr c).1 := by rw [←source_host A he z,homeAt.1]
    simpa only [w,place] using source_mass A native S ready names win next home coord s.bins df room z
  have blocks : sites (panel (addr c).1) (heap (addr c).2) false=xs.map A.block :=
    source_sites A native S ready names win next he fit winner order c false
  exact (congrArg (thinPacks w A.cap) blocks).trans (packs_map_on A.block (live T) w A.cap xs same)

theorem pack_needs (s : Shape) (coord : Function.Injective (fun z=>(A.pos z,A.block z)))
    (order : ∀u v,A.pos u=A.pos v→ originalId W.graph.Site u<originalId W.graph.Site v→A.block u<A.block v)
    (df : A.degree<2^short) (room : ∀h x (e : PackedCensus.Out W A.pos A.block h x),bin (panel h) (Dest (h,x) e) x<s.bins)
    (c : ScanColonies he A.stage) (j : Fin s.packs) :
    (((packs (panel (addr c).1) s.bins A.cap (heap (addr c).2))[j.val]?).map (DescentPacking.amount (countAt (panel (addr c).1) s.bins))).getD 0=
      PackedLocalMatch.needs (DescentPacking.amount (live T)) (thinPacks (live T) A.cap (thinList home color c)) j := by
  let xs : List W.graph.Site := thinList home color c
  let w : Fin (2^k)→ℕ := countAt (panel (addr c).1) s.bins
  have same (z : W.graph.Site) (hz : z∈xs) : w (A.block z)=live T z := by
    have homeAt := (mem_colorSites home color false c z).mp hz
    have place : A.pos z=(addr c).1 := by rw [←source_host A he z,homeAt.1]
    simpa only [w,place] using source_mass A native S ready names win next home coord s.bins df room z
  let qs : List (List W.graph.Site) := thinPacks (live T) A.cap xs
  have physical : packs (panel (addr c).1) s.bins A.cap (heap (addr c).2)=qs.map (List.map A.block) :=
    physical_packs A native S ready names win next he fit winner s coord order df room c
  have selected := congrArg (fun vs : List (List (Fin (2^k))) =>
    (vs[j.val]?.map (DescentPacking.amount w)).getD 0) physical
  refine selected.trans ?_
  change (((qs.map (List.map A.block))[j.val]?).map (DescentPacking.amount w)).getD 0 =
    (qs[j.val]?.map (DescentPacking.amount (live T))).getD 0
  rw [List.getElem?_map]
  cases found : qs[j.val]? with
  | none => rfl
  | some part =>
    change DescentPacking.amount w (part.map A.block) = DescentPacking.amount (live T) part
    apply amount_map_on A.block (live T) w part
    intro z hz
    apply same z
    have hpart : part∈qs := List.mem_of_getElem? found
    have hzflat : z∈qs.flatten := List.mem_flatten.mpr ⟨part,hpart,hz⟩
    exact (thinPacks_flatten (live T) A.cap xs) ▸ hzflat


end Stage
end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI
