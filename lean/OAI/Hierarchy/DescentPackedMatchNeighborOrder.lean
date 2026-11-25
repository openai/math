import OAI.Hierarchy.DescentPackedMatchCapacities
import OAI.Hierarchy.DescentNamedGeometry

namespace OAI
/-! # Positive physical neighbor bins are ordered by first original site -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup DescentPhysicalOrder
open scoped Classical
noncomputable section
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (names : DescentSharedCableNames.Stage.Host J V k↪ℕ) (win : J×V→Fin (2^k)→Cell a)
    (next : (J×V)→Fin A.degree→Option (J×V)) (he : 0≤ε)
local notation "panel" => terrain (short:=short) A native S ready names win next
local notation "addr" => nativeAddress he A.stage
local notation "grp" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "Dest" => target A native S ready names
local notation "priorSite" => originalId W.graph.Site

def actor (h : J×V) (v : Fin A.degree) (x : Fin (2^k)) : Option W.graph.Site :=
  if ha : ∃u,next h v=some (A.pos u) ∧ A.block u=x then some ha.choose else none

theorem actor_iff (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (h : J×V) (v : Fin A.degree) (x : Fin (2^k)) (u : W.graph.Site) :
    actor A next h v x=some u ↔ next h v=some (A.pos u) ∧ A.block u=x := by
  unfold actor
  split
  · rename_i ha
    obtain ⟨src,slot⟩ := ha.choose_spec
    simp only [Option.some.injEq]
    constructor
    · rintro rfl;exact ⟨src,slot⟩
    · rintro ⟨hv,hx⟩;exact coord (Prod.ext (Option.some.inj (src.symm.trans hv)) (slot.trans hx.symm))
  · rename_i ha;simp only [reduceCtorEq,false_iff];intro hit;exact ha ⟨u,hit⟩

variable (rank : (J×V)↪ℕ) (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed rank)

include coord named in
theorem site_name_order (u v : W.graph.Site) : priorSite u<priorSite v ↔
    rank (A.pos u)*2^k+(A.block u).val<rank (A.pos v)*2^k+(A.block v).val := by
  let q := A.siteFrom rank coord
  have eqn (z) : priorSite z=(DescentPhysicalOrder.physical q z).val := (named z).trans (physical_val q z).symm
  rw [eqn,eqn]
  exact physical_lt_iff q u v

include coord named in
theorem block_order (u v : W.graph.Site) (at_ : A.pos u=A.pos v) (lt : priorSite u<priorSite v) : A.block u<A.block v := by
  have pre := (site_name_order A rank coord named u v).mp lt
  rw [at_] at pre
  exact Nat.lt_of_add_lt_add_left pre

/-- The property of the immutable, ascending old-host neighbor table used by `peerExpr`. -/
abbrev RosterSorted := ∀h j y l z,next h j=some y→next h l=some z→(j.val<l.val ↔ rank y<rank z)

private theorem step_raster {n a b x y : ℕ} (hx : x<n) (hy : y<n) : a*n+x<b*n+y ↔ a<b ∨ a=b ∧ x<y := by
  have inc {u v : ℕ} (lt : u<v) {x : ℕ} (hx : x<n) : u*n+x<v*n := calc
    _<u*n+n := Nat.add_lt_add_left hx _
    _=(u+1)*n := by rw [Nat.add_mul,Nat.one_mul]
    _≤v*n := Nat.mul_le_mul_right n lt
  rcases lt_trichotomy a b with lt|eqn|gt
  · exact iff_of_true ((inc lt hx).trans_le (Nat.le_add_right ..)) (Or.inl lt)
  · subst b;simp
  · have bad := (inc gt hy).trans_le (Nat.le_add_right (a*n) x)
    exact iff_of_false (Nat.not_lt_of_ge bad.le) (by omega)

private def placesOfActors {U C H : Type} {r D p digit k : ℕ}
    (P : Panel r D p digit) (row : U ↪ ℕ) (groupOf : U → C)
    (addressOf : C ↪ H × (ℕ × ℕ)) (hostOf : U → H) (blockOf : U → Fin r)
    (paintOf : U → Bool) (hostRank : H ↪ ℕ) (neighbor : Fin D → Option H)
    (readActor : Fin D → Fin r → Option U)
    (legal : ∀ c, (addressOf c).2 ∈ DescentHostDirectory.codes k)
    (atHost : ∀ u, (addressOf (groupOf u)).1 = hostOf u)
    (readSpec : ∀ v x u, readActor v x = some u ↔ neighbor v = some (hostOf u) ∧ blockOf u = x)
    (live : ∀ v x u, readActor v x = some u →
      (P.peerWinner v x).val = 1 + 2 * heap (addressOf (groupOf u)).2 + (paintOf u).toNat)
    (dead : ∀ v x, readActor v x = none → P.peerWinner v x = 0)
    (rowOrder : ∀ u z, row u < row z ↔
      hostRank (hostOf u) * r + (blockOf u).val < hostRank (hostOf z) * r + (blockOf z).val)
    (rosterOrder : ∀ j y l z, neighbor j = some y → neighbor l = some z →
      (j.val < l.val ↔ hostRank y < hostRank z)) : Places P row groupOf := by
  have leafAt {v x u} (hit : readActor v x = some u) :
      leaf (P.peerWinner v x).val = heap (addressOf (groupOf u)).2 := by
    rw [leaf, live v x u hit]
    cases paintOf u <;> simp; omega
  refine ⟨readActor, ?_, ?_, ?_, ?_⟩
  · intro v x
    cases hit : readActor v x with
    | none =>
      exact iff_of_false (fun nonzero => nonzero (dead v x hit)) (by simp)
    | some u =>
      refine iff_of_true ?_ rfl
      intro eqZero
      have value := live v x u hit
      rw [eqZero, Fin.val_zero] at value
      omega
  · intro v x y u z xu yz
    rw [leafAt xu, leafAt yz]
    constructor
    · intro eqKey
      have hu := ((readSpec v x u).mp xu).1
      have hz := ((readSpec v y z).mp yz).1
      have sameHost := Option.some.inj (hu.symm.trans hz)
      exact addressOf.injective (Prod.ext ((atHost u).trans (sameHost.trans (atHost z).symm))
        (heap_inj (k := k) (legal (groupOf u)) (legal (groupOf z)) eqKey))
    · intro sameGroup
      rw [sameGroup]
  · intro v x u z hit sameGroup
    have sameHost : hostOf z = hostOf u :=
      (atHost z).symm.trans ((congrArg (fun c : C => (addressOf c).1) sameGroup).trans (atHost u))
    refine ⟨blockOf z, (readSpec v (blockOf z) z).mpr ⟨?_, rfl⟩⟩
    rw [sameHost]
    exact ((readSpec v x u).mp hit).1
  · intro v x u w y z xu yz
    obtain ⟨hv, hx⟩ := (readSpec v x u).mp xu
    obtain ⟨hw, hy⟩ := (readSpec w y z).mp yz
    have forward := rosterOrder v (hostOf u) w (hostOf z) hv hw
    have backward := rosterOrder w (hostOf z) v (hostOf u) hw hv
    rw [rowOrder u z, hx, hy,
      step_raster (a := hostRank (hostOf u)) (b := hostRank (hostOf z)) x.isLt y.isLt,
      step_raster (a := v.val) (b := w.val) x.isLt y.isLt]
    omega

variable (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀ u : W.graph.Site, (win (A.pos u) (A.block u)).val =
      1 + 2 * heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2 + (scanColorAt he A.stage u).toNat)

include coord named fit winner in
def places (sorted : RosterSorted A next rank) (h : J×V) : Places (panel h) priorSite grp := by
  have peek (v : Fin A.degree) (x : Fin (2^k)) : (panel h).peerWinner v x =
      (next h v).elim 0 (fun h' => (panel h').winner x) := rfl
  refine placesOfActors (U := W.graph.Site) (C := ScanColonies he A.stage) (H := J × V)
    (r := 2^k) (D := A.degree) (p := 2*A.cap) (digit := short) (k := k)
    (panel h) priorSite grp (addr) A.pos A.block (color) rank (next h) (actor A next h)
    ?_ (source_host A he) (actor_iff A next coord h) ?_ ?_ (site_name_order A rank coord named) (sorted h)
  · intro c
    exact (Finset.mem_product.mp (Finset.mem_product.mp (nativeAddress_legal he A.stage c)).2).1
  · intro v x u found
    obtain ⟨host, block⟩ := (actor_iff A next coord h v x u).mp found
    simp only [peek, host, Option.elim_some, ←block]
    exact (real_winner (short:=short) A native S ready names win next u (fit u)).trans (winner u)
  · intro v x absent
    rw [peek v x]
    cases selected : next h v with
    | none => rfl
    | some dst =>
      have vacant : ¬ ∃ u, A.pos u = dst ∧ A.block u = x := by
        rintro ⟨u, atHost, atBlock⟩
        have found := (actor_iff A next coord h v x u).mpr ⟨selected.trans (congrArg some atHost.symm),atBlock⟩
        rw [absent] at found
        contradiction
      exact empty_winner (short:=short) A native S ready names win next dst x vacant

private theorem named_first {U C : Type*} [Fintype C] (row : U↪ℕ) (g : U→C) (surj : Function.Surjective g) :
    let rank:=DescentPhysicalOrder.first row g surj
    let fresh:=DescentPhysicalOrder.home rank g
    let cover:=DescentPhysicalOrder.home_surjective rank surj
    ∀c d,PositiveAperture.rank c<PositiveAperture.rank d ↔ DescentPhysicalOrder.first row fresh cover c<DescentPhysicalOrder.first row fresh cover d := by
  intro r fresh cover
  have eqn (c : C) : DescentPhysicalOrder.first row fresh cover (rename r c)=r c := by
    apply Nat.le_antisymm
    · obtain ⟨u,hu,where_⟩ := first_at row g surj c
      have key : fresh u=rename r c := congrArg (rename r) hu
      calc
        DescentPhysicalOrder.first row fresh cover (rename r c) =
            DescentPhysicalOrder.first row fresh cover (fresh u) :=
          congrArg (DescentPhysicalOrder.first row fresh cover) key.symm
        _ ≤ row u := first_le row fresh cover u
        _ = r c := where_
    · obtain ⟨u,hu,where_⟩ := first_at row fresh cover (rename r c)
      have group : g u=c := (rename r).injective hu
      calc
        r c = r (g u) := congrArg r group.symm
        _ ≤ row u := first_le row g surj u
        _ = DescentPhysicalOrder.first row fresh cover (rename r c) := where_
  intro x y
  obtain ⟨c,rfl⟩ := (rename r).surjective x
  obtain ⟨d,rfl⟩ := (rename r).surjective y
  simp only [eqn,PositiveAperture.rank,code_rename]
  exact physical_lt_iff r c d

theorem group_order (c d : ScanColonies he A.stage) : PositiveAperture.rank c<PositiveAperture.rank d ↔
    DescentPhysicalOrder.first priorSite grp (scanHomeAt_surjective he A.stage) c <
      DescentPhysicalOrder.first priorSite grp (scanHomeAt_surjective he A.stage) d := by
  let T := A.stage
  let μ := (DescentKernelHistory.BitDescription.scannedRows he T).μ
  let block := DescentKernelHistory.BitDescription.scanBlocks T μ
  let mass := W.siteUnits T.hub T.records T.wire 256 T.hist
  let cap := T.wire*(T.z*G.b)*T.cap
  let gap := DescentHostDegree.gap T.Δ
  let exp := DescentHostDegree.packExponent 20 T.Δ
  let load := blockMass W.graph T.pos block mass
  have small : ∀v x,load v x≤cap :=
    small_reindexed W.graph T.pos T.block mass T.small (DescentColonies.multiplier T.fieldBits μ)
  let g : W.graph.Site→ScanColonies he T := rawColony W.graph cap T.near gap exp load small T.pos block
  have onto : Function.Surjective g :=
    rawColony_surjective W.graph cap T.near gap exp load small T.pos block
  exact named_first priorSite g onto c d


end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
