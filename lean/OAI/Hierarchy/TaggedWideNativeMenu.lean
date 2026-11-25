import OAI.Hierarchy.TaggedWideActiveLedger
import OAI.Hierarchy.TaggedWideActivePartition
import OAI.Hierarchy.TaggedWideReportedPrice
import OAI.Hierarchy.ProbeFixedLinkMenu
import OAI.Hierarchy.TaggedDyadicBanks

namespace OAI
/-! # A resolution for the actual padded CPU tape, common to all selectors and wide parents -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage CoreBoard ReportSockets CatalogueRows ProtocolRAMEmit
open Tagged TaggedShorterBudget Tagged.WideStack ProtocolRAMReportedPorts
open scoped Classical BigOperators
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ)

local notation "jobs" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel

/-- The common paid class bounds refer to all native rows at all heights,
selectors and fixed dyadic width classes. Inactive original slots carry zero units. -/
def PhysicalCounts (u : ℝ→ℝ) (A δ ξ : ℝ) (m : ℕ) : Prop :=
  ∀ a∈Set.Icc 1 A,∀ {h w R groups : ℕ} (π : Equiv.Perm (Fin (2^h)))
      (b : Board) (marks : Marks h v.W k jobs) (order : Fin b.coreRows≃Edges v.sampler h (2^v.W) k)
      (size : jobs*(PurchaseFrozen.count h (2^v.W) k*PurchaseFrozen.paths h v.sampler.degree (publicTiles k v.W-1))=b.boughtRows)
      (raw : Fin b.rows→ProtocolRAMEmit.Row) (bits : Catalogue v.sampler π (publicTiles k v.W-1) marks→ℕ),
      let ord:=b.ordinal v.sampler π (publicTiles k v.W-1) marks order size
      ∀(rec : Alignment b v.sampler π (publicTiles k v.W-1) marks v.radius raw (fun i=>(raw i).width) ord),
      (∀e,(raw (ord e)).width=bits e) →
      TermBudget p q Q Λ (2^h) w v.radius (∑_j:Columns h (2^v.W)×Fin k,R)
        (scaleOf v.sampler π (publicTiles k v.W-1) marks) (fun e=>(lenCode v.sampler π (publicTiles k v.W-1) marks v.radius e:ℝ))
        (fun e=>(bits e:ℝ)/w) →
      (rec.geometry w R).links.Keep (2^h) →
      ∀γ, ((∑g:Fin groups, count (atScale (b.transport order) (fun _=>0) 0 raw) w m γ g.val:ℕ):ℝ)
        ≤typeFraction u δ ξ a (v.W,γ)*(2^h:ℕ)

/-- Compare the real recorded cross-layer flow with the uniform shortening
menu, including unpurchased dormant ordinals and zero-width settled rows. -/
theorem printed_menu {A ε δ η ξ : ℝ} {u : ℝ→ℝ}
    (price : Choice u A ε p q Q σ Λ δ η ξ) :
    ∃m:ℕ,v.PhysicalCounts u A δ ξ m := by
  obtain ⟨m,resolution⟩:=reported_menu price (Nat.cast_nonneg v.rowFactor)
  refine ⟨m, ?_⟩
  intro a ha h w R groups π b marks order size raw bits
  let ord := b.ordinal v.sampler π (publicTiles k v.W-1) marks order size
  dsimp only
  intro rec read paid keep γ
  let G:=rec.geometry w R
  let t:=activeScale raw G.scale
  let len:=fun i:Fin b.rows=>((raw i).lengthCode:ℝ)
  let T:=scaleOf v.sampler π (publicTiles k v.W-1) marks
  let L:=lenCode v.sampler π (publicTiles k v.W-1) marks v.radius
  have ratio (i:ActiveRows raw) : (raw i.val).width=bits (rec.ident i) := by
    simpa only [rec.original i] using read (rec.ident i)
  have dense : TermBudget p q Q Λ (2^h) w v.radius (∑_j:Columns h (2^v.W)×Fin k,R) t len
      (rowRatio raw w) :=
    ledger_of_active raw ord T (fun e=>(L e:ℝ)) (fun e=>(bits e:ℝ)/w) rec.ident rec.original
      (fun i=>by exact_mod_cast rec.metric i) (fun i=>by rw [ratio i])
      v.capacityPrice.le (fun e => scaleOf_nonneg v.sampler π (publicTiles k v.W-1) marks e)
      (fun e=>Nat.cast_nonneg _) (fun e=>by positivity) paid
  have stage (i:Fin b.rows) (pos:0<t i) : t i=dyadic v.W ∧ Λ*(t i)^σ≤len i := by
    by_cases live:0<(raw i).width
    · let j:ActiveRows raw:=⟨i,live⟩
      have eq:t i=T (rec.ident j):=by simp [t,activeScale,live,G,Alignment.scale_read,T,j]
      have positive : 0 < T (rec.ident j) := by rwa [←eq]
      have known:=v.positive_metric π marks (rec.ident j) positive
      rw [eq]
      refine ⟨known.1,?_⟩
      have metric : (raw i).lengthCode = L (rec.ident j) := rec.metric j
      change Λ * T (rec.ident j) ^ σ ≤ ((raw i).lengthCode : ℝ)
      rw [metric]
      exact known.2.2
    · simp [t,activeScale,live] at pos
  have many : ((Finset.univ.filter (fun i=>0<t i)).card:ℝ)≤(v.rowFactor:ℝ)*(2^h:ℕ) := by
    have room:=v.board_rows b order size
    have c:=Finset.card_le_univ (Finset.univ.filter (fun i=>0<t i))
    rw [Fintype.card_fin] at c
    exact_mod_cast c.trans room
  have crossing:2*(v.radius:ℝ)*(∑ _j:Columns h (2^v.W)×Fin k,R:ℕ)/w-(2^h:ℕ)≤
      ∑i∈denseCross raw G,len i*rowRatio raw w i := by
    have test:=(keep_dense raw G (2^h)).mp keep
    simpa [rowRatio,G,len,Fintype.card_prod,Nat.cast_mul,mul_assoc,mul_comm,mul_left_comm] using test
  have nn (i:Fin b.rows):0≤t i:=by dsimp [t,activeScale];split <;> first | exact G.scale_nonneg _ | exact le_rfl
  have bound:=resolution a ha (groups:=groups) raw (fun _=>v.W) t len (denseCross raw G)
    (2^h) w v.radius (∑_j:Columns h (2^v.W)×Fin k,R) nn (fun i=>Nat.cast_nonneg _)
    (denseCross_zero raw G) stage many dense crossing v.W γ
  have proj : atScale (b.transport order) (fun _=>0) 0 raw=atScale (fun i=>0<t i) (fun _=>v.W) v.W raw := by
    funext i
    by_cases live:0<(raw i).width
    · let j:ActiveRows raw:=⟨i,live⟩
      have equiv := rec.transport_iff order (fun e=>Fin.cast size (originalBought v.sampler π (publicTiles k v.W-1) marks e))
        (fun e=>rfl) j
      have yes:(b.transport order i)↔0<t i := by simpa [t,activeScale,live,G,Alignment.scale_read,j] using equiv
      simp [atScale,yes]
    · have zero: (raw i).width=0:=Nat.eq_zero_of_not_pos live
      simp [atScale,zero]
  rw [proj]
  simpa [typeFraction] using bound

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
