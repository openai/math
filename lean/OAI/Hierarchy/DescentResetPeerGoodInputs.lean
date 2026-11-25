import OAI.Hierarchy.DescentResetPeerRootPages
import OAI.Hierarchy.DescentPreparedReservations

namespace OAI
/-! # The three measured operands of each private good-root page -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentResetHostSize
open DescentSixParty.Chronology DescentSixParty DescentResetGates DescentPackedWalsh DescentPlainTerminal.Suffix
open DescentRotorRootPresence DescentSharedLeafLookup DescentRotorPeerIssue
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open ThreeFlat.RAM.DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {D cap N n r c H G K R M h₀ l t field Ht w h bit : ℕ}
    (a : Receiver D cap N n r c H G K R M h₀ l t field Ht w) (E : EstimatorArena)
    (stencil : StencilBook) (old : StencilBook.Sources) (stencilBase splitBank hubWidth : ℕ)
    (peers : Ports D) (oldId : Bank) (publicCap f fee full total portPitch : ℕ)
    (board : NonlinearExpanders.Graph n h) (packet C groupDigits batches layerBits factor : ℕ)
    (primitive : CanonicalTag (2^n)→Cell bit) (bookPage : RootPage r (2^n))
local notation "L" => 2^r
local notation "J" => 2^c
local notation "B" => a.issuedBook E stencil old stencilBase splitBank hubWidth peers oldId (.lit publicCap)
  f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage
local notation "src" => a.issuedSources E stencil old stencilBase splitBank hubWidth peers oldId (.lit publicCap)
  f fee full total portPitch
local notation "head" => stencil.header stencilBase
variable (space : a.PreparedFits B) (mem : Memory w)
local notation "mid" => a.preparedMid B space mem
local notation "ceiling" => a.headerEnd B
local notation "rack" => Expr.lookup oldId .row
local notation "far" => (head).levelAt old.levels rack
local notation "dep" => Expr.branch .lt rack old.count
  (.op .add (.op .sub (Cutoff.level (.lit c) far) (.lit c)) (.lit 1)) (.lit 0)

def depthDigit (c count : ℕ) (level : Fin H→ℕ) (v : Fin H) :=
  if v.val < count then level v-c+1 else 0

def goodInput (c field publicCap count : ℕ) (level : Fin H→ℕ) (marks : Fin H→Fin J→Fin L→Cell field)
    (root : Code r) (v : Fin H) (g : Fin J) (j : Fin 3) : Cell field :=
  if j=0 then (publicCap:Cell field) else if j=1 then (depthDigit c count level v:Cell field) else marks v g (sample root)

/-- The source of the conditional depth is the old row count and the strided depth word issued
at the original estimator. Beyond that count the physical scalar is exactly zero. -/
theorem good_header_controls (count : ℕ) (level : Fin H→ℕ)
    (eqH : stencil.hosts=H) (extent : H < 2^w) (actualHosts : count ≤ H)
    (counted : ∀p : Row H J M,old.count.eval mid ((row H J M p).val:Word w)=(count:Word w))
    (owner : ∀p : Row H J M,(rack).eval mid ((row H J M p).val:Word w)=(p.1.val:Word w))
    (chart : (head).chart.Resident mid) (addresses : (head).depth.Fits w ceiling)
    (physical : old.levels.Fits w ceiling)
    (range : ∀v : Fin H,v.val < count → v.val*(stencil.m+1) < old.levels.size)
    (stored : ∀v : Fin H,v.val < count → mid (old.levels.base+v.val*(stencil.m+1))=(level v:Word w))
    (common : ∀v : Fin H,v.val < count → c ≤ level v ∧ level v < 2^w)
    (tiny : ∀v : Fin H,v.val < count → level v-c+1 < 2^field)
    (prior : publicCap < 2^field)
 :
    Source (src).priorCap (fun (_ : Fin H) (_ : Fin J)=>(publicCap:Cell field)) M mid ∧
    Source (src).relativeDepth (fun (v : Fin H) (_ : Fin J)=>(depthDigit c count level v:Cell field)) M mid :=by
  let header:=(B).rankHeader a.projectionEnd H J M bookPage
  have controls:=a.prepared_broadcast_room B space bookPage
  have fixed:=(a.prepared_shared B space mem bookPage).2.2
  have cword : ∀p : Row H J M,(Expr.lit publicCap).eval mid ((row H J M p).val:Word w)=
      (((publicCap:Cell field).val):Word w):=by intro p;rw [Fin.val_cast_of_lt prior];rfl
  have capRead:=broadcast_at header (.lit publicCap) mid ceiling controls fixed (fun _:Fin H=>(publicCap:Cell field)) cword
  have depthRead:=broadcast_at header dep mid ceiling controls fixed (fun v:Fin H=>(depthDigit c count level v:Cell field)) (by
    intro p
    let v:=p.1
    let tick:Word w:=((row H J M p).val:Word w)
    let ord : Fin (head).hosts:=Fin.cast eqH.symm v
    have test : Comparison.lt.test ((rack).eval mid tick) (old.count.eval mid tick)=decide (v.val < count) := by
      simp only [tick, v, owner p, counted p, Comparison.test, Fin.lt_def, Fin.val_cast_of_lt (v.isLt.trans extent),
        Fin.val_cast_of_lt (actualHosts.trans_lt extent)]
    by_cases hv : v.val < count
    · have read:=((head).level_at old.levels rack mid tick ceiling ord chart addresses physical (range v hv) (owner p)).trans (stored v hv)
      have ⟨lo,up⟩:=common v hv
      have cut:=(PortLevels.read_level (.lit c) far mid tick c (level v) rfl read (by rwa [max_eq_right lo]))
      have wordLo : (c : Word w) ≤ (level v : Word w) := by
        change (c : Word w).val ≤ (level v : Word w).val
        simpa only [Fin.val_cast_of_lt (lo.trans_lt up), Fin.val_cast_of_lt up] using lo
      rw [max_eq_right wordLo] at cut
      have offset:=PortLevels.read_relative c (level v) (Cutoff.level (.lit c) far) mid tick lo cut
      change (if Comparison.lt.test ((rack).eval mid tick) (old.count.eval mid tick) then
        ((PortLevels.relative c (Cutoff.level (.lit c) far)).eval mid tick+(1:Word w)) else (0:Word w))=_
      rw [test,ite_eq_left (by simpa using hv),offset]
      change p.1.val < count at hv
      simp only [v, depthDigit, ite_eq_left hv]
      rw [Fin.val_cast_of_lt (tiny p.1 hv), Nat.cast_add, Nat.cast_one]
    · change (if Comparison.lt.test ((rack).eval mid tick) (old.count.eval mid tick) then _ else (0:Word w))=_
      change ¬ p.1.val < count at hv
      simp [test, v, hv, depthDigit])
  exact ⟨capRead,depthRead⟩

theorem good_header_inputs (count : ℕ) (level : Fin H→ℕ) (marks : Fin H→Fin J→Fin L→Cell field)
    (eqH : stencil.hosts=H) (extent : H < 2^w) (actualHosts : count ≤ H)
    (counted : ∀p : Row H J M,old.count.eval mid ((row H J M p).val:Word w)=(count:Word w))
    (owner : ∀p : Row H J M,(rack).eval mid ((row H J M p).val:Word w)=(p.1.val:Word w))
    (chart : (head).chart.Resident mid) (addresses : (head).depth.Fits w ceiling)
    (physical : old.levels.Fits w ceiling)
    (range : ∀v : Fin H,v.val < count → v.val*(stencil.m+1) < old.levels.size)
    (stored : ∀v : Fin H,v.val < count → mid (old.levels.base+v.val*(stencil.m+1))=(level v:Word w))
    (common : ∀v : Fin H,v.val < count → c ≤ level v ∧ level v < 2^w)
    (tiny : ∀v : Fin H,v.val < count → level v-c+1 < 2^field)
    (prior : publicCap < 2^field)
    (markFit : ∀i,((src).here i).Fits w ceiling ∧ H*chunks J M ≤ ((src).here i).size)
    (stamp : ∀i,Reads ((src).here i) (fun v g=>marks v g i) M mid) :
    ∀s root j,Source ((((B).good s root (.inl true)).2).reads j)
      (fun v g=>goodInput c field publicCap count level marks root v g j) M
      (a.rootInputState B space mem (privatePage s (.inl root))) := by
  obtain ⟨capRead,depthRead⟩:=a.good_header_controls E stencil old stencilBase splitBank hubWidth peers oldId publicCap
    f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage space mem
    count level eqH extent actualHosts counted owner chart addresses physical range stored common tiny prior
  intro s root j
  change Source ((src).headerRow root j) _ M mid
  change Fin 3 at j
  by_cases h0 : j = 0
  · simpa only [RootSources.headerRow, goodInput, ite_eq_left h0] using capRead
  by_cases h1 : j = 1
  · simpa only [RootSources.headerRow, goodInput, ite_eq_right h0, ite_eq_left h1] using depthRead
  · simpa only [RootSources.headerRow, goodInput, RootSources.self, ite_eq_right h0, ite_eq_right h1] using
      source_column ((src).here (sample root)) ceiling (markFit _).1 mid _ (markFit _).2 (stamp (sample root))

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
