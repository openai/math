import OAI.Hierarchy.DescentPrivateRootBook

namespace OAI
/-! # Causal reset receiver with every private-root table mounted in the same memory -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentSIMDLookup DescentSixParty.Chronology DescentSixParty.Chronology.Shelf
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D cap N n r c H G K R M h l t field Ht w : ℕ}
    (a : Receiver D cap N n r c H G K R M h l t field Ht w) (b : RootBook n r D (2^r) cap field)
local notation "G₁" => 2^c

def headerEnd:=b.stop a.projectionEnd H G₁ M
def rootedTemplates:=b.templates a.projectionEnd H G₁ M
def preparedEnd :=(RootTemplates.arena (a.headerEnd b) H G₁ M r n D).first (Fintype.card (RootPage r (2^n)))
def headerImage:=b.book a.projectionEnd H G₁ M w

structure PreparedFits : Prop extends PrefixFits a where
  literals : a.headerEnd b<2^w
  rows : (a.rootedTemplates b).Fits (a.headerEnd b) H G₁ M Ht w
def preparedCatalog (space : a.PreparedFits b) :=
  series (catalog ((a.rootedTemplates b).job (a.headerEnd b) space.rows ∘ (rootIndex r (2^n)).symm))

def preparedRoots (space : a.PreparedFits b) :=((a.prefix space.toPrefixFits).seq (a.headerImage b).program).seq
  (a.preparedCatalog b space).program
def preparedTicks (space : a.PreparedFits b) :=(a.prefixTime space.toPrefixFits+
  (4+10*(a.headerEnd b-a.projectionEnd)))+(a.preparedCatalog b space).ticks
def preparedMid (space : a.PreparedFits b) (m : Memory w) :=
  (a.headerImage b).output (a.prefixImage space.toPrefixFits m)
def preparedImage (space : a.PreparedFits b) (m : Memory w) :=(a.preparedCatalog b space).image (a.preparedMid b space m)

theorem origin_le_projection : a.origin≤ a.projectionEnd:=by
    have ret:a.origin≤ a.retileEnd:=by dsimp [retileEnd,DescentGLPacked.BankImage.SignedFields.Retile.stop,Subwords.destination];omega
    have join:a.retileEnd≤ a.signedOrigin:=Nat.le_add_right ..
    have shift:a.signedOrigin≤ a.signedEnd:=DescentGLPacked.BankImage.Dated.origin_le_endAddress _ _ _ _ _
    exact ((ret.trans join).trans shift).trans (Nat.le_add_right ..)

theorem prepared_lower (space : a.PreparedFits b) (m : Memory w) (x : ℕ) (lo : x< a.origin) :
    a.preparedMid b space m x=m x := by
  have first:=lo.trans_le a.origin_le_projection
  have kept:=(b.installed a.projectionEnd H G₁ M (a.prefixImage space.toPrefixFits m) space.literals).2.2.2.2.2 x (.inl first)
  exact kept.trans ((a.prefix_hardware space.toPrefixFits m).2.2 x (.inl lo))

/-- A bounded prior expression, including the Walsh zero and the inverse-layout comparison,
continues to read its original digit from the prepared root input. -/
theorem prepared_source {u : ℕ} (space : a.PreparedFits b) (e : Expr) (m : Memory w)
    (values : Fin H→Fin G₁→Cell u) (fits : e.Fits w a.origin)
    (seen : DescentPackedZip.Source e values M m) :
    DescentPackedZip.Source e values M (a.preparedMid b space m) := by
  intro row
  exact (eval_below e _ m (a.preparedMid b space m) fits (a.prepared_lower b space m)).trans (seen row)

theorem prepared_any (space : a.PreparedFits b) (m : Memory w) :
    (a.preparedRoots b space).Exec m (a.preparedImage b space m) (a.preparedTicks b space) ∧
      CheapCode (a.preparedRoots b space) ∧
      ∀x,x< a.origin ∨ a.preparedEnd b≤ x→a.preparedImage b space m x=m x := by
  have h:=b.limits a.projectionEnd H G₁ M
  have one:a.projectionEnd≤ a.headerEnd b:=h.1.trans (h.2.1.trans h.2.2)
  have two:a.headerEnd b≤ a.preparedEnd b:=Nat.le_add_right ..
  have positive:=a.origin_le_projection
  obtain ⟨run,cheap,old⟩:=a.prefix_hardware space.toPrefixFits m
  obtain ⟨emit,paper,_,_,_,header⟩:=b.installed a.projectionEnd H G₁ M (a.prefixImage space.toPrefixFits m) space.literals
  obtain ⟨jobs,_,archive⟩:=(a.rootedTemplates b).run (a.headerEnd b) space.rows (a.preparedMid b space m)
  refine ⟨Procedure.Exec.then (Procedure.Exec.then run emit) jobs,cheap_seq (cheap_seq cheap paper) (a.preparedCatalog b space).cheap,?_⟩
  rintro x (lo|hi)
  · have l:=lo.trans_le positive
    exact (archive x (.inl (l.trans_le one))).trans ((header x (.inl l)).trans (old x (.inl lo)))
  · have l:=two.trans hi
    exact (archive x (.inr hi)).trans ((header x (.inr l)).trans (old x (.inr (one.trans l))))

theorem prepared_root (space : a.PreparedFits b) (m : Memory w) (p : RootPage r (2^n)) (x : ℕ)
    (lo : ((a.rootedTemplates b).job (a.headerEnd b) space.rows p).first≤ x)
    (hi : x<((a.rootedTemplates b).job (a.headerEnd b) space.rows p).limit) :
    a.preparedImage b space m x=((a.rootedTemplates b).job (a.headerEnd b) space.rows p).image (a.preparedMid b space m) x :=
  ((a.rootedTemplates b).run (a.headerEnd b) space.rows (a.preparedMid b space m)).2.1 p x lo hi

theorem prepared_mid_window (space : a.PreparedFits b) (m : Memory w) (x : ℕ) (lo:x< a.projectionEnd) :
    a.preparedMid b space m x=a.prefixImage space.toPrefixFits m x :=
  (b.installed a.projectionEnd H G₁ M (a.prefixImage space.toPrefixFits m) space.literals).2.2.2.2.2 x (.inl lo)

theorem prepared_window (space : a.PreparedFits b) (m : Memory w) (x : ℕ) (lo:x< a.projectionEnd) :
    a.preparedImage b space m x=a.prefixImage space.toPrefixFits m x := by
  have limits:=b.limits a.projectionEnd H G₁ M
  have later:=lo.trans_le (limits.1.trans (limits.2.1.trans limits.2.2))
  have jobs:=((a.rootedTemplates b).run (a.headerEnd b) space.rows (a.preparedMid b space m)).2.2 x (.inl later)
  have held:=(b.installed a.projectionEnd H G₁ M (a.prefixImage space.toPrefixFits m) space.literals).2.2.2.2.2 x (.inl lo)
  exact jobs.trans held

theorem prepared_tables (space : a.PreparedFits b) (m : Memory w) (p : RootPage r (2^n)) :
    let first:=a.projectionEnd
    let actual:=a.preparedMid b space m
    let spec:=b.table p
    let terms:=spec.2.terms (b.atPage first H G₁ M p) H G₁ M (b.target first H G₁ M p)
    (∀i,DescentPackedZip.Static (terms.tables i) (DescentPacking.PackedMatch.Local.Gather.setField (d:=spec.2.field) i) M actual) ∧
      DescentPackedFallbackTree.Image.resident spec.2.law terms.menu H G₁ M actual := by
  obtain ⟨_,_,_,_,pages,_⟩:=b.installed a.projectionEnd H G₁ M (a.prefixImage space.toPrefixFits m) space.literals
  have top:=(b.bounds a.projectionEnd H G₁ M w p).2
  have j:=(rootIndex r (2^n) p).isLt
  have endAt:(b.pageImage a.projectionEnd H G₁ M w p).stop≤ a.headerEnd b:=
    top.trans (Nat.add_le_add_left (Nat.mul_le_mul_right (b.width H G₁ M) j) _)
  exact (b.table p).2.resident_at (b.atPage a.projectionEnd H G₁ M p) (b.target a.projectionEnd H G₁ M p) _
    (endAt.trans_lt space.literals) (pages p)

/-- The same installed prefix supplies the scalar tables used by fallback traversal and the
broadcast words used by every data-dependent rank lookup. -/
theorem prepared_shared (space : a.PreparedFits b) (m : Memory w) (p : RootPage r (2^n)) :
    let first:=a.projectionEnd
    let bank:=b.common first H
    let actual:=a.preparedMid b space m
    DescentSharedBookScan.fixed bank r (2^n) D H actual ∧
    DescentNativeFallbackShapes.Stored bank.shapes r b.fallbackDegree b.hubBits b.loadBits (2^n) b.shapes actual ∧
    DescentSharedLeafLookup.Fixed (b.rankHeader first H G₁ M p) (DescentSharedBookScan.width r (2^n) D)
      H G₁ M field actual := by
  obtain ⟨_,_,scalar,repeats,_,_⟩:=b.installed a.projectionEnd H G₁ M (a.prefixImage space.toPrefixFits m) space.literals
  have lim:=b.limits a.projectionEnd H G₁ M
  have top:b.scalarEnd a.projectionEnd H<2^w:=(lim.2.1.trans lim.2.2).trans_lt space.literals
  obtain ⟨controls,shapes⟩:=DescentSharedBookScan.Public.stored b.previousNeighbors b.previousHubs
    (a.preparedMid b space m) top scalar
  exact ⟨controls,shapes,DescentSharedLeafLookup.Public.mounted (b.scalarEnd a.projectionEnd H)
    (DescentSharedBookScan.width r (2^n) D) H G₁ M field _ (a.preparedMid b space m) repeats⟩

/-- One mounted dictionary converts every inverse-layout comparison to the private
packet pitch. All source rows and every padded host share the same dictionary. -/
theorem prepared_comparison {raw : ℕ} (space : a.PreparedFits b) (p : RootPage r (2^n)) (m : Memory w)
    (mode : b.originalBits=some raw) (e : Expr) (fits : e.Fits w a.origin)
    (compare : Fin H→Fin G₁→Cell raw) (read : DescentPackedZip.Source e compare M m) :
    DescentPackedZip.Source (.lookup (DescentRootOrderCast.bank (b.castAt a.projectionEnd H G₁ M) raw M) e)
      (fun h g=> DescentRootOrderCast.widen (b:=field) (compare h g)) M (a.preparedMid b space m) := by
  let base:=a.projectionEnd
  have pre:=a.prepared_source b space e m compare fits read
  let I:=a.headerImage b
  have lim:=b.limits base H G₁ M
  have live:=I.issue (a.prefixImage space.toPrefixFits m)
    (by change base+(b.stop base H G₁ M-base)< _
        have:=lim.1.trans (lim.2.1.trans lim.2.2)
        have top:b.stop base H G₁ M<2^w:=space.literals
        omega)
  have literal:=b.cast_resident base H G₁ M raw p (a.preparedMid b space m) mode live.2.1
  have cardOne:1≤ Fintype.card (RootPage r (2^n)):=by have:=(rootIndex r (2^n) p).isLt;omega
  have slots:=Nat.mul_le_mul_right (b.width H G₁ M) cardOne
  rw [Nat.one_mul] at slots
  have right:DescentRootOrderCast.stop (b.castAt base H G₁ M) raw M < 2^w:=by
    have bound:b.stop base H G₁ M<2^w:=space.literals
    have equality:b.castWords M=2^(raw*M):=by simp [RootBook.castWords,mode]
    change b.repeatEnd base H G₁ M+Fintype.card (RootPage r (2^n))*b.width H G₁ M<2^w at bound
    have saved:b.castWords M≤ b.sharedWords M:=le_max_left ..
    rw [equality] at saved
    rw [RootBook.width] at slots bound
    dsimp [DescentRootOrderCast.stop,RootBook.castAt]
    omega
  exact DescentRootOrderCast.source (b.castAt base H G₁ M) e _ right literal compare pre

/-- Rank-directed reservations, shared by every physical address and root, occupy the
second public page's tail. This interval is literal and precedes every data-dependent read. -/
theorem prepared_extra (space : a.PreparedFits b) (p : RootPage r (2^n)) (m : Memory w) (j : ℕ) (valid : j< b.extraSize) :
    a.preparedMid b space m (b.auxAt a.projectionEnd H G₁ M+j)=(b.extraWord j:Word w) := by
  have lim:=b.limits a.projectionEnd H G₁ M
  have src:=(a.headerImage b).issue (a.prefixImage space.toPrefixFits m) (by
    change a.projectionEnd+(a.headerEnd b-a.projectionEnd)< _
    have le_:a.projectionEnd≤ a.headerEnd b:=lim.1.trans (lim.2.1.trans lim.2.2)
    have top:=space.literals
    omega)
  exact b.extra_at a.projectionEnd H G₁ M p _ src.2.1 j valid

/-- The complete root pass also preserves its physical header all the way through the
last actor. Subsequent actor/profile issuers may reuse the shared scalar geometry directly. -/
theorem prepared_shared_final (space : a.PreparedFits b) (m : Memory w) (p : RootPage r (2^n)) :
    let first:=a.projectionEnd
    let bank:=b.common first H
    let actual:=a.preparedImage b space m
    DescentSharedBookScan.fixed bank r (2^n) D H actual ∧
    DescentNativeFallbackShapes.Stored bank.shapes r b.fallbackDegree b.hubBits b.loadBits (2^n) b.shapes actual ∧
    DescentSharedLeafLookup.Fixed (b.rankHeader first H G₁ M p) (DescentSharedBookScan.width r (2^n) D)
      H G₁ M field actual := by
  let I:=a.headerImage b
  have lim:=b.limits a.projectionEnd H G₁ M
  have orig:=I.issue (a.prefixImage space.toPrefixFits m) (by
    change a.projectionEnd+(a.headerEnd b-a.projectionEnd)< _
    have lower:a.projectionEnd≤ a.headerEnd b:=lim.1.trans (lim.2.1.trans lim.2.2)
    have top:=space.literals
    omega)
  have posted:I.Resident (a.preparedImage b space m):=by
    intro z lo hi
    have past:=((a.rootedTemplates b).run (a.headerEnd b) space.rows (a.preparedMid b space m)).2.2 z (.inl hi)
    exact past.trans (orig.2.1 z lo hi)
  obtain ⟨scalar,repeats,_⟩:=b.resident a.projectionEnd H G₁ M _ posted
  have top:b.scalarEnd a.projectionEnd H<2^w:=(lim.2.1.trans lim.2.2).trans_lt space.literals
  obtain ⟨controls,shapes⟩:=DescentSharedBookScan.Public.stored b.previousNeighbors b.previousHubs _ top scalar
  exact ⟨controls,shapes,DescentSharedLeafLookup.Public.mounted (b.scalarEnd a.projectionEnd H)
    (DescentSharedBookScan.width r (2^n) D) H G₁ M field _ _ repeats⟩

theorem prepared_room (_space : a.PreparedFits b) {out : ℕ} (after : a.headerEnd b≤ out) (fits : out<2^w)
    (neighbor : b.previousNeighbors.Fits w out) (hub : b.previousHubs.Fits w out)
    (peers : H*D≤ b.previousNeighbors.size) (hubs : H≤ b.previousHubs.size) (racks : H<2^w) (slots : D+1<2^w) :
    DescentSharedBookScan.Room (b.common a.projectionEnd H) r (2^n) D H w out := by
  have lim:=b.limits a.projectionEnd H G₁ M
  exact DescentSharedBookScan.Public.room_at b.previousNeighbors b.previousHubs
    ((lim.2.1.trans lim.2.2).trans after) fits neighbor hub peers hubs racks slots

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
