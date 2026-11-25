import OAI.Hierarchy.TaggedWireTransportAt
import OAI.Hierarchy.TaggedWireArchiveAperture
import OAI.Hierarchy.TaggedWireReportMatrix

namespace OAI
/-! # Exact final turn bits in the reporter's original native row order -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.WireTelescope.NamedAperture
open LinearAlgebra.SpectralBooks ChordGraph CalendarTape
open scoped Classical

def liftRow {I E U : Type} (fixed : I→ℕ) (other : U→ℕ) (ident : {i // 0<fixed i} ↪ E) :
    {i : I⊕U // 0<Sum.elim fixed other i} ↪ E⊕U where
  toFun | ⟨.inl i,h⟩=>.inl (ident ⟨i,h⟩) | ⟨.inr j,_⟩=>.inr j
  inj' := by
    rintro ⟨(i|j),hi⟩ ⟨(l|m),hl⟩ eq
    · exact Subtype.ext (congrArg Sum.inl (congrArg Subtype.val (ident.injective (Sum.inl.inj eq))))
    · exact (Sum.inl_ne_inr eq).elim
    · exact (Sum.inr_ne_inl eq).elim
    · exact Subtype.ext (congrArg Sum.inr (Sum.inr.inj eq))

/-- Number the old rows with the reporter's specified equivalence, eliminating
only zero-width padding. Crucially, the dense chord prefix continues to count
the original row order. -/
def renameRows {I E U : Type} {n : ℕ} (fixed : I→ℕ) (other : U→ℕ) (number : Fin n≃I⊕U)
    (ident : {i // 0<fixed i} ↪ E) : LiveEnd (Sum.elim fixed other ∘ number) ↪ (E⊕U)×Bool where
  toFun z := (liftRow fixed other ident ⟨number z.val.1,z.2⟩,z.val.2)
  inj' := by
    intro p q eq
    have ord := congrArg Subtype.val ((liftRow fixed other ident).injective (congrArg Prod.fst eq))
    have side : p.val.2 = q.val.2 := congrArg (fun e : (E⊕U)×Bool => e.2) eq
    exact Subtype.ext (Prod.ext (number.injective ord) side)

end Hierarchy.WireTelescope.NamedAperture

namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.Terminal
open LinearAlgebra.SpectralBooks ChordGraph AdaptiveProbe ReportSockets WireTelescope CalendarTape
open ProtocolRAMEmit
open scoped Classical

variable {h W k attempts edges : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : Marks h W k attempts) (unique : Exclusive marked)
    (B : Mount (S:=S) π (name (W:=W) (k:=k)) edges) (pad : Chord (siteLast h (2^W) k+1))
    (fixed : Fin edges→ℕ) (stock : Goods h W k→ℕ) (reserved used : Catalysts h W k→ℕ)
    (ident : {i // 0<fixed i} ↪ Catalogue S π depth marked)

local notation "layout" => B.matrixLayout (siteNumber h (2^W) k).injective pad
local notation "oldBits" => SettledMatrix.Layout.bits fixed stock reserved used

def orig : NamedAperture.LiveEnd oldBits ↪ Source S π depth marked × Bool :=
  NamedAperture.renameRows fixed (Sum.elim stock fun i=>reserved i-used i)
    (SettledMatrix.Layout.numbered (r:=edges)) ident

def ports : NamedAperture.LiveEnd oldBits ↪ Public S h W k attempts :=
  (orig S π depth marked fixed stock reserved used ident).trans
    ((orient S π depth marked).toEmbedding.trans (physical S π depth marked unique))

variable {M den w R : ℕ} {rows : Fin edges→ProtocolRAMEmit.Row}
    {G : Geometry (boardLayout h (2^W) k w R) M den rows} (H : MatrixReceipt B fixed stock reserved used G)

local notation "U" => B.actual.chordWidths fixed+(commodityGraph π name).chordWidths stock+
  (catalystGraph name).chordWidths (fun c=>reserved c-used c)

def place (cap : Public S h W k attempts→ℕ)
    (room : ∀p,oldBits p.val.1≤cap (ports S π depth marked unique fixed stock reserved used ident p)) :
    (Σs,SiteBit U s) ↪ (Σu,Fin (cap u)) :=
  (NamedAperture.transport (H.old_width (siteNumber h (2^W) k).injective pad)).symm.toEmbedding.trans
    (NamedAperture.livePlace (layout).family oldBits (ports S π depth marked unique fixed stock reserved used ident) cap room)

/-- This is the actual local input row read by matrixLayout.operator, including
reversed physical endpoints, padded rows and arbitrary parallel order. -/
theorem row_word {s : Fin (siteLast h (2^W) k+1)} (x : State U s)
    (p : (bitGraph (rowGraph (layout).family) oldBits).Port s) :
    let same := H.old_width (siteNumber h (2^W) k).injective pad
    rowBits (layout).family oldBits (cast (congrArg (fun V=>State V s) same.symm) x) p=
      siteBits U s x (NamedAperture.transportAt same (NamedAperture.atPort (layout).family oldBits p)) :=
  NamedAperture.rowBits_transport (layout).family oldBits _ x p

private theorem transport_read {K : ℕ} {X Y : Widths K} {T : Type} (eq : X = Y)
    (f : (Σi,SiteBit X i) → T) {i : Fin K} (bit : SiteBit X i) :
    f ((NamedAperture.transport eq).symm ⟨i,NamedAperture.transportAt eq bit⟩) = f ⟨i,bit⟩ := by
  subst Y
  rfl

set_option maxHeartbeats 1000000 in
theorem read (cap : Public S h W k attempts→ℕ)
    (room : ∀p,oldBits p.val.1≤cap (ports S π depth marked unique fixed stock reserved used ident p))
    {s : Fin (siteLast h (2^W) k+1)} (p : (bitGraph (rowGraph (layout).family) oldBits).Port s) :
    let same := H.old_width (siteNumber h (2^W) k).injective pad
    let key : NamedAperture.LiveEnd oldBits := ⟨(p.1.1.1,p.1.2),Nat.zero_lt_of_lt p.1.1.2.isLt⟩
    place S π depth marked unique B pad fixed stock reserved used ident H cap room
      ⟨s,NamedAperture.transportAt same (NamedAperture.atPort (layout).family oldBits p)⟩=
        ⟨ports S π depth marked unique fixed stock reserved used ident key,p.1.1.2.castLE (room key)⟩ := by
  intro same key
  let bit := NamedAperture.atPort (layout).family oldBits p
  let embed := NamedAperture.livePlace (layout).family oldBits
    (ports S π depth marked unique fixed stock reserved used ident) cap room
  exact (transport_read same embed bit).trans (NamedAperture.live_read (layout).family oldBits _ cap room p)

theorem native_site (p : NamedAperture.LiveEnd oldBits)
    (positions : ∀i : {i // 0<fixed i},filledChord B.actual pad i.val=sorted S π depth marked (.inl (ident i))) :
    name (site S (ports S π depth marked unique fixed stock reserved used ident p))=
      (portGraph _).vertex ((layout).family p.val.1) p.val.2 := by
  let num := SettledMatrix.Layout.numbered (r:=edges) (I:=Goods h W k) (A:=Catalysts h W k)
  obtain ⟨⟨i,b⟩,hi⟩ := p
  obtain ⟨c,rfl⟩ := num.symm.surjective i
  have aligned (e : Source S π depth marked) : name (site S (physical S π depth marked unique (orient S π depth marked (e,b))))=
      (portGraph _).vertex (sorted S π depth marked e) b := by
    let id := (Fintype.equivFin (Source S π depth marked)).symm
    simpa [named,id] using named_site S π depth marked unique id (id.symm e) b
  let other := Sum.elim stock (fun i => reserved i-used i)
  let src := NamedAperture.liftRow fixed other ident
  have hc : 0 < Sum.elim fixed other c := by
    change 0 < Sum.elim fixed other (num (num.symm c)) at hi
    simpa only [num.apply_symm_apply] using hi
  have sameRow : (⟨num (num.symm c),hi⟩ : {x // 0 < Sum.elim fixed other x}) = ⟨c,hc⟩ :=
    Subtype.ext (num.apply_symm_apply c)
  refine (aligned (src ⟨num (num.symm c),hi⟩)).trans ?_
  apply congrArg (fun chord => (portGraph _).vertex chord b)
  change sorted S π depth marked (src ⟨num (num.symm c),hi⟩) = (layout).original (num (num.symm c))
  rw [sameRow,num.apply_symm_apply]
  rcases c with u|g|a
  · exact (positions ⟨u,hc⟩).symm
  · rfl
  · rfl

include H in
theorem positions_of_reported
    (observed : ∀i : {e // 0<fixed e},let ends:=actualEnds S π depth marked (ident i)
      ((rows i.val).endpoint=(name ends.1).val ∧ (rows i.val).opposite=(name ends.2).val) ∨
      ((rows i.val).endpoint=(name ends.2).val ∧ (rows i.val).opposite=(name ends.1).val)) :
    ∀i : {e // 0<fixed e},filledChord B.actual pad i.val=sorted S π depth marked (.inl (ident i)) := by
  intro i
  let z := actualEnds S π depth marked (ident i)
  have distinct : name z.1≠name z.2 := name.injective.ne (actual_distinct S π depth marked (ident i))
  have yes : 0<(rows i.val).width := by rw [H.report];have positive:=i.property;omega
  let pos : ActiveRows rows := ⟨i.val,yes⟩
  have native : (B.actual.tail i.val=name z.1 ∧ B.actual.head i.val=name z.2) ∨
      (B.actual.tail i.val=name z.2 ∧ B.actual.head i.val=name z.1) := by
    obtain ⟨left,right⟩|⟨left,right⟩:=H.ends pos
    · obtain ⟨a,b⟩|⟨a,b⟩:=observed i
      · exact .inl ⟨Fin.ext ((congrArg Fin.val left).trans a),Fin.ext ((congrArg Fin.val right).trans b)⟩
      · exact .inr ⟨Fin.ext ((congrArg Fin.val left).trans a),Fin.ext ((congrArg Fin.val right).trans b)⟩
    · obtain ⟨a,b⟩|⟨a,b⟩:=observed i
      · exact .inr ⟨Fin.ext ((congrArg Fin.val left).trans b),Fin.ext ((congrArg Fin.val right).trans a)⟩
      · exact .inl ⟨Fin.ext ((congrArg Fin.val left).trans b),Fin.ext ((congrArg Fin.val right).trans a)⟩
  change filledChord B.actual pad i.val=orderedChord (name z.1) (name z.2) distinct
  rcases native with ⟨one,two⟩|⟨one,two⟩
  · simp [filledChord,one,two,distinct]
  · by_cases lt:name z.1<name z.2
    · simp [filledChord,one,two,distinct.symm,orderedChord,lt,not_lt.mpr lt.le]
    · have gt:name z.2<name z.1 := lt_of_le_of_ne (le_of_not_gt lt) distinct.symm
      simp [filledChord,one,two,distinct.symm,orderedChord,lt,gt]

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.Terminal

end
end OAI
