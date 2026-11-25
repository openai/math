import OAI.Hierarchy.DescentIssuedRootWidths
import OAI.Hierarchy.DescentFallbackPeriodTariff
import OAI.Hierarchy.DescentPackedMatchedAll

namespace OAI
/-! # Instruction counts of the actual reset root operands -/
namespace Hierarchy.DescentPlainTerminal.Suffix.StencilBook
open DescentPacking.PackedMatch.Local DescentSIMDLookup DescentPackedColony ProtocolRAM
noncomputable section

/-- Each original-coordinate bit plane costs two word reads from its physical repacked row.
The assembly reads each plane once per requested comparison. -/
theorem order_work (S : StencilBook) (X : Sources) (base out g i x : ℕ) :
    (S.orderExpr X base out g i x).work≤6+S.m*23 := by
  let src:=(S.readers base).inputs (S.inputs X base out g)
  have single (j : Fin S.m) : (src.planes j).work≤12 := by change 12≤12; exact le_rfl
  have bound := Gather.collect_work (N:=S.m) src.planeTables src.planes (List.finRange S.m) 12 single
  have lengthEq : (List.finRange S.m).length = S.m := List.length_finRange
  change (Gather.collect (N:=S.m) src.planeTables src.planes (List.finRange S.m)).work+5≤_
  omega

end
end Hierarchy.DescentPlainTerminal.Suffix.StencilBook

namespace Hierarchy.DescentFallbackPeriod.Projected.RootSources
open DescentPackedColony DescentSharedLeafLookup DescentPackedPrivateMenu DescentResetHostSize
open DescentSIMDLookup DescentResetGates DescentPacking.PackedMatch.Local ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {D L cap H limit n h r field bit : ℕ}

/-- Bounds on the four nonuniform numerical expressions. The corresponding shared pointer,
signed row and projected self reads have constant instruction count. -/
structure OperandWork (src : RootSources D L cap) (limit : ℕ) : Prop where
  base : 80≤limit
  order : ∀i x,(src.oldOrder i x).work≤limit
  reservations : ∀p q f,(src.reservation p q f).work≤limit
  capacity : src.priorCap.work≤limit
  depth : src.relativeDepth.work≤limit

variable (src : RootSources D (2^r) cap)

theorem matrixRow_work (room : src.OperandWork limit) (H : ℕ)
    (j : Fin (DescentRotorWindowArchive.count D (2^r) cap)) :
    (src.matrixRow H j).work≤limit := by
  unfold matrixRow
  rcases DescentRotorWindowArchive.ix.symm j with (((i|⟨p,i⟩)|⟨i,q⟩)|(⟨i,x⟩|⟨p,q,u⟩))
  · exact (show 7≤80 by decide).trans room.base
  · exact (show (peerExpr src.peers (src.tagged i) H p).work≤80 by simp only [peerExpr,neighborID,Expr.work]; decide).trans room.base
  · exact (show 7≤80 by decide).trans room.base
  · exact room.order i x
  · exact room.reservations p q u

theorem good_work (room : src.OperandWork limit) (H : ℕ) (board : NonlinearExpanders.Graph n h)
    (packet f Ht C groupDigits batches layerBits : ℕ) (primitive : CanonicalTag (2^n)→Cell bit)
    (s : Bool) (v : Code r) (k : Bool ⊕ Fin (2^n)) :
    ∀j,((src.good (field:=field) board packet f Ht C groupDigits batches layerBits primitive H s v k).2.reads j).work≤limit := by
  rcases k with (flag|gate)
  · cases flag
    · exact src.matrixRow_work room H
    · intro j
      change (src.headerRow v j).work≤limit
      unfold headerRow
      split
      · exact room.capacity
      · split
        · exact room.depth
        · exact (show 7≤80 by decide).trans room.base
  · intro j
    change (src.roleRow H v j).work≤limit
    unfold roleRow
    cases finSumFinEquiv.symm j with
    | inl a=>
      dsimp only [Sum.elim_inl]
      cases (finSumFinEquiv.symm a : Fin (DescentRotorWindowArchive.count D (2^r) cap)⊕Fin 1) with
      | inl wire=>exact src.matrixRow_work room H wire
      | inr _=>exact room.capacity
    | inr flag=>
      dsimp only [Sum.elim_inr]
      split
      · exact room.depth
      · exact (show 7≤80 by decide).trans room.base

end
end Hierarchy.DescentFallbackPeriod.Projected.RootSources

namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentPackedWalsh DescentPackedColony DescentPlainTerminal.Suffix DescentPackedColony.Phase.Arena
open DescentSixParty DescentSixParty.Chronology DescentResetGates DescentSharedLeafLookup DescentSIMDLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D cap N n r c H G K R M h₀ l t field Ht w h bit : ℕ}
    (a : Receiver D cap N n r c H G K R M h₀ l t field Ht w) (E : EstimatorArena)
    (stencil : StencilBook) (old : StencilBook.Sources) (stencilBase splitBank hubWidth : ℕ)
    (peers : Ports D) (oldId : Bank) (priorCapacity : Expr) (f fee full total portPitch : ℕ)
    (board : NonlinearExpanders.Graph n h) (packet C groupDigits batches layerBits factor : ℕ)
    (primitive : CanonicalTag (2^n)→Cell bit) (bookPage : RootPage r (2^n))
local notation "L" => 2^r
local notation "groups" => 2^c
local notation "prev" => a.issuedSources E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity f fee full total portPitch
local notation "B" => a.issuedBook E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
  f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage

def readWork (dimension : ℕ) (count cap : Expr) := 400+23*dimension+count.work+cap.work

local notation "src" => a.atlasSources E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
  f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage

theorem atlas_source_work : (src).OperandWork (readWork stencil.m old.count priorCapacity) := by
  constructor
  · unfold readWork;omega
  · intro i j
    have prior:=stencil.order_work old stencilBase splitBank hubWidth i.val j.val
    change (stencil.orderExpr old stencilBase splitBank hubWidth i.val j.val).work+5≤_
    unfold readWork
    omega
  · intro i j u
    apply (ClosedReset.Recorded.reservationFields_work E _ peers H portPitch c (E.dim-c) _
      (Nat.clog 2 (E.dim+2)) total (.lookup oldId .row) i j u).trans
    simp only [Expr.work,readWork];omega
  · change (DescentRotorPeerIssue.broadcast _ _ priorCapacity).work≤_
    simp only [DescentRotorPeerIssue.broadcast,Expr.work,readWork];omega
  · dsimp only [atlasSources,issuedSources,rootSources,DescentRotorPeerIssue.broadcast,PortLevels.AddressBook.levelAt,
      Cutoff.level,Expr.work,readWork]
    omega


theorem issued_matrix_work (H₁ : ℕ) : ∀j,((src).matrixRow H₁ j).work≤readWork stencil.m old.count priorCapacity :=
  (src).matrixRow_work (a.atlas_source_work E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
    f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage) H₁

/-- The earlier source family prior to replacing the reservation and original-order slots. -/
theorem original_matrix_work (H₁ : ℕ) : ∀j,((prev).matrixRow H₁ j).work≤readWork stencil.m old.count priorCapacity := by
  apply (prev).matrixRow_work _ H₁
  constructor
  · unfold readWork;omega
  · intro i j
    have prior:=stencil.order_work old stencilBase splitBank hubWidth i.val j.val
    change (stencil.orderExpr old stencilBase splitBank hubWidth i.val j.val).work≤_
    unfold readWork
    omega
  · intro i j u
    change 1≤_
    unfold readWork;omega
  · change (DescentRotorPeerIssue.broadcast _ _ priorCapacity).work≤_
    simp only [DescentRotorPeerIssue.broadcast,Expr.work,readWork];omega
  · dsimp only [issuedSources,rootSources,DescentRotorPeerIssue.broadcast,PortLevels.AddressBook.levelAt,
      Cutoff.level,Expr.work,readWork]
    omega

/-- Every finite source operator in the authentic root book, including the cost of looking
up the original GL order and the measured capacity reservation at its actual address. -/
theorem issued_read_work (p : RootPage r (2^n)) :
    ∀j,(((B).table p).2.reads j).work≤readWork stencil.m old.count priorCapacity := by
  let pair:=fun table hdr=>ClosedReset.Recorded.reservationFields E hdr peers H portPitch c (E.dim-c)
    table (Nat.clog 2 (E.dim+2)) total (.lookup oldId .row)
  let visible := src
  have bound := a.atlas_source_work E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
    f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage
  rcases p with ⟨s,(⟨v,k⟩|v)⟩
  · have eqn:=(prev).reserved_good (field:=field) board packet f Ht C groupDigits batches layerBits primitive
      H factor hubWidth old.roster old.hubs a.projectionEnd groups M stencil.n pair bookPage s v k
    change (B).good s v k=visible.good (field:=field) board packet f Ht C groupDigits batches layerBits primitive H s v k at eqn
    change ∀j,(((B).good s v k).2.reads j).work≤_
    rw [eqn]
    exact visible.good_work bound H board packet f Ht C groupDigits batches layerBits primitive s v k
  · intro j
    have eqn:=(prev).reserved_fallback_reads (field:=field) board packet f Ht C groupDigits batches layerBits primitive
      H factor hubWidth old.roster old.hubs a.projectionEnd groups M stencil.n pair bookPage s v j
    change ((B).exceptional s v).reads j=_ at eqn
    change (((B).exceptional s v).reads j).work≤_
    rw [eqn]
    exact (DescentFallbackPeriod.reads_work H visible.peers _ visible.self visible.tagged visible.sign 7
      (fun _=>le_refl _) (fun _ _=>le_refl _) (number.symm j)).trans (by
        calc max 7 80 = 80 := by decide
             _ ≤ _ := bound.base)

/-- The common scalar bound lifts directly to the generated gather of any issued page.
Its table addresses may be relocated by the root allocator without changing this bound. -/
theorem issued_assembly (p : RootPage r (2^n))
    (tables : Fin (((B).table p).1)→DescentPackedZip.Tables) :
    (DescentPacking.PackedMatch.Local.Gather.assembly tables ((B).table p).2.reads).work≤
      1+arityLimit D L cap n r*(readWork stencil.m old.count priorCapacity+11) := by
  have bound:=DescentPacking.PackedMatch.Local.Gather.collect_work tables ((B).table p).2.reads
    (List.finRange ((B).table p).1) (readWork stencil.m old.count priorCapacity)
    (a.issued_read_work E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity f fee full total portPitch
      board packet C groupDigits batches layerBits factor primitive bookPage p)
  have arity:=(a.issued_arity E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity f fee full total portPitch
    board packet C groupDigits batches layerBits factor primitive bookPage p).1
  exact (by simpa only [DescentPacking.PackedMatch.Local.Gather.assembly,List.length_finRange] using bound :
    (DescentPacking.PackedMatch.Local.Gather.assembly tables ((B).table p).2.reads).work≤
      1+((B).table p).1*(readWork stencil.m old.count priorCapacity+11)).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ arity) 1)

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
