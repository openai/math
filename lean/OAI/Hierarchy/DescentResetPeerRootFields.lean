import OAI.Hierarchy.DescentIssuedGoodHeaders
import OAI.Hierarchy.DescentFallbackPeriodRun
import OAI.Hierarchy.DescentResetPrivatePeerChip

namespace OAI
/-! # The same five private edge fields at the public and measured layer precisions -/
namespace Hierarchy.DescentSixParty.ResetInput
open DescentColonies DescentResetHostSize DescentResetCableSlots DescentSIMDLookup
open DescentPackedPrivateMenu DescentResetPeerUnionRAM
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {price ε : ℝ} {h C Ht H field count layer slots : ℕ} (Z : ResetInput W price ε h C Ht)
  (T : Z.Terminals) (vertex : Z.V↪Fin H) (unit : 0 < Z.unit)
local notation "r" => Z.k-T.commonDepth
local notation "X" => Z.placement

/-- The public layer field is allowed to be wider or narrower than the bound used by
the semantic reset. Both encodings publish the same natural layer count on every live root. -/
theorem good_root_fields (s : Bool) (arr : Z.Fallback→DescentPackedFallbackTree.Panel Ht count)
    (v : Z.V) (hi : Block T.commonDepth) (t : Code r) (f : ℕ) (x : Fin 3→Cell field)
    (status : ((x 1).val=t.val.1+1 ∧ (x 2).val%2=0) ↔
      ∃g : (X).Good,Z.rootVertex T (.inl g)=v ∧ Z.rootBlock T (.inl g)=hi ∧ Z.goodLabel T g=t)
    (layers : ∀g : (X).Good,Z.rootVertex T (.inl g)=v → Z.rootBlock T (.inl g)=hi → Z.goodLabel T g=t →
      (Z.circuit s g).layers=DescentRecordedRotorLayers.layers Z.n Z.width f (x 0).val ∧
      (Z.circuit s g).layers < 2^layer) (j : Fin slots) :
    PrivateEvidence.frame (fieldBits Z.graph r Ht count layer C Z.width) slots j
      (DescentIssuedGoodHeaders.compactHeaders Z.graph Z.width f Ht count layer C slots s t x)=
    values Z.graph r Ht count Z.layerBits C Z.width s j.val (Z.rootsOf T vertex unit s arr (.inl t) (vertex v) hi) := by
  let hit:=((x 1).val=t.val.1+1 ∧ (x 2).val%2=0)
  have one : (1 : Fin 2)≠0:=by decide
  by_cases active : hit
  · obtain ⟨g,host,block,tag⟩:=status.mp active
    have equalKey:=Z.rootsOf_read T vertex unit s arr (.inl g)
    change Z.rootsOf T vertex unit s arr (.inl (Z.goodLabel T g)) (vertex (Z.rootVertex T (.inl g)))
      (Z.rootBlock T (.inl g))=Z.rotorKey T unit count s g at equalKey
    rw [host,block,tag] at equalKey
    rw [equalKey]
    have ⟨issued,fits⟩:=layers g host block tag
    funext a
    simp only [PrivateEvidence.frame,DescentIssuedGoodHeaders.compactHeaders,DescentIssuedGoodHeaders.headers,
      cell_read,DescentIssuedGoodHeaders.key,ite_eq_right one]
    rw [ite_eq_left active]
    change DescentPackedRotorPanel.fields Z.graph r Ht C Z.width s j.val (interval r t).val
      (DescentRecordedRotorLayers.layers Z.n Z.width f (x 0).val%2^layer) a=_
    rw [←issued,Nat.mod_eq_of_lt fits,←tag]
    rfl
  · have absent : Z.atRoot T vertex (vertex v,hi,.inl t)=none := by
      apply (Z.empty_at T vertex _).2
      rintro (g|b) same
      · have host:=vertex.injective (congrArg Prod.fst same)
        have block:=congrArg (fun x=>x.2.1) same
        have label:=Sum.inl.inj (congrArg (fun x=>x.2.2) same)
        exact active (status.mpr ⟨g,host,block,label⟩)
      · have mismatch := congrArg (fun x => x.2.2) same
        exact Sum.inr_ne_inl mismatch
    funext a
    simp only [PrivateEvidence.frame,DescentIssuedGoodHeaders.compactHeaders,DescentIssuedGoodHeaders.headers,
      cell_read,DescentIssuedGoodHeaders.key,ite_eq_right one,rootsOf,absent]
    rw [ite_eq_right active]
    rfl

/-- Enlarging the previous-host rectangle preserves the complete incidence test at
every original or padded host in the smaller rectangle. -/
theorem empty_root_reindex {N : ℕ} (embed : Fin H↪Fin N) (v : Fin H) (hi : Block T.commonDepth)
    (t : Z.RootTicket T) : Z.atRoot T (vertex.trans embed) (embed v,hi,t)=none ↔
      Z.atRoot T vertex (v,hi,t)=none := by
  rw [Z.empty_at,Z.empty_at]
  constructor
  · intro larger q small
    exact larger q (congrArg (fun x : Fin H×Block T.commonDepth×Z.RootTicket T=>(embed x.1,x.2)) small)
  · intro smaller q large
    have left : embed (vertex (Z.rootVertex T q))=embed v:=congrArg Prod.fst large
    have right := congrArg (fun x : Fin N × Block T.commonDepth × Z.RootTicket T => x.2) large
    exact smaller q (Prod.ext (embed.injective left) right)

/-- Classify a fallback root in the actual host rectangle, including holes. The two
observations are exactly the occupied and empty key reads of the gathered fallback packet. -/
theorem fall_root_key {L cap degree : ℕ} (s : Bool)
    (arr : Z.Fallback→DescentPackedFallbackTree.Panel Ht (L*(2*cap)))
    (observed : (Code r×Option (Fin (2^Z.n)))→Z.V→Block T.commonDepth→DescentFallbackPeriod.Packet degree L cap Z.n r field)
    (live : ∀b : Z.Fallback,DescentFallbackPeriod.key (Ht:=Ht) (l:=Z.layerBits) s
      (Z.fallLabel T b,(T.code b).2.2) (observed (Z.fallLabel T b,(T.code b).2.2) (Z.rootVertex T (.inr b)) (Z.rootBlock T (.inr b)))=
      Z.fallbackKey T s b (arr b))
    (blank : ∀v hi t,Z.atRoot T vertex (vertex v,hi,.inr t)=none →
      DescentFallbackPeriod.key (Ht:=Ht) (l:=Z.layerBits) s t (observed t v hi)=none)
    (v : Z.V) (hi : Block T.commonDepth) (t : Code r×Option (Fin (2^Z.n))) :
    DescentFallbackPeriod.key (Ht:=Ht) (l:=Z.layerBits) s t (observed t v hi)=
      Z.rootsOf T vertex unit s arr (.inr t) (vertex v) hi := by
  by_cases ready : ∃q,Z.rootLocation T vertex q=(vertex v,hi,.inr t)
  · obtain ⟨(g|b),pos⟩:=ready
    · have mismatch := congrArg (fun x => x.2.2) pos
      exact False.elim (Sum.inl_ne_inr mismatch)
    · have host:=vertex.injective (congrArg Prod.fst pos)
      have block:=congrArg (fun x=>x.2.1) pos
      have tag:=Sum.inr.inj (congrArg (fun x=>x.2.2) pos)
      change Z.rootVertex T (.inr b)=v at host
      change Z.rootBlock T (.inr b)=hi at block
      change (Z.fallLabel T b,(T.code b).2.2)=t at tag
      subst v; subst hi; subst t
      exact (live b).trans (Z.rootsOf_read T vertex unit s arr (.inr b)).symm
  · have absent : Z.atRoot T vertex (vertex v,hi,.inr t)=none :=
      (Z.empty_at T vertex _).2 (fun q h=>ready ⟨q,h⟩)
    simp only [rootsOf,absent]
    exact blank v hi t absent

/-- Read all five digits at the layer precision of the fixed compiled root book. -/
theorem fall_root_fields {L cap degree : ℕ} (s : Bool)
    (arr : Z.Fallback→DescentPackedFallbackTree.Panel Ht (L*(2*cap)))
    (v : Fin H) (hi : Block T.commonDepth) (t : Code r×Option (Fin (2^Z.n)))
    (packet : DescentFallbackPeriod.Packet degree L cap Z.n r field)
    (read : DescentFallbackPeriod.key (Ht:=Ht) (l:=Z.layerBits) s t packet=
      Z.rootsOf T vertex unit s arr (.inr t) v hi) (j : Fin slots) :
    PrivateEvidence.frame (fieldBits Z.graph r Ht (L*(2*cap)) layer C Z.width) slots j
      (DescentFallbackPeriod.law Z.graph r Ht layer C Z.width slots s t (DescentFallbackPeriod.encodePacket packet))=
    values Z.graph r Ht (L*(2*cap)) Z.layerBits C Z.width s j.val (Z.rootsOf T vertex unit s arr (.inr t) v hi) := by
  funext a
  rw [PrivateEvidence.frame,DescentFallbackPeriod.law,DescentFallbackPeriod.packet_encode,cell_read,
    DescentFallbackPeriod.layer_free (Ht:=Ht) Z.graph C Z.width layer Z.layerBits j.val s t packet a,read]

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
