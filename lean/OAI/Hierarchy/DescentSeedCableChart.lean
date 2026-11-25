import OAI.Hierarchy.DescentSeedSiteOrdinals
import OAI.Hierarchy.DescentSharedCableSerial

namespace OAI
/-! Copying a trivalent graph preserves the local serial of every original leg. -/
namespace Hierarchy.DescentPackedSeed.Signed
open DescentSeedRoot DescentInitialHost DescentSharedCableNames
open Computability.BorderVNP.Crossing Catalyst
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {k n R q : ℕ} (X : Approximation F k n)
local notation "N" => X.network.copyGraph
variable {H : Type} [DecidableEq H] (B : Ends H q)

structure Chart (R : ℕ) where
  vertex : Fin R × Vertex X ↪ H
  wire : Fin R × Cable X ≃ Fin q
  src : ∀j e,B.src (wire (j,e))=vertex (j,source N e)
  dst : ∀j e,B.dst (wire (j,e))=vertex (j,target N e)
  lt : ∀j e f, wire (j,e)<wire (j,f) ↔ index e< index f

namespace Chart
variable {X B} (C : Chart X B R)

omit [Field F] in
theorem peer (j : Fin R) (v : Vertex X) (e : Cable X) :
    B.peer (C.vertex (j,v)) (C.wire (j,e))=C.vertex (j,other X v e) := by
  simp only [Ends.peer,C.src,C.dst,EmbeddingLike.apply_eq_iff_eq,Prod.mk.injEq,true_and,other]
  split <;> rfl

omit [Field F] in
theorem parallel (j : Fin R) (v t : Vertex X) (e : Cable X) :
    B.serial (C.vertex (j,v)) (C.vertex (j,t)) (C.wire (j,e))=(earlier X v t e).card := by
  let push : Cable X ↪ Fin q := ⟨fun f=>C.wire (j,f),fun a b h=>congrArg Prod.snd (C.wire.injective h)⟩
  have eqn : B.earlier (C.vertex (j,v)) (C.vertex (j,t)) (C.wire (j,e))=(earlier X v t e).map push := by
    ext y
    obtain ⟨⟨a,f⟩,rfl⟩:=C.wire.surjective y
    simp only [Ends.earlier,Ends.parallel,earlier,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map,
      C.src,C.dst,EmbeddingLike.apply_eq_iff_eq,Prod.mk.injEq]
    constructor
    · rintro ⟨hit,less⟩
      obtain rfl : a=j:=hit.elim (fun h=>h.1.1) (fun h=>h.1.1)
      exact ⟨f,⟨hit.imp (fun h=>⟨h.1.2,h.2.2⟩) (fun h=>⟨h.1.2,h.2.2⟩),(C.lt ..).mp less⟩,rfl⟩
    · rintro ⟨g,⟨hit,less⟩,eqn⟩
      change C.wire (j,g)=C.wire (a,f) at eqn
      obtain ⟨rfl,rfl⟩:=Prod.mk.inj (C.wire.injective eqn)
      exact ⟨hit.imp (fun h=>⟨⟨rfl,h.1⟩,rfl,h.2⟩) (fun h=>⟨⟨rfl,h.1⟩,rfl,h.2⟩),(C.lt ..).mpr less⟩
  change (B.earlier _ _ _).card=_
  rw [eqn,Finset.card_map]

omit [Field F] in
theorem serial (j : Fin R) (v : Vertex X) (e : Cable X) :
    B.serial (C.vertex (j,v)) (B.peer (C.vertex (j,v)) (C.wire (j,e))) (C.wire (j,e))=seedParallel X v e := by
  rw [C.peer];exact C.parallel j v (other X v e) e

end Chart
end
end Hierarchy.DescentPackedSeed.Signed

/-! The two signed seed sockets of a loop share their chronological incident rank. -/
namespace Hierarchy.DescentPackedSeed.Signed
open DescentSeedRoot DescentInitialHost DescentSharedCableNames
open Computability.BorderVNP.Crossing Catalyst
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {k n R q cap : ℕ} (X : Approximation F k n)
local notation "N" => X.network.copyGraph

variable {H : Type} [DecidableEq H] (B : Ends H q)

theorem position_card (fit : ∀h,(B.incident h).card≤cap) (h : H) (y : ↥(B.incident h)) :
    (B.position fit h y).val=((B.incident h).filter (·<y.val)).card := by
  let ord:=B.ordinal h
  change (ord y).val=_
  rw [←Fin.card_Iio (ord y)]
  symm
  apply Finset.card_bij (fun f hf=>ord ⟨f,(Finset.mem_filter.mp hf).1⟩)
  · intro f hf;exact Finset.mem_Iio.mpr (ord.strictMono (Finset.mem_filter.mp hf).2)
  · intro f _ g _ eqn;exact congrArg Subtype.val (ord.injective eqn)
  · intro i hi
    exact ⟨(ord.symm i).val,Finset.mem_filter.mpr ⟨(ord.symm i).property,
      (ord.lt_iff_lt).mp (by simpa using Finset.mem_Iio.mp hi)⟩,ord.apply_symm_apply i⟩

namespace Chart
variable {X B} (C : Chart X B R)

omit [Field F] in
theorem position_eq (fit : ∀h,(B.incident h).card≤cap) (j : Fin R) (v : Vertex X) (e : Cable X)
    (atEnd : C.wire (j,e)∈B.incident (C.vertex (j,v))) :
    (B.position fit _ ⟨_,atEnd⟩).val=position X v e := by
  rw [position_card]
  let embed : Cable X ↪ Fin q := ⟨fun f=>C.wire (j,f),fun a b h=>congrArg Prod.snd (C.wire.injective h)⟩
  have earlier_mem (f : Cable X) : f ∈ earlierAt X v e ↔
      (source X.network.copyGraph f = v ∨ target X.network.copyGraph f = v) ∧ index f < index e := by
    change f ∈ earlierAt X v e ↔ present X v f ∧ index f < index e
    exact (@Finset.mem_filter (Cable X) (fun a => present X v a ∧ index a < index e)
      _ Finset.univ f).trans ⟨And.right, fun h => ⟨Finset.mem_univ f, h⟩⟩
  have eqn : ((B.incident (C.vertex (j,v))).filter (·<C.wire (j,e)))=(earlierAt X v e).map embed := by
    ext y
    obtain ⟨⟨a,f⟩,rfl⟩:=C.wire.surjective y
    simp only [Ends.incident,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map,
      C.src,C.dst,EmbeddingLike.apply_eq_iff_eq,Prod.mk.injEq]
    constructor
    · rintro ⟨hit,less⟩
      obtain rfl : a=j:=hit.elim And.left And.left
      exact ⟨f, (earlier_mem f).2 ⟨hit.imp And.right And.right, (C.lt ..).mp less⟩, rfl⟩
    · rintro ⟨g, member, eqn⟩
      obtain ⟨hit, less⟩ := (earlier_mem g).1 member
      change C.wire (j,g)=C.wire (a,f) at eqn
      obtain ⟨rfl,rfl⟩:=Prod.mk.inj (C.wire.injective eqn)
      exact ⟨hit.imp (fun h=>⟨rfl,h⟩) (fun h=>⟨rfl,h⟩),(C.lt ..).mpr less⟩
  rw [eqn,Finset.card_map]
  rfl
end Chart

end
end Hierarchy.DescentPackedSeed.Signed

end OAI
