import OAI.Computability.BorderVNP.PackedFrozenBirthCompile
import OAI.Computability.BorderVNP.PackedFrozenTapeRound

/-! # Main birth section at the actual coded directory keys

The directory's static injection can assign an arbitrary binary key to each
physical row. The owner circuit emits that key directly, and the same field
pins still give the true main birth section in source order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.Birth

open Crossing Shortening Shortening.StaticRows Shortening.SeedIntervals Shortening.CombiningStep
open InheritedProfile BankSite BankJoint ParseBatchSort VPVNP.VerifierNetwork CellAddressCircuit CellAddressPhysical
open CellSparse ParseBatchCounts
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m) (first : Fin D × Bool)
    {S : Type} [Fintype S] {n s d w : ℕ} (seed : S ↪ Fin n) (code : Fin (siteCapacity e s n) ↪ Fin (2^d))
    {σ : Type*} [Fintype σ] (packet : Frame σ (S × Output e first × Fin w))

private noncomputable def codedLiteral (r : Row e first S) : Unit ⊕ Fin d → Bool
  | .inl _ => true
  | .inr b => (numberWords d).symm (code (slot e seed s r.1)) b

/-- Constant directory keys and direct wiring of the already compiled seed
packet words. The source packet frame is shared by all the output rows. -/
noncomputable def codedFrame : Frame σ (Pins (Row e first S) (S × Output e first × Fin w) d) :=
  let keys := (Frame.initial (id : σ → σ)).step fun r : Row e first S × (Unit ⊕ Fin d) =>
    .const (codedLiteral e first seed code r.1 r.2)
  parallelFrame keys packet

/-- A constant flag and fixed-width key for each native row. -/
theorem codedFrame_size : (codedFrame e first seed code packet).size ≤
    Fintype.card (Row e first S)*(1+d)+packet.size := by
  have h := Frame.step_size_le (Frame.initial (id : σ → σ))
    (fun r : Row e first S × (Unit ⊕ Fin d) => StatementCircuit.Expr.const (codedLiteral e first seed code r.1 r.2))
    1 (fun _ => le_rfl)
  simp only [Frame.initial_size,zero_add,Fintype.card_prod,Fintype.card_sum,Fintype.card_unit,Fintype.card_fin,mul_one] at h
  unfold codedFrame
  rw [parallelFrame_size]
  exact Nat.add_le_add_right h _

private theorem coded_active (x : σ → Bool) (r : Row e first S) :
    (codedFrame e first seed code packet).eval x (.inl (r,.inl ())) = true := by
  simp [codedFrame,codedLiteral,StatementCircuit.Expr.eval]

/-- This row's enable and owner name are the actual ones in the physical directory. -/
theorem coded_owner (x : σ → Bool) (r : Row e first S) :
    owner ((codedFrame e first seed code packet).eval x) r = (code (slot e seed s r.1)).val := by
  simp [owner,codedFrame,codedLiteral,StatementCircuit.Expr.eval,value_encode]

private theorem coded_at (x : σ → Bool) (key : Fin (siteCapacity e s n)) :
    (schema e first S w).atSite ((codedFrame e first seed code packet).eval x) (code key).val =
      (schema e first S w).atSite ((frame (d := d) e first seed s packet).eval x) key.val := by
  have fit : siteCapacity e s n ≤ 2^d := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective code code.injective
  rw [Schema.atSite,Schema.atSite]
  apply List.filterMap_congr
  intro r _
  have h : (schema e first S w).read ((codedFrame e first seed code packet).eval x) r =
      (schema e first S w).read ((frame (d := d) e first seed s packet).eval x) r := by
    simp only [Schema.read,codedFrame,frame,parallelFrame_eval_inr]
  simp only [coded_active,active,coded_owner,owner_value e first seed s packet fit,true_and,Fin.val_inj,
    code.injective.eq_iff,h]

variable [NeZero D] {P : Type} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
    (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S) (positive : p.layout.Edge → Bool)
    (q : Counts e p bin perm) (oldSite : p.layout.Site ↪ Fin s) {ne np : ℕ}
    (edgeID : (output e p bin perm positive first q).layout.Edge ↪ Fin ne) (portID : P ↪ Fin np)

/-- The immutable seed packets form the exact main section on all real sewn
sites, with no live owner outside the directory's physical image. -/
theorem successor_section (x : σ → Bool)
    (words : ∀ a (z : Output e first), value (fun j => packet.eval x (a,z,j)) =
      (Packet.fieldList Packet.record (emitted e first (relativeRaw e p bin perm positive first q a edgeID portID)
        z.1))[z.2.val]?.getD 0) :
    (schema e first S w).Section ((codedFrame e first seed code packet).eval x)
      ((siteRows e p oldSite seed).trans (code.trans Fin.valEmbedding))
      (birthRows e p bin perm positive first q edgeID portID) := by
  have fit : siteCapacity e s n ≤ 2^d := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective code code.injective
  constructor
  · intro r _ _
    exact ⟨.inr ⟨r.1.1,r.1.2⟩,coded_owner e first seed code packet x r⟩
  · rintro (v|⟨a,v⟩)
    · exact (coded_at e first seed code packet x _).trans (at_old e first seed s packet fit x p oldSite v)
    · exact (coded_at e first seed code packet x _).trans
        (at_seed e first seed s packet fit x _ words a v)

section Compile

variable {k u C h : ℕ} (F : Fields (siteCapacity e s n) (edgeCapacity e k n) u C d h w σ)
    (counts : Frame σ (S × Option (Fin e.count) × Fin w))

/-- A single finite circuit, chosen before the geometry and histogram, realizes
the complete main section at the keys stored in the actual public field frame. -/
theorem exists_mainSection (hm : 0 < m) :
    ∃ f : Frame σ (Pins (Row e first S) (S × Output e first × Fin w) d),
      f.size ≤ Fintype.card (Row e first S)*(1+d) + (counts.size+(Views.frame F).size+6+Fintype.card S *
        ((adjustNodes e + BankCircuit.headerNodes D e.count m + PaidBox.nodeBound e + nodes e first) * (100*(w+1)^2))) ∧
      ∀ {P : Type} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K) (bin : p.layout.Edge → Option S)
        (perm : Fin D → Equiv.Perm S) (positive : p.layout.Edge → Bool) (q : Counts e p bin perm)
        (oldSite : p.layout.Site ↪ Fin s) (oldEdge : p.layout.Edge ↪ Fin k) (portID : P ↪ Fin u),
        let G := (output e p bin perm positive first q).layout
        let site := siteRows e p oldSite seed
        let edge := outputRows e p bin perm positive first q oldEdge seed
        ∀ (cell : G.Site → Fin C) (aux : G.Site → ℕ) (x : σ → Bool), Represents G cell aux site edge portID F x →
          (∀ a i, value (fun j => counts.eval x (a,i,j)) = i.elim (blocks p.layout bin perm m a) (q a).val) →
          ∀ (prior payload : p.layout.Site → ℕ) (M : ℕ),
          (∀ c, localRecords G true (Sum.elim prior (fun _ => 0))
            (Sum.elim payload (fun z => bankUses e (blocks p.layout bin perm m z.1) (q z.1).val z.2))
            (fun v => cell v = c) ≤ M) →
          addressCoefficient e first * (BankCharges.bound e * M + M + 1) < 2^w →
          (schema e first S w).Section (f.eval x) (site.trans (F.sites.trans Fin.valEmbedding))
            (birthRows e p bin perm positive first q edge portID) := by
  obtain ⟨packets,hsize,hword⟩ := exists_seedPackets e first hm seed F counts
  refine ⟨codedFrame e first seed F.sites packets,
    (codedFrame_size e first seed F.sites packets).trans (Nat.add_le_add_left hsize _),?_⟩
  intro P _ bits p bin perm positive q oldSite oldEdge portID G site edge cell aux x rep hist prior payload M cap room
  exact successor_section e first seed F.sites packets p bin perm positive q oldSite edge portID x
    (hword p bin perm positive q oldSite oldEdge portID cell aux x rep hist prior payload M cap room)

end Compile

end Packing.Inherited.FrozenTape.Birth

end BorderVNP
end Computability
end OAI
