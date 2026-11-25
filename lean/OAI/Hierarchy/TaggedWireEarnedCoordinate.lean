import OAI.Hierarchy.TaggedWireEarnedLoad
import OAI.Hierarchy.ProbeColumnAccounts

namespace OAI
/-! # The stock and paid coordinates of the original installation -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard AdaptiveProbe Strip WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph Probe ChosenPackets RowRouting StripPaths PacketTurns
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped Classical Fin.CommRing
variable {sam : PurchaseSampler} {h d k n K w : ℕ} {A B Ball : Type} [Fintype A] [Fintype B] [Fintype Ball]
local notation "C" => TreeColumn n
local notation "X" => TreeSite n k
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "T" => TreeLink n k
local notation "U" => R⊕T
local notation "G" => Commodity (Fin (2^h)) (Stages h d) k
local notation "shift" => Fintype.card G
variable {p : StripPorts sam h d k (TreeColumn n) (Fin n) B} {b : Board} {π : Equiv.Perm (Fin (2^h))}
    {extra : A⊕B→DistinctPair (TreeSite n k)} {place : Ball×TreeSite n k↪Fin K} {u : Ball}
    {endRow : Fin b.rows→Site h d k×Site h d k} {name : Site h d k↪Fin K} {pad : Chord K}
    {addr : A → Commodity (Fin (2^h)) (Stages h d) k} {m : Memory w} {reg : Word w}
local notation "roles" => ColumnWires.ends (horizontal n) extra
local notation "own" => Sum.elim (reportedRole place roles u) (reportedRole place (treeEnds n k) u)
local notation "phys" => installedRows π endRow name pad
local notation "enum" => treeFirst R T
local notation "order" => (Fintype.equivFin ((i : Fin (Fintype.card U)) × Fin (menuLen (enum i)))).symm

namespace EarnedInstall
variable (g : EarnedInstall p b π extra place u endRow name addr m reg)

local notation "old" => retained (b:=b) addr
local notation "fwd" => Fin.natAdd shift
local notation "pr" => primaryRow (b:=b) old fwd g.index
local notation "ma" => (fun c j=>fwd (g.mate c j))
local notation "tr" => (fun j:T=>fwd (g.index (treeRole n k j)))
local notation "walk" => Sum.elim (links (horizontal n) extra place u pr ma) (fun j:T=>[tr j]) ∘ enum

variable {F J : Type} [Field F] [Fintype J] (labels : TreeSite n k≃Fin (Fintype.card (TreeSite n k))) (req : J → ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k)
    (rt : Fin (Fintype.card (TreeSite n k))) (P : Packet F (fun e=>@DistinctPair.chord _ _ ⟨labels⟩ (ColumnWires.ends (Strip.horizontal n) extra e)) req)
    (copies : ℕ)
local notation "row" => Row.packet (stripPacket labels roles req place u rt P) copies

variable (pad : Chord K)
local notation "chosen" => g.tender labels req rt P copies pad
open scoped BigOperators


variable (hist : Histogram (Fin P.terms) copies)
local notation "amt" => histWidth P.count hist
local notation "st" => g.placed.2.choose_spec.choose_spec

private theorem differentBanks {g n : ℕ} (a : Fin g) (e : Fin n) :
    stockRow (p:=n) a≠Fin.natAdd g e := by
  intro same
  exact Sum.inl_ne_inr ((@finSumFinEquiv g n).injective same)

private theorem shiftedInjective {g n : ℕ} : Function.Injective (Fin.natAdd g : Fin n→Fin (g+n)) := by
  intro a b same
  exact Sum.inr.inj ((@finSumFinEquiv g n).injective same)

/-- Every occurrence pointing to this global input contributes its width,
including distinct local requests sharing the same inventory address. -/
theorem tender_stock (i : G) :
    (chosen).install.load ((chosen).bits hist) (stockRow (p:=b.rows) (stockOrder h d k i)) =
      ∑r : R, if ColumnWires.account addr r=some i then amt r else 0 := by
  let target := stockRow (p:=b.rows) (stockOrder h d k i)
  have disjoint (e : Fin b.rows) : fwd e ≠ target := (differentBanks (stockOrder h d k i) e).symm
  have slot (a : A) : old a=target ↔ addr a=i := by
    change finSumFinEquiv (m:=shift) (n:=b.rows) (Sum.inl (stockOrder h d k (addr a)))=
      finSumFinEquiv (Sum.inl (stockOrder h d k i)) ↔ addr a=i
    constructor
    · exact fun same=>(stockOrder h d k).injective (Sum.inl.inj (finSumFinEquiv.injective same))
    · exact fun same=>congrArg (fun z=>stockRow (p:=b.rows) (stockOrder h d k z)) same
  have first (r : R) : (if pr r=target then amt r else 0) =
      if ColumnWires.account addr r=some i then amt r else 0 := by
    cases r with
    | catalyst c j => simp [primaryRow,ColumnWires.account,disjoint]
    | radius c j side => simp [primaryRow,ColumnWires.account,disjoint]
    | cross c axes left right => simp [primaryRow,ColumnWires.account,disjoint]
    | horizontal e l => simp [primaryRow,ColumnWires.account,disjoint]
    | extra t => cases t with
      | inl a => simp [primaryRow,ColumnWires.account,slot a]
      | inr y => simp [primaryRow,ColumnWires.account,disjoint]
  rw [g.tender_load labels req rt P copies pad hist target]
  simp only [first,disjoint,ite_false,Finset.sum_const_zero,Nat.add_zero]
  refine (congrArg (fun z : ℕ=>(∑r : R, if ColumnWires.account addr r=some i then amt r else 0)+z) ?_).trans (Nat.add_zero _)
  apply Finset.sum_eq_zero
  intro r _
  cases r <;> rfl

/-- Primary paid lanes, the opposite catalyst radius, and the selector tree
are charged separately to the same original permanent-edge coordinate. -/
theorem tender_paid (e : Fin b.rows) :
    (chosen).install.load ((chosen).bits hist) (paidRow (g:=shift) e) =
      (∑r : R,if paidRole r ∧ g.index r=e then amt r else 0)+
      (∑r : R,match r with
        | .catalyst c j => if g.mate c j=e then amt r else 0
        | _ => 0)+
      (∑j : T,if g.index (treeRole n k j)=e then copies*P.selectorBits else 0) := by
  have first (r : R) : (if pr r=fwd e then amt r else 0) =
      if paidRole r ∧ g.index r=e then amt r else 0 := by
    have hit := paid_primary_count b old fwd g.index r e shiftedInjective
      (fun a j=>differentBanks (stockOrder h d k (addr a)) j)
    simpa only [ite_mul,one_mul,zero_mul] using congrArg (fun z : ℕ=>z*amt r) hit
  change (chosen).install.load ((chosen).bits hist) (fwd e)=_
  rw [g.tender_load labels req rt P copies pad hist (fwd e)]
  simp only [first,shiftedInjective.eq_iff]
  refine congrArg₂ Nat.add (congrArg₂ Nat.add rfl ?_) rfl
  apply Finset.sum_congr rfl
  intro r _
  cases r <;> rfl

/-- In each case the paid coordinate is the actual protected word of the
original CT row. The inventory case makes no paid contribution. -/
theorem tender_paid_read (e : Fin b.rows) :
    (chosen).install.load ((chosen).bits hist) (paidRow (g:=shift) e) =
      (∑r : R,if paidRole r ∧ ((p.primary b r).eval m reg).val=e.val then amt r else 0)+
      (∑r : R,match r with
        | .catalyst c j => if ((p.mate b (.catalyst c j:R)).eval m reg).val=e.val then amt r else 0
        | _ => 0)+
      (∑j : T,if ((p.primary b (treeRole n k j:R)).eval m reg).val=e.val then copies*P.selectorBits else 0) := by
  have primary (r : R) : (paidRole r ∧ g.index r=e) ↔ paidRole r ∧ ((p.primary b r).eval m reg).val=e.val := by
    apply and_congr_right
    intro on
    rw [(st).1 r on]
    exact Fin.ext_iff
  have opposite (c : C) (j : Fin k) : g.mate c j=e ↔ ((p.mate b (.catalyst c j:R)).eval m reg).val=e.val := by
    rw [(st).2.1 c j]
    exact Fin.ext_iff
  have treeHit (j : T) : g.index (treeRole n k j)=e ↔ ((p.primary b (treeRole n k j:R)).eval m reg).val=e.val := by
    have paid : paidRole (treeRole n k j:R) := by rcases j with a|⟨c,a,t⟩ <;> trivial
    rw [(st).1 _ paid]
    exact Fin.ext_iff
  have mate (r : R) : (match r with
      | .catalyst c j=>if g.mate c j=e then amt r else 0
      | _=>0)=(match r with
      | .catalyst c j=>if ((p.mate b (.catalyst c j:R)).eval m reg).val=e.val then amt r else 0
      | _=>0) := by cases r <;> simp only [opposite]
  rw [g.tender_paid labels req rt P copies pad hist e]
  simp only [primary,mate,treeHit]

/-- Equality of native stock words tests the actual commodity identity when
its inventory fits the word. Repeated local demands are included individually. -/
theorem tender_stock_read (i : G) (stock : A→Expr)
    (room : PurchaseInventory.footprint h (Stages h d) k≤2^w)
    (held : ∀a,(stock a).eval m reg=(PurchaseInventory.slot (addr a):Word w)) :
    (chosen).install.load ((chosen).bits hist) (stockRow (p:=b.rows) (stockOrder h d k i)) =
      ∑r : R,if ColumnWires.account (fun a=>((stock a).eval m reg).val) r=some (PurchaseInventory.slot i)
        then amt r else 0 := by
  rw [g.tender_stock labels req rt P copies pad hist i]
  apply Finset.sum_congr rfl
  intro r _
  cases r with
  | catalyst c j => simp [ColumnWires.account]
  | radius c j side => simp [ColumnWires.account]
  | cross c axes l r => simp [ColumnWires.account]
  | horizontal h l => simp [ColumnWires.account]
  | extra t => cases t with
    | inr x => simp [ColumnWires.account]
    | inl a =>
      simp only [ColumnWires.account,Option.some.injEq,held,
        Fin.val_cast_of_lt ((PurchaseInventory.slot_lt (addr a)).trans_le room),PurchaseInventory.slot_injective.eq_iff]

end EarnedInstall
end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
