import OAI.Hierarchy.ProtocolRAMCatalystLayoutTypes
import OAI.Hierarchy.ProtocolRAMTerminalSinkSpace
import OAI.Hierarchy.ProtocolRAMCatalogueRowBounds
import OAI.Hierarchy.ProtocolRAMRowChoiceFits

namespace OAI
/-! # Native terminal memory for the original paid catalogue and both route passes -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive.TerminalLayout
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe Calendar Calendar.CoreRoute Calendar.CatalogueRows
open scoped Classical Fin.CommRing

def footprint (c : Mesh) (A : Arena) (stock : Bank) (ownerStride edges r count n : ℕ) :=
  A.endAddress c + stock.base+stock.size + (events c).length*ownerStride+edges+2*r+count+2*n+1

def pageBits (c : Mesh) (A : Arena) (stock : Bank) (ownerStride edges r count n : ℕ) :=
  (footprint c A stock ownerStride edges r count n).log2+1

def page (bits i : ℕ) : Bank := ⟨i*2^bits,bits⟩

def settlement (bits : ℕ) (stock : Bank) : RouteSettlement.Banks :=
  ⟨page bits 1,page bits 4,page bits 5,stock,page bits 6,page bits 7⟩

def reserve (start n bits : ℕ) : ReserveUse.Archive :=
  banks start n ⟨0,bits+2⟩ (8*2^bits)

def ownerArea (bits stride : ℕ) : Arena := ⟨2*2^bits,stride⟩

def source (bits : ℕ) := 9*2^bits
def table (bits : ℕ) := 10*2^bits
def destination (bits : ℕ) := 18*2^bits

private theorem bank_fit (b : Bank) {w out : ℕ} (wide : out<2^w) (enough : b.base+b.size≤out) :
    b.Fits w out := ⟨Nat.two_pow_pos _,by omega,enough⟩

private theorem packed_fit {w out : ℕ} (b : RouteSettlement.Banks) (cat : CatalogueRows.Board) (owners : Bank)
    (ow : owners.Fits w out) (bw : b.width.Fits w out) (geom : ∀i,(cat.geometry i).Fits w out) :
    (packed owners (RouteSettlement.fields b cat.geometry)).Fits w out := by
  apply BoughtSockets.choose_fits_bound
  · intro i
    apply CatalogueRows.fits_atRow
    · by_cases hit : i=4
      · subst i
        simp only [RouteSettlement.fields,Function.update_self]
        exact ⟨bw,trivial⟩
      · simpa only [RouteSettlement.fields,Function.update_of_ne hit] using geom i
    · exact ⟨ow,trivial⟩
  · exact ⟨trivial,trivial⟩

theorem static_below (start n r edges : ℕ) (A : Arena)
    (below : (sinkBank start n r edges).base+(sinkBank start n r edges).size≤A.first) :
    let p:=routeBanks start n r
    (∀f,(which p f).base+(which p f).size≤A.first) ∧
      start+2*2^((2*n).log2+1)≤A.first := by
  intro p
  let entries:=2^((2*n).log2+1)
  let routes:=2^((2*r).log2+1)
  let owners:=2^((8*edges).log2+1)
  change start+2*entries+2*routes+routes+owners ≤ A.first at below
  have operand := (Nat.le_add_right (start+2*entries+2*routes+routes) owners).trans below
  have mode := (Nat.le_add_right (start+2*entries+2*routes) routes).trans operand
  rw [two_mul routes, ← Nat.add_assoc] at mode
  have kind := (Nat.le_add_right (start+2*entries+routes) routes).trans mode
  constructor
  · intro f
    cases f with
    | kind => exact kind
    | mode => exact mode
    | operand => exact operand
  · exact (Nat.le_add_right (start+2*entries) routes).trans kind

/-- All scalar and input-bank obligations consumed by the strip settlement.
The geometry fields are the original catalogue expressions. -/
structure Ready (c : Mesh) (A : Arena) (L : OwnerLedger) (cat : CatalogueRows.Board)
    (z W k count n start bits w : ℕ) (stock : Bank) : Prop where
  archive : Room c A L (reserve start n bits) (settlement bits stock) count n w
  sink : SinkSpace (cat.sink (Fintype.card (Slots z (2^W) k)) (settlement bits stock) (source bits) (table bits) (destination bits)
    (sinkBank start n (Fintype.card (Slots z (2^W) k)) cat.rows)) w
  readers : (ReserveUse.word (reserve start n bits) (settlement bits stock)).Fits w (settlement bits stock).kind.base
  flagWord : A.endAddress c+1<2^w
  widthRoom : (settlement bits stock).width.base+cat.rows<2^w
  ownerEnd : L.arena.endAddress c<2^w
  refOrder : A.first≤(settlement bits stock).kind.base
  recipes : ∀f,(which (routeBanks start n (Fintype.card (Slots z (2^W) k))) f).Fits w (settlement bits stock).kind.base
  rows : 2*(Fintype.card (Slots z (2^W) k))≤2^w
  countWord : count<2^w
  kindSize : 2*(Fintype.card (Slots z (2^W) k))≤(settlement bits stock).kind.size
  indexSize : 2*(Fintype.card (Slots z (2^W) k))≤(settlement bits stock).index.size
  order : (settlement bits stock).kind.base+2*(Fintype.card (Slots z (2^W) k))≤(settlement bits stock).index.base
  indexWord : (settlement bits stock).index.base+2*(Fintype.card (Slots z (2^W) k))<2^w
  recipeLow : ∀f,(which (routeBanks start n (Fintype.card (Slots z (2^W) k))) f).base+(which (routeBanks start n (Fintype.card (Slots z (2^W) k))) f).size≤A.first
  ownerLow : (sinkBank start n (Fintype.card (Slots z (2^W) k)) cat.rows).base+(sinkBank start n (Fintype.card (Slots z (2^W) k)) cat.rows).size≤A.first
  flagLow : A.endAddress c<L.arena.first ∧ A.endAddress c<(settlement bits stock).reserved.base ∧
    A.endAddress c<(settlement bits stock).used.base ∧ A.endAddress c<(reserve start n bits).scratch ∧
    A.endAddress c<(settlement bits stock).width.base ∧ A.endAddress c<table bits ∧ A.endAddress c<destination bits

theorem allocated (c : Mesh) (A : Arena) (L : OwnerLedger) (cat : CatalogueRows.Board)
    (z W k count n start stride w : ℕ) (stock : Bank) :
    let bits:=pageBits c A stock stride cat.rows (Fintype.card (Slots z (2^W) k)) count n
    L.arena=ownerArea bits stride →
    (sinkBank start n (Fintype.card (Slots z (2^W) k)) cat.rows).base+(sinkBank start n (Fintype.card (Slots z (2^W) k)) cat.rows).size≤A.first →
    (∀i,(cat.geometry i).Fits w (A.endAddress c)) → 28*2^bits<2^w →
    Ready c A L cat z W k count n start bits w stock := by
  intro bits ledger low geometry top
  let r:=Fintype.card (Slots z (2^W) k)
  let B:=2^bits
  let buyers:=sinkBank start n r cat.rows
  let a:=reserve start n bits
  let b:=settlement bits stock
  have cap : footprint c A stock stride cat.rows r count n < B := Nat.lt_log2_self
  unfold footprint at cap
  have cash : A.first≤A.endAddress c:=Nat.le_add_right ..
  have ptr:=(static_below start n r cat.rows A low).2
  have recipes:=(static_below start n r cat.rows A low).1
  have rowCap:= (Nat.lt_log2_self (n:=2*n)).le
  have bpos : 0<B := Nat.two_pow_pos _
  change 28*B<2^w at top
  have hist : a.history.size=4*B := by simp [a,reserve,banks,Bank.size,B,pow_add,Nat.mul_comm]
  have ledgerEnd : L.arena.endAddress c=2*B+(events c).length*stride := by rw [ledger];rfl
  have ledgerFirst : L.arena.first=2*B:=by rw [ledger];rfl
  have signed : a.kind.base+a.kind.size≤A.first ∧ a.pointer.base+a.pointer.size≤A.first := by
    dsimp only [a,reserve,banks,Bank.size]
    omega
  have fitsBefore (bank : Bank) (bound : bank.base+bank.size≤A.first) : bank.Fits w (4*B) :=
    bank_fit bank (by omega) (by omega)
  have kind := fitsBefore a.kind signed.1
  have pointer := fitsBefore a.pointer signed.2
  have history : a.history.Fits w (4*B) := by
    apply bank_fit _ (by omega)
    change 0+a.history.size≤4*B
    omega
  have read : (ReserveUse.word a b).Fits w b.kind.base := by
    change (ReserveUse.word a b).Fits w (4*B)
    simp only [ReserveUse.word,Expr.Fits,kind,history,pointer,and_self]
  have afits : Room c A L a b count n w := by
    constructor
    · rfl
    · change start+2*n≤ start+2^((2*n).log2+1)
      omega
    · exact rowCap
    · exact rowCap
    · change (start+2^((2*n).log2+1))+2*n≤A.first
      omega
    · change _≤1*B
      omega
    · change 1*B≤_
      omega
    · rw [hist,ledgerEnd]
      omega
    · change 0+a.history.size≤6*B
      omega
    · change 6*B+count≤7*B
      omega
    · change 7*B+count≤8*B
      omega
    · change 8*B+2*n<2^w
      omega
    · change _≤6*B ∧ _≤6*B
      omega
    · change count≤B
      omega
    · change count≤B
      omega
  have eachPage (i : ℕ) (hi : i≤8) : (page bits i).Fits w (source bits) := by
    apply bank_fit _ (by change 9*B<2^w;omega)
    change i*B+B≤9*B
    have small:=Nat.mul_le_mul_right B hi
    omega
  have stockFit : stock.Fits w (source bits) := bank_fit _ (by change 9*B<2^w;omega) (by change _≤9*B;omega)
  have bk : b.kind.Fits w (source bits):=eachPage 4 (by decide)
  have bi : b.index.Fits w (source bits):=eachPage 5 (by decide)
  have br : b.reserved.Fits w (source bits):=eachPage 6 (by decide)
  have bu : b.used.Fits w (source bits):=eachPage 7 (by decide)
  have words : (RouteSettlement.words b).Fits w (source bits) := by
    simpa only [RouteSettlement.words,Expr.Fits,and_true,true_and] using
      (show b.kind.Fits w (source bits) ∧ b.index.Fits w (source bits) ∧ b.kind.Fits w (source bits) ∧
        (b.stock.Fits w (source bits) ∧ b.index.Fits w (source bits)) ∧
        (b.reserved.Fits w (source bits) ∧ b.index.Fits w (source bits)) ∧
        (b.used.Fits w (source bits) ∧ b.index.Fits w (source bits)) from
        ⟨bk,bi,bk,⟨stockFit,bi⟩,⟨br,bi⟩,bu,bi⟩)
  have geometryFit (i : Fin 7) : (cat.geometry i).Fits w (table bits) :=
    ProtocolRAMGeneratedWrite.fits_mono _ (by change A.endAddress c≤10*B;omega) (geometry i)
  have sink : SinkSpace (cat.sink r b (source bits) (table bits) (destination bits) buyers) w := by
    constructor
    · change 4*B+B≤6*B;omega
    · change 5*B+B≤6*B;omega
    · change buyers.base+buyers.size≤6*B;change buyers.base+buyers.size≤A.first at low;omega
    · change buyers.base+buyers.size≤1*B;change buyers.base+buyers.size≤A.first at low;omega
    · exact words
    · change 9*B+2*r<2^w;omega
    · change 1*B+cat.rows≤9*B;omega
    · by_contra! short
      have tiny : 2^w≤2^3 := Nat.pow_le_pow_right (by decide) short
      norm_num at tiny
      omega
    · apply packed_fit b cat buyers
      · apply bank_fit _ (by change 10*B<2^w;omega)
        change buyers.base+buyers.size≤10*B
        change buyers.base+buyers.size≤A.first at low
        omega
      · apply bank_fit _ (by change 10*B<2^w;omega)
        change 1*B+B≤10*B
        omega
      · exact geometryFit
    · change 10*B+8*cat.rows<2^w;omega
    · change 18*B+9*cat.rows<2^w;omega
    · left
      change 10*B+8*cat.rows≤18*B;omega
  refine ⟨afits,sink,read,?_,?_,?_,?_,fun f=>fitsBefore _ (recipes f),?_,?_,?_,?_,?_,?_,recipes,low,?_⟩
  · omega
  · change 1*B+cat.rows<2^w;omega
  · omega
  · change A.first≤4*B;omega
  · omega
  · omega
  · change 2*r≤B;omega
  · change 2*r≤B;omega
  · change 4*B+2*r≤5*B;omega
  · change 5*B+2*r<2^w;omega
  · change A.endAddress c<L.arena.first ∧ _<6*B ∧ _<7*B ∧ _<8*B ∧ _<1*B ∧ _<10*B ∧ _<18*B
    omega

end Hierarchy.ProtocolRAM.CatalystArchive.TerminalLayout
end

end OAI
