import OAI.ThreeFlat.Diagonal.CompressorDemandInput
import OAI.ThreeFlat.Diagonal.CompressorDenseMotifs
import OAI.ThreeFlat.Diagonal.CompressorDemandROM

namespace OAI
/-! # Inverting the high digits of an actual old source before demand admission -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkWidth
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
open scoped Fin.NatCast
variable {B H : Type*} [AddCommGroup H] {n w c d t l N : ℕ}
variable {data : Param → Word w} {mem : Memory w} {vs : Fin n → Word w}
local notation "V" => Formula.value data mem vs

private theorem unpair {j k : ℕ} (a : Fin j) (b : Fin k) : (finProdFinEquiv (a,b)).val =
    a.val*k + b.val := by change b.val+k*a.val = _; ac_rfl

private theorem quotient {k : ℕ} (q : ℕ) (b : Fin k) :
    (q*k+b.val)/k=q := by
  rw [Nat.mul_comm q k,Nat.mul_add_div (Nat.zero_lt_of_lt b.isLt),Nat.div_eq_of_lt b.isLt,Nat.add_zero]

private theorem remnant {k : ℕ} (q : ℕ) (b : Fin k) :
    (q*k+b.val)%k=b.val := by simp [Nat.add_mod,Nat.mod_eq_of_lt b.isLt]

omit [AddCommGroup H] in
theorem upper_code (P : PackingData B H (BitWord t) (BitWord l) d c) (b : B ≃ Fin N)
    (E : Codec B w c t l) (table tags lanes residual upper : F n) (a : Upper B H (BitWord t) (BitWord l) d)
    (hb : ∀v, E.base v = ((b v).val:Word w)) (ht : V tags=((2^t:ℕ):Word w)) (hr : V residual=((2^l:ℕ):Word w))
    (hu : V upper=((upperNumber P b (tagOrdinal t) (tagOrdinal l) a).val:Word w))
    (hf : (upperNumber P b (tagOrdinal t) (tagOrdinal l) a).val <2^w)
    (dims : d<2^w ∧ 2^t<2^w ∧ 2^l<2^w) :
    let (x,slot) := upperSource (Demand.layout table tags lanes d c) residual upper
    x.map V = posCode P E (a.1.1,(0 : BitWord c),a.2) ∧ V slot=(a.1.2.val:Word w) := by
  let p := finProdFinEquiv (b a.1.1.1,a.1.2)
  let pl := finProdFinEquiv (p,tagOrdinal l a.1.1.2.2)
  let plt := finProdFinEquiv (pl,tagOrdinal t a.1.1.2.1)
  let u := finProdFinEquiv (plt,P.slotLabel a.2)
  change V upper=(u.val:Word w) at hu
  change u.val<2^w at hf
  have le {m k : ℕ} (x : Fin m) (y : Fin k) : x.val ≤ (finProdFinEquiv (x,y)).val := by
    rw [unpair]
    exact (Nat.le_mul_of_pos_right _ (Nat.zero_lt_of_lt y.isLt)).trans (Nat.le_add_right ..)
  have bplt : plt.val<2^w := (le plt (P.slotLabel a.2)).trans_lt hf
  have bpl : pl.val<2^w := (le pl (tagOrdinal t a.1.1.2.1)).trans_lt bplt
  have bp : p.val<2^w := (le p (tagOrdinal l a.1.1.2.2)).trans_lt bpl
  have ddiv {m k : ℕ} (x : Fin m) (y : Fin k) (hz : (finProdFinEquiv (x,y)).val<2^w) (hk : k<2^w) :
      BinaryOp.div.eval ((finProdFinEquiv (x,y)).val:Word w) (k:Word w)=(x.val:Word w) := by
    rw [op_cast (w:=w) .div _ _ ⟨hz,hk⟩]
    simp only [natOp,unpair,quotient]
  have dmod {m k : ℕ} (x : Fin m) (y : Fin k) (hz : (finProdFinEquiv (x,y)).val<2^w) (hk : k<2^w) :
      BinaryOp.mod.eval ((finProdFinEquiv (x,y)).val:Word w) (k:Word w)=(y.val:Word w) := by
    rw [op_cast (w:=w) .mod _ _ ⟨hz,hk⟩]
    simp only [natOp,unpair,remnant]
  simp only [upperSource,Demand.layout,Position.map,Site.map,Formula.value,hu,ht,hr,Fin.ofNat_eq_cast,
    show BinaryOp.div.eval (u.val:Word w) (d:Word w)=(plt.val:Word w) from ddiv _ _ hf dims.1,
    show BinaryOp.mod.eval (u.val:Word w) (d:Word w)=((P.slotLabel a.2).val:Word w) from dmod _ _ hf dims.1,
    show BinaryOp.div.eval (plt.val:Word w) ((2^t:ℕ):Word w)=(pl.val:Word w) from ddiv _ _ bplt dims.2.1,
    show BinaryOp.mod.eval (plt.val:Word w) ((2^t:ℕ):Word w)=((tagOrdinal t a.1.1.2.1).val:Word w) from dmod _ _ bplt dims.2.1,
    show BinaryOp.div.eval (pl.val:Word w) ((2^l:ℕ):Word w)=(p.val:Word w) from ddiv _ _ bpl dims.2.2,
    show BinaryOp.mod.eval (pl.val:Word w) ((2^l:ℕ):Word w)=((tagOrdinal l a.1.1.2.2).val:Word w) from dmod _ _ bpl dims.2.2,
    show BinaryOp.div.eval (p.val:Word w) (d:Word w)=((b a.1.1.1).val:Word w) from ddiv _ _ bp dims.1,
    show BinaryOp.mod.eval (p.val:Word w) (d:Word w)=(a.1.2.val:Word w) from dmod _ _ bp dims.1,
    posCode,siteCode,tagWord_zero,hb,Demand.tag_cast E.tags a.1.1.2.1,
    Demand.tag_cast E.lanes a.1.1.2.2,Nat.cast_zero,and_true]


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkWidth

end OAI
