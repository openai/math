import OAI.Hierarchy.DescentResetStemReindexed
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # Memory geometry of the stem issuer for all output blocks -/
namespace Hierarchy.DescentResetStemPackedIssue.Mixed
open DescentDyadicSpan DescentSIMDLookup

/-- The first 56 cells contain the seven scalar digit weights. After them come
two scalar descriptor rows for each short ticket and physical receiving host. -/
def plan (location ptr K H : ℕ) : Layout :=
  ⟨location+56, ptr, location+56+(2*K)*H+span H⟩

def endAddress (location ptr D f b K P H G M X Q : ℕ) :=
  (plan location ptr K H).stop D f (b*7) K M P H G (X*Q)

def segment (D f b K P H G M X Q : ℕ) :=
  64+DescentResetStemKey.words D f M+2^(b*7)+DescentResetStemMux.words K (f+2) (b*7) M+
    (2*K+2)*H+2*P+(X*Q+2)*(P*chunks G M)+(2*K+X*Q+10)*(H*chunks G M)

theorem space (location ptr D f b K P H G M X Q : ℕ) :
    endAddress location ptr D f b K P H G M X Q≤ location+segment D f b K P H G M X Q := by
  have h1:=span_le H
  have h2:=span_le P
  have h3:=span_le (P*chunks G M)
  have h4:=span_le (H*chunks G M)
  simp only [endAddress,segment,plan,Layout.stop,Layout.out,Layout.mux,Layout.hdr,Layout.mapping,
    DescentResetStemKey.Columns.stop,DescentResetStemKey.Columns.start,DescentResetStemKeyReindex.size,
    DescentResetStemHeaders.outputBase,DescentResetStemHeaders.romSize,Nat.add_mul]
  omega

/-- One descriptor array and each fixed control ROM are shared across all blocks. -/
theorem fixed_start (location ptr K H : ℕ) :
    (plan location ptr K H).raw=location+56 ∧
    (plan location ptr K H).base=(plan location ptr K H).raw+(2*K)*H+span H := ⟨rfl,rfl⟩

/-- The runtime predecessor pointer affects reads only. Translating the scratch
origin translates every subsequent end by exactly the same amount. -/
theorem affine (location ptr D f b K P H G M X Q : ℕ) :
    endAddress location ptr D f b K P H G M X Q =
      location+endAddress 0 0 D f b K P H G M X Q := by
  simp only [endAddress,plan,Layout.stop,Layout.out,Layout.mux,Layout.hdr,Layout.mapping,
    DescentResetStemKey.Columns.stop,DescentResetStemKey.Columns.start,
    DescentResetStemHeaders.outputBase,Nat.zero_add,Nat.add_assoc]

open DescentDatedAddressBook

/-- A single address exponent is enough for all reached permutations and all
their dates. The three lookup exponential sizes appear individually. -/
theorem bounded {ι : ℕ→Type*} (loc ptr D f b K P H G M X Q : ∀h,ι h→ℕ)
    (origin : Bounded loc) (degree : Bounded D) (tickets : Bounded K)
    (old : Bounded P) (hosts : Bounded H) (blocks : Bounded X) (slots : Bounded Q)
    (rail : Bounded (fun h i=>chunks (G h i) (M h i)))
    (keys : Bounded (fun h i=>2^(DescentResetStemKey.unit (D h i) (f h i)*M h i)))
    (digit : Bounded (fun h i=>2^(b h i*7)))
    (select : Bounded (fun h i=>2^(DescentResetStemMux.unit (f h i+2) (b h i*7)*M h i))) :
    Bounded (fun h i=>endAddress (loc h i) (ptr h i) (D h i) (f h i) (b h i)
      (K h i) (P h i) (H h i) (G h i) (M h i) (X h i) (Q h i)) := by
  apply Bounded.of_le (le:=fun h i=>space (loc h i) (ptr h i) (D h i) (f h i) (b h i) (K h i)
    (P h i) (H h i) (G h i) (M h i) (X h i) (Q h i))
  let c (n : ℕ):=Bounded.const (ι:=ι) n
  have key := ((degree.add (c 2)).add (c 2)).mul ((c 2).mul keys)
  have mux := (tickets.add (c 1)).mul ((c 2).mul select)
  have tq := blocks.mul slots
  exact origin.add ((((((((c 64).add key).add digit).add mux).add ((((c 2).mul tickets).add (c 2)).mul hosts)).add
    ((c 2).mul old)).add ((tq.add (c 2)).mul (old.mul rail))).add
      (((((c 2).mul tickets).add tq).add (c 10)).mul (hosts.mul rail)))

end Hierarchy.DescentResetStemPackedIssue.Mixed

end OAI
