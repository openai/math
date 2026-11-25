import OAI.Hierarchy.DescentDonorTrimCode
import OAI.Hierarchy.DescentOrdinarySiteDecoder
import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Coalesced ordinary cable endpoints in short position-relative coordinates -/

namespace Hierarchy.DescentHostDirectory.SiteDecode
open DescentSIMDLookup
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def localNumber (k slots : ℕ) (q : Key V) := packedNumber (fun _=>0) k slots q
omit [DecidableEq V] in
theorem trim_key (k g slots : ℕ) (hub : V→Bool) (q : Key V) (legal : q∈keys k slots) :
    trim k g slots (hub q.1) (localNumber k slots q)=localNumber k slots (mergeHub hub k g q) := by
  obtain ⟨_,atKey⟩:=Finset.mem_product.mp legal
  obtain ⟨tree,slot⟩:=Finset.mem_product.mp atKey
  have hslot:=Finset.mem_range.mp slot
  have valid:=codes_valid tree
  have nd:=node_decode _ _ valid.2
  have div : (nodeNumber q.2.1.1 q.2.1.2*slots+q.2.2)/slots=nodeNumber q.2.1.1 q.2.1.2 := by
    rw [Nat.mul_comm _ slots,Nat.mul_add_div (by omega : 0<slots),Nat.div_eq_of_lt hslot,Nat.add_zero]
  cases h:hub q.1 <;> simp [trim,mergeHub,h,localNumber,packedNumber,div,nd.1,nd.2]

omit [DecidableEq V] in
theorem trim_lt (k g slots : ℕ) (hub : V→Bool) (q : Key V) (legal : q∈keys k slots) :
    trim k g slots (hub q.1) (localNumber k slots q)<2^(k+1)*slots := by
  rw [trim_key k g slots hub q legal]
  obtain ⟨_,atKey⟩:=Finset.mem_product.mp legal
  obtain ⟨tree,slot⟩:=Finset.mem_product.mp atKey
  have hs:=Finset.mem_range.mp slot
  obtain ⟨hd,hi⟩:=codes_valid tree
  have limit {d j : ℕ} (dk : d≤k) (idx : j<2^d) (a : ℕ) (small : a<slots) :
      nodeNumber d j*slots+a<2^(k+1)*slots := by
    have hnode : nodeNumber d j<2^(k+1) :=
      (node_range idx).2.trans_le ((Nat.sub_le ..).trans (Nat.pow_le_pow_right (by decide) (by omega)))
    calc
      _ < nodeNumber d j*slots+slots := Nat.add_lt_add_left small _
      _ = (nodeNumber d j+1)*slots := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hnode
  cases flag : hub q.1
  · simpa [mergeHub,flag,localNumber,packedNumber] using limit hd hi q.2.2 hs
  · have shrunk : q.2.1.2/2^(q.2.1.1-(k-g))<2^(k-g) := by
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
      rw [←pow_add]
      have depth_bound (depth cut : ℕ) : depth≤cut+(depth-cut) := by omega
      exact hi.trans_le (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (depth_bound q.2.1.1 (k-g)))
    simpa [mergeHub,flag,localNumber,packedNumber] using
      limit (Nat.sub_le k g) shrunk 0 (by omega : 0<slots)

omit [DecidableEq V] in
theorem merged_decompose (rank : V→ℕ) (k g slots : ℕ) (hub : V→Bool) (q : Key V)
    (legal : q∈keys k slots) :
    packedNumber rank k slots (mergeHub hub k g q) =
    rank q.1*(2^(k+1)*slots)+trim k g slots (hub q.1) (localNumber k slots q) := by
  rw [trim_key k g slots hub q legal]
  cases h:hub q.1 <;> simp [mergeHub,localNumber,packedNumber,h] <;> ring

omit [DecidableEq V] in
/-- Global-cable comparison at either endpoint reduces to equality of the two
common position names, followed by comparison of the short local slot. -/
theorem keep_iff (rank : V↪ℕ) (k g slots : ℕ) (hub : V→Bool) (q r : Key V)
    (hq : q∈keys k slots) (hr : r∈keys k slots) :
    packedNumber rank k slots (mergeHub hub k g q)=packedNumber rank k slots (mergeHub hub k g r) ↔
    q.1=r.1 ∧ trim k g slots (hub q.1) (localNumber k slots q)=
      trim k g slots (hub r.1) (localNumber k slots r) := by
  rw [merged_decompose rank k g slots hub q hq,merged_decompose rank k g slots hub r hr]
  let radix:=2^(k+1)*slots
  let trimQ:=trim k g slots (hub q.1) (localNumber k slots q)
  let trimR:=trim k g slots (hub r.1) (localNumber k slots r)
  have qlt : trimQ<radix:=trim_lt k g slots hub q hq
  have rlt : trimR<radix:=trim_lt k g slots hub r hr
  have quotient (owner digit : ℕ) (small : digit<radix) : (owner*radix+digit)/radix=owner := by
    rw [Nat.mul_comm owner radix,Nat.mul_add_div (by omega : 0<radix),Nat.div_eq_of_lt small,Nat.add_zero]
  constructor
  · intro h
    have qr : rank q.1=rank r.1 := by
      have d:=congrArg (·/radix) h
      change (rank q.1*radix+trimQ)/radix=(rank r.1*radix+trimR)/radix at d
      simpa only [quotient _ _ qlt,quotient _ _ rlt] using d
    rw [qr] at h
    exact ⟨rank.injective qr,Nat.add_left_cancel h⟩
  · rintro ⟨same,sameTrim⟩
    rw [sameTrim,same]

def trimKey (a : ℕ) : Cell 1 × Cell a ≃ Cell (1+a) :=
  finProdFinEquiv.trans (finCongr (pow_add 2 1 a).symm)

def shortTrim (k g slots a : ℕ) (u : Cell (1+a)) : Cell a :=
  let arg:=(trimKey a).symm u
  (trim k g slots (decide (arg.1.val≠0)) arg.2.val:ℕ)

omit [DecidableEq V] in
theorem bit_trim (k g slots a : ℕ) (hub : V→Bool) (q : Key V) (valid : q∈keys k slots)
    (fit : 2^(k+1)*slots≤2^a) :
    let v := localNumber k slots q
    shortTrim k g slots a (trimKey a ((if hub q.1 then 1 else 0),(v:ℕ)))=
      ((localNumber k slots (mergeHub hub k g q):ℕ):Cell a) := by
  have small : localNumber k slots q<2^a := by
    have h:=trim_lt k g slots (fun _=>false) q valid
    simpa [trim] using h.trans_le fit
  cases flag:hub q.1 <;> simp [shortTrim,flag,Fin.val_cast_of_lt small,←trim_key k g slots hub q valid]

end
end Hierarchy.DescentHostDirectory.SiteDecode

end OAI
