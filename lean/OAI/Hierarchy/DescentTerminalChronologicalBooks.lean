import OAI.Hierarchy.DescentTerminalScalarHeader
import OAI.Hierarchy.DescentTerminalBirthOrdinal

namespace OAI
/-! # Terminal control words printed in actual old/birth/local vertex order -/
namespace Hierarchy.DescentTerminalChronologicalBooks
open DescentKernelHistory DescentTerminalRecipeRows DescentTerminalBinReaddress
open DescentTerminalRowBooks Computability.VPVNP.RAMSerialization
open scoped Classical BigOperators
noncomputable section

variable {q tags H N A w V p : ℕ} {F : Type} [CommSemiring F]

structure Birth {t : Site} (h : ∀v : Fin t.nodes,Recipe (Fin tags) (Fin (t.arity v))) where
  hidden : ∀v,(h v).Hidden ↪ ℕ
  atom : ∀v,(h v).Node ↪ ℕ

def selectOwner {m : ℕ} (owns : Fin m→Prop) :=
  ordinal ((Function.Embedding.subtype owns).trans Fin.valEmbedding)

def select {m : ℕ} (owns : Fin m→Prop) (limit : m≤V) (get : Fin m→Book q tags H N A w) : Control q tags H N A w V :=
  ⟨⟨Fintype.card {v:Fin m // owns v},Nat.lt_succ_of_le ((Fintype.card_subtype_le _).trans (by simpa using limit))⟩,
    fun i=>get ((selectOwner owns).symm i).val⟩

section Local
variable {t : Site} (qp : 0<q) (h : ∀v : Fin t.nodes,Recipe (Fin tags) (Fin (t.arity v)))
    (birth : Birth h) (hH : ∀v,Fintype.card (h v).Hidden ≤ H) (hN : ∀v,Fintype.card (h v).Node ≤ N)
    (hA : ∀v u,(h v).arity u ≤ A) (hw : ∀v u,(h v).width u ≤ w) (hV : t.nodes ≤ V)

def book (v : Fin t.nodes) : Book q tags H N A w :=
  ⟨⟨_,Nat.lt_succ_of_le (hH v)⟩,⟨_,Nat.lt_succ_of_le (hN v)⟩,
    DescentKernelHistory.encode (h v) id (fun j=>(Site.target qp ⟨v,j⟩).2)
      (ordinal (birth.hidden v)) (ordinal (birth.atom v)) (hw v) (hA v)⟩

def owner {t : Site} (qp : 0<q) (r : Fin (t.rows q)) :=
  selectOwner (fun v : Fin t.nodes=>t.descriptor qp v=r)

def control (r : Fin (t.rows q)) : Control q tags H N A w V :=
  select (fun v=>t.descriptor qp v=r) hV (book qp h birth hH hN hA hw)

theorem read_control (dict : Fin tags→List (List Bool)→F) (r : Fin (t.rows q)) (payload : Fin q→Fin p→Bool) :
    DescentTerminalRowBooks.read dict (control qp h birth hH hN hA hw hV r) payload=
      Site.rowScalar qp h dict r payload := by
  let vs:={v : Fin t.nodes //t.descriptor qp v=r}
  let f (v : vs):=(book qp h birth hH hN hA hw v.val).2.2.read dict (fun j=>List.ofFn (payload j))
  change (∏i,f ((owner qp r).symm i))=_
  rw [(owner qp r).symm.prod_comp]
  apply Finset.prod_congr rfl
  intro v _
  exact encode_read (h v.val) id _ (ordinal (birth.hidden v.val)) (ordinal (birth.atom v.val))
    (hw v.val) (hA v.val) dict (fun j=>List.ofFn (payload j))
end Local

abbrev Keys (q tags H N A w V p : ℕ) := DescentTerminalScalarHeader.range q tags H N A w V * 2^(q*p)

def key (c : Control q tags H N A w V) (payload : Fin q→Fin p→Bool) : Fin (Keys q tags H N A w V p) :=
  finProdFinEquiv (DescentTerminalScalarHeader.encode c,(wordBits _).symm (fun j=>
    payload (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2))

def menu (dict : Fin tags→List (List Bool)→F) (z : Fin (Keys q tags H N A w V p)) : F :=
  let pair:=finProdFinEquiv.symm z
  DescentTerminalRowBooks.read dict (DescentTerminalScalarHeader.decode pair.1)
    (fun j t=>wordBits _ pair.2 (finProdFinEquiv (j,t)))

theorem read_key (dict : Fin tags→List (List Bool)→F) (c : Control q tags H N A w V) (payload : Fin q→Fin p→Bool) :
    menu dict (key c payload)=DescentTerminalRowBooks.read dict c payload := by
  unfold menu key
  rw [Equiv.symm_apply_apply]
  simp only [DescentTerminalScalarHeader.back c,Equiv.apply_symm_apply,Equiv.symm_apply_apply]

def empty (q tags H N A w V p : ℕ) : Fin (Keys q tags H N A w V p) :=
  key (⟨⟨0,Nat.zero_lt_succ V⟩,Fin.elim0⟩:Control q tags H N A w V) (fun _ _=>false)
theorem empty_read (dict : Fin tags→List (List Bool)→F) :
    menu dict (empty q tags H N A w V p)=1 := by
  rw [empty,read_key]
  exact Finset.prod_of_isEmpty _

variable {S W pool piece bitsW : ℕ} (sites : Fin S→Site) (wp : 0<W) (qp : 0<q)
    (room : sliceWidth W q piece ≤ bitsW) (pay : Fin (Bins (W:=W) (q:=q) sites)→Payload W q piece)
    (space : DescentTerminalBinPack.purchased W (counts (q:=q) sites) ≤ pool)
    (hist : ∀i,(v : Fin (sites i).nodes)→Recipe (Fin tags) (Fin ((sites i).arity v))) (birth : ∀i,Birth (hist i))
    (hH : ∀i v,Fintype.card (hist i v).Hidden ≤ H) (hN : ∀i v,Fintype.card (hist i v).Node ≤ N)
    (hA : ∀i v u,(hist i v).arity u ≤ A) (hw : ∀i v u,(hist i v).width u ≤ w) (hV : ∀i,(sites i).nodes ≤ V)

def «meta» (z : LocalRow (q:=q) sites) :=
  control qp (hist z.1) (birth z.1) (hH z.1) (hN z.1) (hA z.1) (hw z.1) (hV z.1) z.2
local notation "desc" => «meta» sites qp hist birth hH hN hA hw hV
def issued (c : Control q tags H N A w V) (payload : Fin q→Fin p→Bool) :=
  if c.1.val=0 then empty q tags H N A w V p else key c payload

theorem issued_read (dict : Fin tags→List (List Bool)→F)
    (c : Control q tags H N A w V) (payload : Fin q→Fin p→Bool) :
    menu dict (issued c payload)=DescentTerminalRowBooks.read dict c payload := by
  by_cases hc : c.1.val=0
  · have : IsEmpty (Fin c.1.val):=⟨fun i=>by have:=i.isLt;omega⟩
    simp [issued,hc,empty_read,DescentTerminalRowBooks.read]
  · simp [issued,hc,read_key]

def loc (z : LocalRow (q:=q) sites) := issued (desc z) (rowData sites wp qp room pay z.1 z.2)
local notation "localKey" => loc sites wp qp room pay hist birth hH hN hA hw hV
local notation "gapKey" => empty q tags H N A w V (W*piece)
def requests (i : Fin pool) := padded (rowAddress sites wp space) localKey (rows sites) gapKey i

theorem request_at (z : LocalRow (q:=q) sites) :
    requests sites wp qp room pay space hist birth hH hN hA hw hV (rowAddress sites wp space z)=localKey z := by
  exact padded_live (rowAddress sites wp space) localKey (rows sites) gapKey z (mem_rows sites z)

theorem request_gap (i : Fin pool) (off : ∀z,rowAddress sites wp space z≠i) :
    requests sites wp qp room pay space hist birth hH hN hA hw hV i=gapKey := by
  exact padded_empty (rowAddress sites wp space) localKey (rows sites) gapKey i (fun a _=>off a)

theorem requests_product (fit : ∀i,(sites i).rows q ≤ W) (small : ∀i v,(sites i).arity v ≤ q)
    (dict : Fin tags→List (List Bool)→F) :
    (∏i,menu dict (requests sites wp qp room pay space hist birth hH hN hA hw hV i))=
      ∏i,∏v,(hist i v).value dict (fun j=>
        let src:=source sites wp qp (sourceName sites ⟨i,v,j⟩)
        List.ofFn (pay src.1 src.2)) := by
  unfold requests
  rw [prod_padded _ _ _ (mem_rows sites) _ _ (empty_read dict),Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _
  simp only [loc,issued_read,«meta»,read_control]
  rw [Site.scalar_product qp (small i)]
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  funext j
  apply congrArg List.ofFn
  funext b
  exact reassembled_arg sites wp qp room fit pay ⟨i,v,j⟩ b

theorem alphabet (q tags H N A w V p tagBits bits : ℕ) (tag : tags ≤ 2^tagBits)
    (small : DescentTerminalControlBits.rowBits q tagBits H N A w V+q*p ≤ bits/2) :
    Keys q tags H N A w V p ≤ 2^(bits/2) := by
  apply (Nat.mul_le_mul_right (2^(q*p)) (DescentTerminalScalarHeader.header_room q tags H N A w V tagBits tag)).trans
  rw [←pow_add]
  exact Nat.pow_le_pow_right (by decide) small

end
end Hierarchy.DescentTerminalChronologicalBooks

end OAI
