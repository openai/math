import OAI.Hierarchy.DescentTerminalFieldCoordinates
import OAI.Hierarchy.DescentTerminalSiteShelves
import OAI.Hierarchy.DescentTerminalVertexWord
import OAI.Hierarchy.ProtocolRAMPortRanks
import OAI.Computability.VPVNP.LiveHeaderBits

namespace OAI
/-! # The terminal shared table accepts the separately emitted little-endian fields -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentTerminalSiteShelves DescentTerminalPrintedFields DescentTerminalLeafDigits
open DescentTerminalRowBooks Computability.VPVNP.RAMSerialization Computability.VPVNP.BurstRAM
open scoped Classical BigOperators
noncomputable section
variable {q t H N A w : ℕ}
local notation "K" => Key H N A
local notation "Row" => DescentTerminalSiteShelves.Row (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w)

def order : K ↪ ℕ :=
  (((Equiv.sumCongr (Equiv.ofUnique Unit (Fin 1)) (fieldsOrder 1 H N A)).trans finSumFinEquiv).toEmbedding).trans Fin.valEmbedding

def offset (k : K) (j : Fin (bits q t H N A w k)) : Fin (span q t H N A w) :=
  ProtocolRAMPortRanks.address (bits q t H N A w) order ⟨k,j⟩

def one (b : Book q t H N A w) : Control q t H N A w 1 := ⟨1,fun _=>b⟩
def value (r : Row) : (k:K)→Fin (bound q t H N A w k)
  | .inl _=>r.1
  | .inr k=>digit (emit (one r.2)) k

theorem positive (k : K) : 0<bound q t H N A w k := by
  rcases k with _|(_|(_|(_|(_|(_|(_|_)))))) <;> simp [bound,radix]

def read (x : Word (span q t H N A w)) (k : K) : Fin (bound q t H N A w k) :=
  let z:Word (bits q t H N A w k):=(wordBits _).symm (fun j=>wordBits _ x (offset k j))
  if room : z.val<bound q t H N A w k then ⟨z.val,room⟩ else ⟨0,positive k⟩

def emitted (r : Row) (x : Word (span q t H N A w)) :=
  ∀k : K,∀j : Fin (bits q t H N A w k),wordBits _ x (offset k j)=(value r k).val.testBit j.val

theorem read_at (r : Row) (x : Word (span q t H N A w)) (found : emitted r x) (k : K) : read x k=value r k := by
  let y:=value r k
  have fits : y.val<2^(bits q t H N A w k):=y.isLt.trans_le (Nat.le_pow_clog (by decide) _)
  have same : (wordBits _).symm (fun j=>wordBits _ x (offset k j))=(⟨y.val,fits⟩:Word (bits q t H N A w k)) := by
    apply (wordBits _).injective
    funext j;rw [Equiv.apply_symm_apply]
    exact (found k j).trans (Computability.VPVNP.LiveHeader.testBit_wordBits (⟨y.val,fits⟩:Word (bits q t H N A w k)) j)
  unfold read
  rw [same]
  simp only [dite_eq_left y.isLt]
  exact Fin.ext rfl

def descriptor (x : Word (span q t H N A w)) : Fields q t H N A w 1 where
  count:=1
  sizes v:=(read x (.inr (.inr (.inl v))),read x (.inr (.inr (.inr (.inl v)))))
  width v h:=read x (.inr (.inr (.inr (.inr (.inl (v,h))))))
  role v n:=read x (.inr (.inr (.inr (.inr (.inr (.inl (v,n)))))))
  arity v n:=read x (.inr (.inr (.inr (.inr (.inr (.inr (.inl (v,n))))))))
  operand v n a:=read x (.inr (.inr (.inr (.inr (.inr (.inr (.inr (v,n,a))))))))

def decode (x : Word (span q t H N A w)) : Row :=
  (read x (.inl ()),(DescentTerminalPrintedFields.decode (descriptor x)).2 ⟨0,(by decide : (0 : ℕ) < 1)⟩)

theorem decode_read (r : Row) (x : Word (span q t H N A w)) (found : emitted r x) : decode x=r := by
  have fields : descriptor x=emit (one r.2) := by
    apply Fields.ext
    · rfl
    · funext v
      exact Prod.ext (read_at r x found (.inr (.inr (.inl v))))
        (read_at r x found (.inr (.inr (.inr (.inl v)))))
    · funext v h
      exact read_at r x found (.inr (.inr (.inr (.inr (.inl (v,h))))))
    · funext v n
      exact read_at r x found (.inr (.inr (.inr (.inr (.inr (.inl (v,n)))))))
    · funext v n
      exact read_at r x found (.inr (.inr (.inr (.inr (.inr (.inr (.inl (v,n))))))))
    · funext v n a
      exact read_at r x found (.inr (.inr (.inr (.inr (.inr (.inr (.inr (v,n,a))))))))
  let get (c : Control q t H N A w 1) := if h:0<c.1.val then c.2 ⟨0,h⟩ else DescentTerminalScalarHeader.emptyBook q t H N A w
  have body:=congrArg get ((congrArg DescentTerminalPrintedFields.decode fields).trans (back (one r.2)))
  apply Prod.ext
  · exact read_at r x found (.inl ())
  · exact body

/-- The physical prefix plus the local field offset locate each bit directly in the upstream texture. -/
def Source {V : ℕ} (z : DescentTerminalSiteShelves.Home (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V))
    (start : ℕ) (stream : ℕ→Bool) := ∀v : Fin z.1.val,∀k : K,∀j : Fin (bits q t H N A w k),
      stream (start+(v.val*span q t H N A w+(offset k j).val))=(value (z.2 v) k).val.testBit j.val

theorem vertex_read {V B : ℕ} (z : DescentTerminalSiteShelves.Home (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V))
    (start : ℕ) (stream : ℕ→Bool) (bp : 0<B) (localFit : z.1.val*span q t H N A w≤B)
    (source : Source z start stream) (v : Fin z.1.val) :
    decode (vertex (span q t H N A w) ⟨start%B,Nat.mod_lt _ bp⟩ (DescentTerminalDenseWindow.dense B stream (start/B))
      (DescentTerminalDenseWindow.dense B stream (start/B+1)) v.val)=z.2 v := by
  apply decode_read
  intro k j
  have room := (Nat.mul_le_mul_right (span q t H N A w) v.isLt).trans localFit
  exact (vertex_dense_at (span q t H N A w) start v.val stream bp room (offset k j)).trans (source v k j)

end
end Hierarchy.DescentTerminalVertexFields

end OAI
