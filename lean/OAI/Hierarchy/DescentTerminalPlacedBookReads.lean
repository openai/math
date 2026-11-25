import OAI.Hierarchy.DescentTerminalScalarLiterals
import OAI.Hierarchy.DescentTerminalHeaderScatter

namespace OAI
/-! # All four concrete scalar table receipts in the routed terminal RAM image -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalVertexFields DescentTerminalSiteShelves
open DescentTerminalPrintedFields DescentTerminalHeaderScatter
open DescentTerminalEmitter.Compact
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {blocks v B bw:ℕ} (V:Home.Format) (S:Shape) (J:Input) (R:MaskAllocation.Channels blocks)
variable (start header q t H N A p verts W:ℕ) (qp:0<q)
variable (short:v*span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece≤B)
variable (vals:Fin 43→ℕ→ℕ)
local notation "P" => S.terminal.pool
local notation "c" => ScalarLiterals.columns q t H N A p verts W B P J.sources
local notation "I" => ({ J with sources:=c }:Input)
local notation "fixed" => ScalarLiterals.data q t H N A p verts W B P qp J.sources vals
local notation "ba" => afterMeter V S R start
local notation "O" => registers V S R start header
local notation "C" => meter V R start
local notation "L" => layout S I ba O
local notation "src" => pageEnd S I ba
local notation "loaded" => input V S I R start header short fixed
local notation "μ" => fun m:Memory bw=>Suffix.events S L (C).layout ((rowArena S I ba).mount (loaded m))
local notation "route" => fun m:Memory bw=>DescentTerminalEmitter.routed S.terminal (L).emit (μ m)
local notation "leaf" => (L).emit.leaf
local notation "table" => DescentTerminalPrintedFields.headerTable q t H N A p verts
local notation "total" => (DescentTerminalPrintedFields.capacity q t H N A p verts).total

theorem placed_book_reads (m:Memory bw) (early:Earlier S I ba (C).layout bw) (room:last V S I R start<2^bw) :
    (∀(i:Fin P) (j:Fin 2),(leaf).half.read (route m) ((field i j).val:Word bw)=(i.val:Word bw)) ∧
    (∀i:Fin P,(leaf).home.read (route m) (i.val:Word bw)=(i.val:Word bw)) ∧
    (∀j:Fin (alphabet verts W B),(leaf).weight.read (route m) (j.val:Word bw)=
      (entryBy (DescentTerminalVertexFields.decode (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p)) qp j:Word bw)) ∧
    (∀j:Fin total,(leaf).table.read (route m) (j.val:Word bw)=
      (table[j.val]'(by simp [DescentTerminalPrintedFields.headerTable]):Word bw)) := by
  let μ₀:=route m
  have read (j:Fin 43) {n:ℕ} (bought:c j=.literal n) (next:inputs S I ba j=view src c j) (i:Fin n) :
      (inputs S I ba j).read μ₀ (i.val:Word bw)=(fixed j ⟨i.val,by rw [bought];exact i.isLt.trans_le (Nat.le_pow_clog (by decide) n)⟩:Word bw):=by
    let u:Fin (size (c j)):=⟨i.val,by rw [bought];exact i.isLt.trans_le (Nat.le_pow_clog (by decide) n)⟩
    rw [next]
    exact literal_routed V S I R start header short fixed m early room j bought u
  have a37:c 37=.literal (2*P):=by norm_num [ScalarLiterals.columns]
  have a39:c 39=.literal P:=by norm_num [ScalarLiterals.columns]
  have a41:c 41=.literal (alphabet verts W B):=by norm_num [ScalarLiterals.columns]
  have a42:c 42=.literal total:=by norm_num [ScalarLiterals.columns]
  refine ⟨?_,?_,?_,?_⟩
  · intro i j
    have h:=read 37 a37 (by norm_num [inputs]) (field i j)
    rw [ScalarLiterals.half] at h
    have eqn:(field i j).val/2=i.val:=by change (2*i.val+j.val)/2=i.val;have:=j.isLt;omega
    rw [eqn] at h
    exact h
  · intro i
    have h:=read 39 a39 (by norm_num [inputs]) i
    rw [ScalarLiterals.identity] at h
    exact h
  · intro j
    have h:=read 41 a41 (by norm_num [inputs]) j
    let u : Fin (size (c 41)) := ⟨j.val, by rw [a41]; exact j.isLt.trans_le (Nat.le_pow_clog (by decide : 1 < 2) _)⟩
    rw [ScalarLiterals.decoder q t H N A p verts W B P qp J.sources vals u j.isLt] at h
    exact h
  · intro j
    have h:=read 42 a42 (by norm_num [inputs]) j
    let u : Fin (size (c 42)) := ⟨j.val, by rw [a42]; exact j.isLt.trans_le (Nat.le_pow_clog (by decide : 1 < 2) _)⟩
    rw [ScalarLiterals.header q t H N A p verts W B P qp J.sources vals u j.isLt] at h
    exact h

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
