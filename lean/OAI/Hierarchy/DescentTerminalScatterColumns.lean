import OAI.Hierarchy.DescentTerminalScatterChip
import OAI.Hierarchy.DescentTerminalScatterRows
import OAI.Hierarchy.DescentTerminalChipTapes

namespace OAI
/-! # The native endpoint scatter writes the exact banks read by the five-scan host -/
namespace Hierarchy.DescentTerminalScatterColumns
open DescentKernelHistory hiding Word
open DescentTerminalChipSource DescentTerminalRecipeRows DescentTerminalGraphPositions
open DescentTerminalScatterRows DescentTerminalDenseWindow DescentTerminalCableOrder DescentTerminalScalarPadded
open Computability.VPVNP.BurstRAM PrivateRAM DescentTerminalChipRuntime Computability.BorderVNP.Crossing
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {S q W K₀ : ℕ} (sites : Fin S→Site) (wp : 0<W)
    (front : Bins (W:=W) (q:=q) sites ≤ K₀)
def fixed : GroupRow (q:=q) sites ↪ Fin (K₀*W) :=
  (rowAddress sites wp).trans (Fin.castLEEmb (Nat.mul_le_mul_right W front))

theorem extend_fixed {A B : Type} (values : GroupRow (q:=q) sites→A) (missing : A) (map : A→B)
    (i : Fin (K₀*W)) :
    Function.extend (fixed sites wp front) (map∘values) (fun _=>map missing) i=
      map (pad (column sites wp values missing) missing i) := by
  by_cases live : ∃a,fixed sites wp front a=i
  · obtain ⟨a,rfl⟩:=live
    rw [(fixed sites wp front).injective.extend_apply]
    change _=map (pad _ _ ((rowAddress sites wp a).castLE (Nat.mul_le_mul_right W front)))
    rw [pad_front,column_at]
    rfl
  · by_cases owned : i.val<Bins (W:=W) (q:=q) sites*W
    · let j : Fin (Bins (W:=W) (q:=q) sites*W):=⟨i.val,owned⟩
      have gap : ¬∃a,rowAddress sites wp a=j := by
        rintro ⟨a,h⟩
        apply live
        refine ⟨a,Fin.ext ?_⟩
        change ((rowAddress sites wp) a).val=j.val
        exact congrArg Fin.val h
      simp [Function.extend,live,pad,owned,column,show (⟨i.val,owned⟩:Fin _)=j from rfl,gap]
    · simp [Function.extend,live,pad,owned]

def recorded {B : Type} (values : GroupRow (q:=q) sites→B) (missing : B) : Fin (K₀*W)→B :=
  Function.extend (fixed sites wp front) values (fun _=>missing)

attribute [local irreducible] DescentTerminalCableOrder.order DescentTerminalBundleRows.site
  fixed recorded

variable {P Tag : Type} [Fintype P] {D p piece K w rawRows : ℕ} {bits : P→ℕ}
    (N : Network D P bits) (home : N.Site→Fin S) (native : N.Edge ↪ Fin (Fintype.card N.Edge))
    (external : P ↪ ℕ) (nodes : N.Site ↪ ℕ) (ops : ∀v,Boundary N v ↪ ℕ)
    (r : ∀v,Recipe Tag (DescentTerminalBundleRows.SiteRef (p:=p) N v)) (hp : 0<p)
    (birth : ∀v,(r v).Node ↪ ℕ) (qp : 0<q)
local notation "L" => DescentTerminalCableOrder.order (S:=S) (D:=D) (P:=P) (bits:=bits)
  N home native p external nodes ops
local notation "actual" => DescentTerminalBundleRows.site (G:=N) (S:=S) (p:=p) (Tag:=Tag) L r hp birth
local notation "Inst" => GroupRow (q:=q) actual
local notation "idx" => DescentTerminalScalarInput.index (q:=q) (rawRows:=rawRows) N home native external nodes ops r hp birth
local notation "fmt" => DescentTerminalScalarInput.control N home native external nodes ops r hp birth qp
local notation "actualContent" => content (K₀:=K) N home native external nodes ops r hp birth wp qp
local notation "recordedWord" => recorded (q:=q) (W:=W) (K₀:=K) (B:=Word w) actual wp

theorem index_read (f : Bins (W:=W) (q:=q) actual ≤ K) (same : p=W*piece)
    (pay : (Fin rawRows × Fin (q*p))→Bool) (outer : Ports bits) (b : ℕ) (m : Memory w)
    (scatter : ∀i : Fin (K*W),m (b+i.val)=recordedWord f
      (fun a : Inst=>(idx (anchor actual qp a):Word w)) 0 i) :
    ∀i : Fin (K*W),m (b+i.val)=((actualContent same pay outer).first i:Word w) := by
  intro i
  have placed := extend_fixed (q:=q) (W:=W) (K₀:=K) actual wp f (fun a=>idx (anchor actual qp a)) 0
    (fun z : ℕ=>(z:Word w)) i
  rw [scatter i]
  unfold recorded
  exact placed

theorem format_read (f : Bins (W:=W) (q:=q) actual ≤ K) (same : p=W*piece)
    (pay : (Fin rawRows × Fin (q*p))→Bool) (outer : Ports bits) (b : ℕ) (m : Memory w)
    (scatter : ∀i : Fin (K*W),m (b+i.val)=recordedWord f
      (fun a : Inst=>((formatIndex q p (fmt (anchor actual qp a))).val:Word w))
      ((formatIndex q p (blank q p)).val:Word w) i) :
    ∀i : Fin (K*W),m (b+i.val)=((formatIndex q (W*piece) ((actualContent same pay outer).format i)).val:Word w) := by
  intro i
  have placed := extend_fixed (q:=q) (W:=W) (K₀:=K) actual wp f
    (fun a=>fmt (anchor actual qp a)) (blank q p) (fun a=>((formatIndex q p a).val:Word w)) i
  rw [scatter i]
  unfold recorded
  subst p
  exact placed

end
end Hierarchy.DescentTerminalScatterColumns

end OAI
