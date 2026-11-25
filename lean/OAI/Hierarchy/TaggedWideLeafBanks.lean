import OAI.Hierarchy.TaggedWideReported
import OAI.Hierarchy.TaggedWideRowPrefixes
import OAI.Hierarchy.TaggedWideLeafSupport

namespace OAI
/-! # Positive stack instances on the actual common public port grid -/

noncomputable section
namespace Hierarchy.Tagged.WideStack.Leaf
open ThreeFlat Routing Spill CallPool
open TaggedShorterCompaction TaggedShorterNetwork TaggedShorterBudget ProtocolStackContraction ProtocolRAMReportedPorts
open scoped Classical BigOperators

variable {F : Type*} [Field F] {N groups ports lanes w m γ : ℕ} {rows : Fin N→ProtocolRAMEmit.Row}

structure Installed (F : Type*) [Field F] (groups ports lanes w m γ : ℕ)
    (rows : Fin N→ProtocolRAMEmit.Row) where
  half : ℕ
  address : ℕ
  modules : ℕ
  fraction : ℝ
  parentRows : ℝ
  unique : Function.Injective fun i=>(rows i).link
  volume : ((∑g : Fin groups,count rows w m γ g.val : ℕ):ℝ)≤fraction*parentRows
  padding : (groups:ℝ)*(2*half:ℕ)≤fraction*parentRows
  halfPos : 0<half
  twice : 2^address=2*half
  purchase : modules=⌈6*fraction*parentRows/(2*half:ℕ)⌉₊
  near : Compactor F (ports*lanes) (2^address) (address+⌈dyadic γ*w⌉₊)
  far : Compactor F (TaggedShorterGroups.capacity (Fin groups) (ports*lanes) half modules) modules
    (Width (2^address) (address+⌈dyadic γ*w⌉₊))
  metadata : 1+address+address≤⌈dyadic γ*w⌉₊
  port : Bool→Fin N→Fin ports
  distinct : ∀(g:Fin groups) b,PortDistinct rows w m γ g.val (port b)
  room : ∀i,pieces rows w i≤lanes

def Installed.bank (s : Installed F groups ports lanes w m γ rows) : Board F :=
  ofStaticReported rows s.unique s.volume s.padding s.halfPos s.twice s.purchase
    s.near s.far s.metadata s.port s.distinct s.room le_rfl

theorem Installed.placed_mod (s : Installed F groups ports lanes w m γ rows)
    (g : Fin groups) (b : Bool) (u : Fin (count rows w m γ g.val)) :
    (s.bank.place g b u).val%lanes=((common rows w m γ g.val s.unique).symm u).2.val := by
  let kv := (common rows w m γ g.val s.unique).symm u
  exact fixedSlot_mod le_rfl (s.port b kv.1.val) (kv.2.castLE (s.room _))

variable {T : Type} [Fintype T] {cls : T→ℕ} {records : T→Fin N→ProtocolRAMEmit.Row}
  (s : ∀t,Installed F groups ports lanes w m (cls t) (records t))

abbrev banks := fun t=>(s t).bank

def active := originalPrefix (fun _ : T=>groups) cls records w m (fun t=>(s t).unique)

omit [Fintype T] in
theorem support_on_records (t : T) (x : ((s t).bank).Slots) :
    ((∀b i j,x (none,b,i) j=false) ∧ ∀g b i j,x (some g,b,i) j=true →
      ∃u,((s t).bank.place g b u)=i ∧
        i.val%lanes*⌈dyadic (cls t)*w⌉₊+j.val <
          (records t (((common (records t) w m (cls t) g.val (s t).unique).symm u).1.val)).width) ↔
      Supported (s t).bank.place (active s t) x := by
  exact stored_supported (s t).bank.place lanes
    (fun e=>(records t (((common (records t) w m (cls t) e.1.val (s t).unique).symm e.2).1.val)).width)
    (fun e=>((common (records t) w m (cls t) e.1.val (s t).unique).symm e.2).2.val)
    (s t).placed_mod x

end Hierarchy.Tagged.WideStack.Leaf

end
end OAI
