import OAI.Hierarchy.DescentPackedLookupHeader
import OAI.Hierarchy.DescentPackedFallbackTree

namespace OAI
/-! # Compiling all five metadata words at every local cable in one packed reset lookup -/
namespace Hierarchy.DescentPackedFallbackTree.Image
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure
open DescentPrivateTreeTemplate
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {a b w : ℕ}
/-- Lane-local coding contains only private slot ordinals and the five measured fields. -/
def columns (H n fieldBits unit cap : ℕ) (site : ∀d,Site d→ℕ) (key : Cell (width H n)) :
    Cell (fieldBits*(cap*5)) :=
  encode fieldBits (cap*5) (fun i=>let q : Fin cap × Fin 5:=finProdFinEquiv.symm i
    output H n fieldBits unit q.1.val q.2 site key)

theorem column_read (H n fieldBits unit cap : ℕ) {d : ℕ} (hd : d≤H)
    (site : ∀d,Site d→ℕ) (p : Panel H n) (i : Fin cap) (j : Fin 5) :
    let t:=DescentPrivateTreeTemplate.lookup H d i.val (site d)
    digit fieldBits (finProdFinEquiv (i,j)).val (columns H n fieldBits unit cap site (pack H d p)).val=
      ((![t.active,t.source,t.target,unit*count p t,t.active] j:ℕ):Cell fieldBits).val := by
  rw [columns,digit_encode,Equiv.symm_apply_apply]
  exact congrArg Fin.val (output_pack hd p unit i.val fieldBits j site)

theorem compiled {H n b unit cap M hosts groups : ℕ} (g : Banks) (out : ℕ)
    (site : ∀d,Site d→ℕ) (d : Fin hosts→Fin groups→ℕ) (hd : ∀v i,d v i≤H)
    (p : Fin hosts→Fin groups→Panel H n) (pos : 0<M)
    (fit : Fits g (width H n) (b*(cap*5)) M hosts groups w out) (m : Memory w)
    (tableMem : resident (columns H n b unit cap site) g hosts groups M m)
    (shortRows : ∀q : Row hosts groups M,m (g.source.base+(row hosts groups M q).val)=
       ((data (fun v i=>pack H (d v i) (p v i)) q).val:Word w)) :
    let dst:=imageBank hosts groups M out g m
    (DescentSIMDLookup.program g out hosts groups M w).Exec m dst (4+44*(hosts*chunks groups M)) ∧
      (∀ v i (s : Fin cap) (j : Fin 5),let t:=DescentPrivateTreeTemplate.lookup H (d v i) s.val (site (d v i))
        digit b (finProdFinEquiv (s,j)).val
          (digit (b*(cap*5)) (lane i pos).val (dst (out+(row hosts groups M (position v i pos)).val)).val)=
        ((![t.active,t.source,t.target,unit*count (p v i) t,t.active] j:ℕ):Cell b).val) ∧
      (∀a<out,dst a=m a) ∧ ∀a,out+hosts*chunks groups M≤a→dst a=m a := by
  let f:=columns H n b unit cap site
  let x:=fun v i=>pack H (d v i) (p v i)
  have words : PinFrame (M:=M) g f x m := by
    refine ⟨?_,shortRows⟩
    intro key bit
    cases key with
    | inl key=>exact congrArg (fun n=>wordBits w n bit) (tableMem.1 key)
    | inr key=>exact congrArg (fun n=>wordBits w n bit) (tableMem.2 key)
  have ok : (DescentSIMDLookup.lookup g).Fits w out:=⟨⟨fit.dictionary,fit.source,trivial⟩,fit.mask,trivial⟩
  let dst:=imageBank hosts groups M out g m
  have read (q : Row hosts groups M) : dst (out+(row hosts groups M q).val)=(masked f x q:Word w):=
    (ProtocolRAMGeneratedWrite.read_image _ _ _ _ _).trans (lookup_read g out fit f x m words q)
  refine ⟨?_,?_,fun a ha=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl ha),
    fun a ha=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr ha)⟩
  · have charge : 2*(DescentSIMDLookup.lookup g).work+4 = 44 := rfl
    change (scan w out (hosts*chunks groups M) (DescentSIMDLookup.lookup g)).Exec m
      (image out (hosts*chunks groups M) (DescentSIMDLookup.lookup g) m) _
    rw [Nat.mul_comm 44,←charge]
    intro pcCount regCount slotCount machine pcMap regMap pub exit installed rom cfg input entry same
    subst input
    exact scan_exec out (hosts*chunks groups M) _ m ok fit.output machine pcMap regMap pub exit
      installed rom cfg m entry rfl
  · intro v i s j
    rw [physical_read g out fit f x dst read v i pos]
    exact column_read H n b unit cap (hd v i) site (p v i) s j

end
end Hierarchy.DescentPackedFallbackTree.Image

end OAI
