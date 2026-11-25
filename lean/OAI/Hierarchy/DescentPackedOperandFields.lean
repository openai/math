import OAI.Hierarchy.DescentPackedOperand
import OAI.Hierarchy.DescentPackedFieldGather
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Native assembly of ten packed operand columns and their common short-key transition -/

namespace Hierarchy.DescentPackedOperand
open DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM DescentPacking.PackedMatch.Local
open scoped Classical Fin.CommRing
noncomputable section

variable {k H r w M : ℕ}
structure Layout where
  field : Fin 10→Bank
  joins : Fin 10→DescentPackedZip.Tables
  remap : Banks

def source (L : Layout) (i : Fin 10) := Expr.lookup (L.field i) .row
def panel (L : Layout) := Gather.assembly L.joins (source L)

structure Room (L : Layout) (k H r M w out : ℕ) : Prop where
  join : Gather.Bounds (w:=w) (d:=k+2) (M:=M) L.joins (source L) L.remap.source.base
  fieldCap : ∀i,H*chunks r M≤(L.field i).size
  route : DescentSIMDLookup.Fits L.remap (inputWidth k) (outputWidth k) M H r w out
  staticBelow : ∀j : Cell (inputWidth k*M)⊕Fin (H*chunks r M),fixedAddr L.remap j<L.remap.source.base

structure Installed (L : Layout) (x : Fin H→Fin r→Fragment k) (M : ℕ) (m : Memory w) : Prop where
  fieldRead : ∀i (p : Row H r M),m ((L.field i).base+(row H r M p).val)=
    ((data (fun v t=>sourceFields (x v t) i) p).val:ℕ)
  join : ∀i,DescentPackedZip.Static (L.joins i) (Gather.setField (d:=k+2) i) M m
  dictionary : ∀j : Cell (inputWidth k*M)⊕Fin (H*chunks r M),
    m (fixedAddr L.remap j)=fixedWord (M:=M) (H:=H) (r:=r) (transition k) j

def prepare (L : Layout) (H r M w : ℕ) := scan w L.remap.source.base (H*chunks r M) (panel L)
def prepared (L : Layout) (H r M : ℕ) (m : Memory w) := image L.remap.source.base (H*chunks r M) (panel L) m

private theorem collect_work (L : Layout) (fields : List (Fin 10)) :
    (Gather.collect L.joins (source L) fields).work=1+18*fields.length := by
  induction fields with
  | nil=>rfl
  | cons i fields ih=>
    simp only [Gather.collect,DescentPackedZip.work,ih,List.length_cons]
    change (1+18*fields.length)+7+11=_
    omega

theorem panel_work (L : Layout) : (panel L).work=181 := by
  simpa [panel,Gather.assembly] using collect_work L (List.finRange 10)

theorem assemble (L : Layout) (x : Fin H→Fin r→Fragment k) (out : ℕ)
    (room : Room L k H r M w out) (m : Memory w) (load : Installed L x M m) :
    (prepare L H r M w).Exec m (prepared L H r M m) (4+366*(H*chunks r M)) ∧
      PinFrame (M:=M) L.remap (transition k) (fun h i=>packed (x h i)) (prepared L H r M m) := by
  have fields i : DescentPackedZip.Source (source L i) (fun v j=>sourceFields (x v j) i) M m :=
    DescentPackedZip.source_column (L.field i) _ (room.join i).1.1 m _ (room.fieldCap i) (load.fieldRead i)
  have got:=Gather.collected L.joins (source L) L.remap.source.base room.join m load.join
    (fun v j=>sourceFields (x v j)) fields (List.finRange 10)
  have read : DescentPackedZip.Source (panel L) (fun v j=>packed (x v j)) M m := by
    simpa only [panel, Gather.assembly, packed, inputWidth, List.mem_finRange, ite_true] using got
  have fits := Gather.fits L.joins (source L) L.remap.source.base room.join (List.finRange 10)
  have capacity:=room.route.srcSize
  have placement := room.route.source.2.2
  have enough := room.route.output
  refine ⟨?_,?_,?_⟩
  · rw [show 4+366*(H*chunks r M)=4+(H*chunks r M)*(2*(panel L).work+4) by rw [panel_work];omega]
    intro P R K machine
    exact scan_exec L.remap.source.base (H*chunks r M) (panel L) m fits (by omega) machine
  · intro j i
    have old := ProtocolRAMGeneratedWrite.frame_image L.remap.source.base (H*chunks r M)
      (panel L) m _ (.inl (room.staticBelow j))
    simp only [prepared,old,load.dictionary]
  · intro p
    exact (ProtocolRAMGeneratedWrite.read_image _ _ _ m (row H r M p)).trans (read p)

def routed (L : Layout) (out H r M w : ℕ) := (prepare L H r M w).seq (program L.remap out H r M w)

theorem routed_spec (L : Layout) (out : ℕ) (room : Room L k H r M w out)
    (x : Fin H→Fin r→Fragment k) (positive : 0<M) (m : Memory w) (load : Installed L x M m) :
    (routed L out H r M w).Spec (·=m) (fun _ done=>∀v j (f : Fin 5),
      digit (k+4) f.val (digit (outputWidth k) (lane j positive).val
        (done (out+(row H r M (position v j positive)).val)).val)=(resolve (x v j)).fields f)
      (8+410*(H*chunks r M)) ∧ CheapCode (routed L out H r M w) := by
  obtain ⟨first,stored⟩:=assemble L x out room m load
  obtain ⟨next,cheap⟩:=native k H r M w L.remap out room.route x positive
  refine ⟨?_,cheap_seq (@scan_cheap _ _ _ _) cheap⟩
  exact Procedure.Spec.mono (Procedure.Spec.seq first next (by intro _ tmp eqn;subst tmp;exact stored))
    (fun _ h=>h) (fun _ _ h=>h.choose_spec.2) (by omega)

def finished (L : Layout) (out H r M : ℕ) (m : Memory w) :=
  image out (H*chunks r M) (lookup L.remap) (prepared L H r M m)

/-- Exact memory map of the two packed scans. In particular a common table
loaded once remains available to all following calls on the same row geometry. -/
theorem routed_image (L : Layout) (out : ℕ) (room : Room L k H r M w out)
    (x : Fin H→Fin r→Fragment k) (m : Memory w) (load : Installed L x M m) :
    (routed L out H r M w).Exec m (finished L out H r M m) (8+410*(H*chunks r M)) := by
  obtain ⟨first,_⟩:=assemble L x out room m load
  have fit : (lookup L.remap).Fits w out := by
    simp [lookup,Expr.Fits,room.route.source,room.route.dictionary,room.route.mask]
  have clock : 8+410*(H*chunks r M)=(4+366*(H*chunks r M))+
      (4+H*chunks r M*(2*(lookup L.remap).work+4)) := by rw [lookup_work];omega
  rw [clock]
  intro P R K machine
  exact Procedure.Exec.then first (scan_exec out (H*chunks r M) (lookup L.remap) (prepared L H r M m) fit room.route.output) machine

theorem finished_frame (L : Layout) (out H r M : ℕ) (m : Memory w) (a : ℕ)
    (first : a<L.remap.source.base ∨ L.remap.source.base+H*chunks r M≤a)
    (last : a<out ∨ out+H*chunks r M≤a) :
    finished L out H r M m a=m a :=
  (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ last).trans
    (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ first)

theorem finished_read (L : Layout) (out : ℕ) (room : Room L k H r M w out)
    (x : Fin H→Fin r→Fragment k) (m : Memory w) (load : Installed L x M m)
    (positive : 0<M) (v : Fin H) (j : Fin r) (f : Fin 5) :
    digit (k+4) f.val (digit (outputWidth k) (lane j positive).val
      (finished L out H r M m (out+(row H r M (position v j positive)).val)).val)=(resolve (x v j)).fields f := by
  have stored:=(assemble L x out room m load).2
  have words (p : Row H r M) : finished L out H r M m (out+(row H r M p).val)=
      ((masked (transition k) (fun p i=>packed (x p i)) p:ℕ):Word w) :=
    (ProtocolRAMGeneratedWrite.read_image _ _ _ _ (row H r M p)).trans
      (lookup_read L.remap out room.route _ _ _ stored p)
  rw [physical_read L.remap out room.route (transition k) _ _ words v j positive,transition_read]
  exact word_read _ _

def unit (k : ℕ) := 11*(k+2)

/-- Both the intermediate packing dictionaries and the final short-key dictionary
fit in the shared half-word address space. The ten source columns and emitted fields
are charged by packed rows. -/
theorem cells_room (k w : ℕ) :
    let M:=lanes w (unit k)
    ((k+2)*10+(k+2))*M≤w/2 ∧ inputWidth k*M≤w/2 ∧ outputWidth k*M≤w/2 := by
  let M:=lanes w (unit k)
  have budget:=lanes_fit w (unit k)
  have input : inputWidth k≤unit k := by simp [inputWidth,unit];omega
  have output : outputWidth k≤unit k := by simp [outputWidth,unit];omega
  have combined : (k+2)*10+(k+2)=unit k := by unfold unit;omega
  dsimp only
  rw [combined,Nat.mul_comm (unit k) M]
  exact ⟨budget,(Nat.mul_le_mul_right _ input).trans (by simpa [M,Nat.mul_comm] using budget),
    (Nat.mul_le_mul_right _ output).trans (by simpa [M,Nat.mul_comm] using budget)⟩

theorem packed_ticks (k w H r : ℕ) (wide : 2*unit k≤w) :
    (8+410*(H*chunks r (lanes w (unit k))))*w≤8*w+410*(H*w+4*H*r*unit k) := by
  have pos : 0 < unit k := by unfold unit;omega
  have size:=volume H r w (unit k) pos wide
  nlinarith only [Nat.mul_le_mul_left 410 size]

end
end Hierarchy.DescentPackedOperand

end OAI
