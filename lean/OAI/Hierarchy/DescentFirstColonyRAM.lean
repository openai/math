import OAI.Hierarchy.DescentFirstOccurrence
import OAI.Hierarchy.ProtocolRAMEndpointPrefix
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Materializing each old site's compact occupied-colony ordinal -/

namespace Hierarchy.DescentFirstColonyRAM
open DescentFirstOccurrence ProtocolRAM ProtocolRAMGeneratedWrite
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {U C : Type*} [Fintype C] {n cells w : ℕ}

structure Chart where
  keys : Bank
  heads : Bank
  links : ℕ
  flags : ℕ
  starts : Bank
  out : ℕ

structure Room (L : Chart) (w n cells : ℕ) : Prop where
  buckets : TraceIntervalScanner.Layout w L.keys.base L.heads.base L.links n cells
  keysSize : n ≤ L.keys.size
  headsSize : cells ≤ L.heads.size
  keyFit : L.keys.Fits w L.flags
  headFit : L.heads.Fits w L.flags
  linksEnd : L.links+n ≤ L.flags
  flagsEnd : L.flags+n ≤ L.starts.base
  startsSize : n+1 ≤ L.starts.size
  startFit : L.starts.Fits w L.out
  last : L.out+n < 2^w

def pointer (L : Chart) : Expr := .lookup L.heads (.lookup L.keys .row)
def firstFlag (L : Chart) : Expr := .branch .eq (pointer L) (.op .add .row (.lit 1)) (.lit 1) (.lit 0)
def number (L : Chart) : Expr := .lookup L.starts (.op .sub (pointer L) (.lit 1))

def program (L : Chart) (w n cells : ℕ) :=
  (((TraceIntervalScanner.procedure w L.keys.base L.heads.base L.links n cells).seq
    (scan w L.flags n (firstFlag L))).seq
    (ProtocolRAMEndpointPrefix.exclusive w L.flags L.starts.base n)).seq
    (scan w L.out n (number L))

def clock (L : Chart) (n cells : ℕ) :=
  (((9+4*cells+10*n)+(4+n*(2*(firstFlag L).work+4)))+(10+(3+12*n)))+
    (4+n*(2*(number L).work+4))

theorem clock_eq (L : Chart) (n cells : ℕ) : clock L n cells = 30+4*cells+106*n := by
  change (((9+4*cells+10*n)+(4+n*(2*19+4)))+(10+(3+12*n)))+(4+n*(2*19+4))=_
  omega

variable (row : U ≃ Fin n) (group : U → C) (covered : Function.Surjective group) (cell : C ↪ Fin cells)

structure Published (L : Chart) (m o : Memory w) : Prop where
  site : ∀ u, o (L.out+(row u).val) = ((DescentPhysicalOrder.physical (rank row group covered) (group u)).val : Word w)
  first : ∀ c, (o (L.heads.base+(cell c).val)).val=rank row group covered c+1
  empty : ∀ b : Fin cells, (∀ c,cell c≠b) → (o (L.heads.base+b.val)).val=0
  compact : ∀ c, o (L.starts.base+rank row group covered c) =
    ((DescentPhysicalOrder.physical (rank row group covered) c).val : Word w)
  prior : ∀ x < L.heads.base, o x=m x

private theorem bankRead (b : Bank) (m : Memory w) (i : ℕ) (h : i < b.size) (fit : b.size < 2^w) :
    b.read m (i : Word w) = m (b.base+i) := by
  simp only [Bank.read,Fin.val_cast_of_lt (h.trans fit),Nat.mod_eq_of_lt h]

omit [Fintype C] in
private theorem pointerRead (L : Chart) (space : Room L w n cells) (m : Memory w)
    (keys : TraceIntervalScanner.Loaded L.keys.base (dest row group cell) m)
    (heads : ∀c,(m (L.heads.base+(cell c).val)).val=rank row group covered c+1)
    (i : Fin n) : ((pointer L).eval m (i.val : Word w)).val = rank row group covered (group (row.symm i))+1 := by
  simp only [pointer,Expr.eval,bankRead L.keys m i.val (i.isLt.trans_le space.keysSize) space.keyFit.2.1,keys i,
    bankRead L.heads m (dest row group cell i).val ((dest row group cell i).isLt.trans_le space.headsSize) space.headFit.2.1]
  exact heads _

private theorem scanSpec (base n : ℕ) (e : Expr) (fits : e.Fits w base) (room : base+n < 2^w) :
    (scan w base n e).Spec (fun _ => True) (fun m o => o=ProtocolRAM.image base n e m)
      (4+n*(2*e.work+4)) := by
  intro P R K M pc reg pub exit installed data cfg mem entry _
  exact scan_exec base n e mem fits room M pc reg pub exit installed data cfg mem entry rfl

theorem publish (L : Chart) (space : Room L w n cells) :
    (program L w n cells).Spec (TraceIntervalScanner.Loaded L.keys.base (dest row group cell))
      (Published row group covered cell L) (clock L n cells) := by
  let pref := fun i => (earlier row group covered i).card
  let A := L.starts.base
  have startLo := space.flagsEnd
  have startHi := space.startFit.2.2
  have startSize := space.startsSize
  have bound := space.last
  have lo := space.buckets.beforeHeads
  have hi := space.buckets.beforeLinks
  have tail := space.linksEnd
  have pointerFit : (pointer L).Fits w L.flags := ⟨space.headFit,space.keyFit,trivial⟩
  have fFit : (firstFlag L).Fits w L.flags := ⟨pointerFit,⟨trivial,trivial⟩,trivial,trivial⟩
  have outFit : (number L).Fits w L.out :=
    ⟨space.startFit, fits_mono _ (by omega) pointerFit,trivial⟩
  intro P R K M pc reg pub exit installed data cfg m entry loaded
  let Intermediate (o : Memory w) := ∃ h : Memory w,
    TraceIntervalScanner.Output L.heads.base L.links (dest row group cell) m h ∧ o=ProtocolRAM.image L.flags n (firstFlag L) h
  have boot : ((TraceIntervalScanner.procedure w L.keys.base L.heads.base L.links n cells).seq
      (scan w L.flags n (firstFlag L))).Spec (·=m) (fun _ o => Intermediate o)
      ((9+4*cells+10*n)+(4+n*(2*(firstFlag L).work+4))) := by
    intro p r k machine pc' reg' pub' exit' code vals config src en eqn
    subst src
    exact Procedure.Spec.seq
      (A:=TraceIntervalScanner.procedure w L.keys.base L.heads.base L.links n cells)
      (B:=scan w L.flags n (firstFlag L))
      (TraceIntervalScanner.procedure_spec space.buckets (dest row group cell))
      (scanSpec L.flags n (firstFlag L) fFit (by omega)) (fun _ _ _ => trivial)
      machine pc' reg' pub' exit' code vals config m en loaded
  have retained {h : Memory w} (ok : TraceIntervalScanner.Output L.heads.base L.links (dest row group cell) m h) :
      TraceIntervalScanner.Loaded L.keys.base (dest row group cell) h := fun i =>
    (ok.1 _ (.inl (by have := i.isLt; omega)) (.inl (by have := i.isLt; omega))).trans (loaded i)
  have accumulate : (ProtocolRAMEndpointPrefix.exclusive w L.flags A n).Spec Intermediate
      (fun a o => o=ProtocolRAMEndpointPrefix.image A pref a n) (10+(3+12*n)) := by
    intro p r k machine pc' reg' pub' exit' code vals config src en hsrc
    obtain ⟨h,ok,rfl⟩ := hsrc
    apply ProtocolRAMEndpointPrefix.run L.flags A n pref _ startLo (by dsimp [A];omega)
      (count_zero row group covered) _ machine pc' reg' pub' exit' code vals config _ en rfl
    intro j hj
    let i : Fin n := ⟨j,hj⟩
    have ptr : ((pointer L).eval h (j:Word w)).val=rank row group covered (group (row.symm i))+1 :=
      pointerRead row group covered cell L space h (retained ok) (head row group covered cell ok) i
    have hw : j+1 < 2^w := by omega
    have refl_ : ((pointer L).eval h (j : Word w) = (j:Word w)+1) ↔
        rank row group covered (group (row.symm i))=j := by
      rw [←Nat.cast_one (R:=Word w),←Nat.cast_add]
      constructor
      · intro eqn
        have z := congrArg Fin.val eqn
        rw [Fin.val_cast_of_lt hw] at z
        exact Nat.succ.inj (ptr.symm.trans z)
      · intro eqn
        exact Fin.ext (by rw [Fin.val_cast_of_lt hw]; simpa [eqn] using ptr)
    have posted := read_image L.flags n (firstFlag L) h i
    rw [show pref (j+1)=pref j+(if rank row group covered (group (row.symm i))=j then 1 else 0) from
      count_step row group covered i,Nat.cast_add,posted]
    by_cases yes : rank row group covered (group (row.symm i))=j
    · simp [firstFlag,Expr.eval,Comparison.test,RowOp.opcode,BinaryOp.eval,i,yes,refl_.mpr yes]
    · have different : (pointer L).eval h (j:Word w) ≠ (j:Word w)+1 :=
        fun eqn=>yes (refl_.mp eqn)
      simp [firstFlag,Expr.eval,Comparison.test,RowOp.opcode,BinaryOp.eval,i,yes,different]
  obtain ⟨t,ht,z,o,steps,stop,prev,⟨marked,⟨h,ok,rfl⟩,rfl⟩,rfl⟩ :=
    Procedure.Spec.seq
      (A:=((TraceIntervalScanner.procedure w L.keys.base L.heads.base L.links n cells).seq
        (scan w L.flags n (firstFlag L))).seq (ProtocolRAMEndpointPrefix.exclusive w L.flags A n))
      (B:=scan w L.out n (number L))
      (Procedure.Spec.seq (@boot) (@accumulate) (fun _ _ post => post))
      (scanSpec L.out n (number L) outFit bound) (fun _ _ _ => trivial)
      M pc reg pub exit installed data cfg m entry rfl
  let final := ProtocolRAMEndpointPrefix.image A pref (ProtocolRAM.image L.flags n (firstFlag L) h) n
  have headKeep (x : ℕ) (hx : x < L.flags) : ProtocolRAM.image L.out n (number L) final x=h x :=
    (frame_image _ _ _ _ _ (.inl (by omega))).trans
      ((ProtocolRAMEndpointPrefix.frame _ _ _ _ _ (.inl (by dsimp [A];omega))).trans
        (frame_image _ _ _ _ _ (.inl hx)))
  refine ⟨t,ht,z,_,steps,stop,⟨?_,?_,?_,?_,?_⟩⟩
  · intro u
    have before (x : ℕ) (hx : x < L.flags) : final x=h x :=
      (ProtocolRAMEndpointPrefix.frame _ _ _ _ _ (.inl (by dsimp [A];omega))).trans
        (frame_image _ _ _ _ _ (.inl hx))
    have value := pointerRead row group covered cell L space h (retained ok) (head row group covered cell ok) (row u)
    have pin : (pointer L).eval final ((row u).val:Word w) =
        ((rank row group covered (group u)+1:ℕ):Word w) := by
      rw [eval_below _ _ h final pointerFit before]
      have rfit := rank_le row group covered (row u)
      have nr := (row u).isLt
      simp only [Equiv.symm_apply_apply] at rfit value
      exact Fin.ext (by rw [Fin.val_cast_of_lt (by omega)]; exact value)
    have rfit := rank_le row group covered (row u)
    simp only [Equiv.symm_apply_apply] at rfit
    have ri := (row u).isLt
    have read := read_image L.out n (number L) final (row u)
    rw [read]
    change L.starts.read final ((pointer L).eval final _ - 1) = _
    simp only [pin,Nat.cast_add,Nat.cast_one,add_sub_cancel_right]
    rw [bankRead _ _ _ (by omega) space.startFit.2.1]
    exact (ProtocolRAMEndpointPrefix.read A pref _ n _ (by omega)).trans
      (congrArg (fun x : ℕ => (x:Word w)) (count_at row group covered (group u)))
  · intro c
    rw [headKeep _ (by have := (cell c).isLt;omega)]
    exact head row group covered cell ok c
  · intro b empty
    rw [headKeep _ (by have := b.isLt;omega)]
    have nil_ : (List.finRange n).filter (fun j => decide (dest row group cell j=b))=[] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro i hi
      exact empty _ (of_decide_eq_true (List.mem_filter.mp hi).2)
    have chain := ok.chain b
    rw [nil_] at chain
    exact chain
  · intro c
    obtain ⟨i,_,hi⟩ := rank_at row group covered c
    have range_ := i.isLt
    rw [frame_image _ _ _ _ _ (.inl (by omega))]
    exact (ProtocolRAMEndpointPrefix.read A pref _ n _ (by omega)).trans
      (congrArg (fun x : ℕ => (x:Word w)) (count_at row group covered c))
  · intro x hx
    exact (headKeep _ (by omega)).trans (ok.1 _ (.inl hx) (.inl (by omega)))

end
end Hierarchy.DescentFirstColonyRAM

end OAI
