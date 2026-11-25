import OAI.Hierarchy.DescentPackedMatchROMRead
import OAI.Hierarchy.DescentPackedMatchROMGeometry
import OAI.Hierarchy.DescentPackedMatchWindowRoom

namespace OAI
/-! # Execute the installed matcher from the earlier source columns and raw tape -/

namespace Hierarchy.DescentPacking.PackedMatch.Local.Gather.ROM
open ProtocolRAM DescentSIMDLookup DescentPackedProfileWindow Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {d r D p K H G M w : ℕ}

def machine (s : Shape) (d r D p B K H G M unit base seats w : ℕ) (field : Fin (fields r D p)→Expr) :=
  let P:=place s d r D p K H G M unit base seats
  let m:=chart s d r D p K H G M (M*s.pairs) unit base P.source
  (program s d r D p B K H G M (M*s.pairs) unit w base).seq
    (complete w (M*s.pairs) m.joins field m.desc m.mask H G M m.lookup P.layout)

def ticks (s : Shape) (d r D p K H G M unit base seats : ℕ) (field : Fin (fields r D p)→Expr) :=
  let P:=place s d r D p K H G M unit base seats
  let m:=chart s d r D p K H G M (M*s.pairs) unit base P.source
  let n:=(K*H)*chunks G M
  4+10*size (fields r D p) K H G M unit+
    (clock (passes m.joins field m.desc m.mask m.lookup.source.base H G M)+((4+44*n)+ProfileTable.clock n))

def after (s : Shape) (d r D p B K H G M unit base seats : ℕ) (field : Fin (fields r D p)→Expr) (old : Memory w) :=
  let P:=place s d r D p K H G M unit base seats
  let R:=M*s.pairs
  let c:=chart s d r D p K H G M R unit base P.source
  let m:=mounted s d r D p B K H G M R unit base old
  finished R (K*H) G M c.lookup P.layout (ProtocolRAM.result (passes c.joins field c.desc c.mask P.source.base H G M) m)

theorem execute (s : Shape) (B unit base seats : ℕ) (field : Fin (fields r D p)→Expr)
    (u : Fin H→Fin G→Panel r D p d) (m : Memory w) (stream : ℕ→Cell s.digit)
    (large : matchUnit s d r D p≤unit) (shifts : unit*M≤w/2)
    (space : (place s d r D p K H G M unit base seats).endAddr<2^w)
    (positive : 0<M*s.pairs) (digits : 0<s.digit) (below : ∀i,(field i).Fits w base)
    (input : ∀i,DescentPackedZip.Source (field i) (fun h j=>terrain u h j i) M m)
    (tape : let b:=(place s d r D p K H G M unit base seats).raw
      ∀i<b.size,m (b.base+i)=((DescentPackedProfileWindow.word s.digit (M*s.pairs) stream i).val:Word w))
    (measured : let keys:=topologyWords (M:=M) s (flat (descriptorInputs (K:=K) s B u))
      ∀i : Fin ((K*H)*chunks G M),PackedProfileCursor.total (ProfileTable.quota s keys) i.val≤ seats) :
    let P:=place s d r D p K H G M unit base seats
    let E:=machine s d r D p B K H G M unit base seats w field
    let o:=after s d r D p B K H G M unit base seats field m
    let keys:=topologyWords (M:=M) s (flat (descriptorInputs (K:=K) s B u))
    E.Exec m o (ticks s d r D p K H G M unit base seats field) ∧
      (∀i,o (P.layout.topology.base+i.val)=((keys i).val:Word w)) ∧
      (∀i : Fin ((K*H)*chunks G M),∀a : Fin M,∀j : Fin s.pairs,
        digit s.digit (finProdFinEquiv (a,j)).val (o (P.layout.out+i.val)).val=
          if j.val<(laneCounts s M (keys i) a).val then (stream
            (PackedProfileCursor.total (ProfileTable.quota s keys) i.val+localPrefix (laneCounts s M (keys i)) a+j.val)).val else 0) ∧
      (∀a<base,o a=m a) ∧ CheapCode E := by
  let P:=place s d r D p K H G M unit base seats
  let R:=M*s.pairs
  let c:=chart s d r D p K H G M R unit base P.source
  let warm:=mounted s d r D p B K H G M R unit base m
  let A:=arranged s d r D p K H G M unit base seats w large shifts space
  have setup : (program s d r D p B K H G M R unit w base).Exec m warm (4+10*size (fields r D p) K H G M unit) :=
    run s d r D p B K H G M R unit base m A.romEnd
  have data:=loaded s d r D p B K H G M unit base P.source m large
  have preserve (a : ℕ) (lo : a<base) : warm a=m a:=frame s d r D p B K H G M R unit base m a (.inl lo)
  have before : base+size (fields r D p) K H G M unit≤P.raw.base := by
    exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  have srcBase : base≤P.source.base := by
    exact ((Nat.le_add_right _ _).trans before).trans (Nat.le_add_right _ _)
  have active : ∀i,DescentPackedZip.Source (field i) (fun h j=>terrain u h j i) M warm :=
    fun i x=>(eval_below (field i) _ m warm (below i) preserve).trans (input i x)
  have head : Header s M R (K*H) G c.lookup P.layout stream warm :=
    data.header P.layout stream rfl rfl fun i hi=>
      (frame s d r D p B K H G M R unit base m (P.raw.base+i) (.inr (by omega))).trans (tape i hi)
  have window (i : Fin ((K*H)*chunks G M)) := (Nat.div_le_div_right (c:=R) (measured i))
  obtain ⟨compute,words,profiles,frame_,cheap_⟩ :=
    complete_run s B c.joins field c.desc c.mask c.lookup P.layout u warm stream
      (A.gather field below) data.joins active A.descriptors A.mask.1 (fun _=>rfl) A.mask.2 data.descriptors data.masks
      A.fit A.room A.prior head A.retained positive le_rfl (ProfileTable.word_room A.room digits)
      (ProfileTable.digit_room s R digits) (fun i=>by
        have cap : seats/R+2 ≤ P.layout.raw.size := A.capacity
        exact (Nat.succ_le_succ (Nat.succ_le_succ (window i))).trans cap)
  refine ⟨?_,words,profiles,fun a lo=>(frame_ a (lo.trans_le srcBase)).trans (preserve a lo),
    cheap_seq (A := program s d r D p B K H G M R unit w base)
      (@cheap s d r D p B K H G M R unit w base) (@cheap_)⟩
  unfold machine ticks after
  apply Procedure.Exec.then setup
  exact compute

end
end Hierarchy.DescentPacking.PackedMatch.Local.Gather.ROM

end OAI
