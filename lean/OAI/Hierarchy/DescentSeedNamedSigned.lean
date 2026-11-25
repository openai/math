import OAI.Hierarchy.DescentSeedWorldNames
import OAI.Hierarchy.DescentSameCableOrder
import OAI.Hierarchy.DescentSignedCableCodec
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! The numerical cable bank is preserved by the heralded static seed relabelling. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Signed
open DescentCompiler DescentColonies DescentSharedCableNames
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits:P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist : ℕ}
    (R : Reached W G q ε S k i z D wire hist)
local notation "A" => R.placement
local notation "T" => placed R
local notation "orig" => R.order.trans Fin.valEmbedding
local notation "next" => Function.Embedding.trans (Reached.order (reached R)) Fin.valEmbedding
local notation "old" => Stage.source A orig
local notation "new" => Stage.source T next
local notation "H" => Stage.Host (Fin (S.groupCount i)) R.V k

theorem grain (e : W.graph.Edge) : (T).grainCount (edge R e)=(A).grainCount e := by
  change (world R).graph.width (edge R e)/((A).z*G.b)=_
  rw [(cable R e).2.2.1]
  rfl

def grainEquiv : Stage.Grain A ≃ Stage.Grain T :=
  Equiv.sigmaCongr (edge R) (fun e => finCongr (grain R e).symm)

theorem «prefix» (e : W.graph.Edge) : ProtocolRAMPortRanks.«prefix» (T).grainCount next (edge R e)=
    ProtocolRAMPortRanks.«prefix» (A).grainCount orig e := by
  unfold ProtocolRAMPortRanks.«prefix»
  simp only [Finset.sum_filter]
  symm
  apply Fintype.sum_equiv (edge R)
  intro t
  change (if (R.order t).val < (R.order e).val then (A).grainCount t else 0) =
    (if ((reached R).order (edge R t)).val < ((reached R).order (edge R e)).val then
      (T).grainCount (edge R t) else 0)
  rw [(cable R t).2.2.2,(cable R e).2.2.2,grain R t]

theorem stream (p : Stage.Grain A) : Stage.stream T next (grainEquiv R p)=
    Fin.cast (Fintype.card_congr (grainEquiv R)) (Stage.stream A orig p) := by
  obtain ⟨e,u⟩:=p
  apply Fin.ext
  change ProtocolRAMPortRanks.«prefix» (T).grainCount next (edge R e) + u.val =
    ProtocolRAMPortRanks.«prefix» (A).grainCount orig e + u.val
  rw [«prefix» R e]

theorem leftHome (e : W.graph.Edge) : Stage.home T ((world R).graph.src (edge R e))=Stage.home A (W.graph.src e) := by
  rw [(cable R e).1];exact Prod.ext (position R _).1 (position R _).2.1

theorem rightHome (e : W.graph.Edge) : Stage.home T ((world R).graph.dst (edge R e))=Stage.home A (W.graph.dst e) := by
  rw [(cable R e).2.1];exact Prod.ext (position R _).1 (position R _).2.1

theorem same : Ends.Same old new where
  count:=Fintype.card_congr (grainEquiv R)
  src t:=by
    obtain ⟨p,rfl⟩:=(Stage.stream A orig).surjective t
    rw [←stream R]
    simp only [Stage.source,Equiv.symm_apply_apply]
    exact leftHome R p.1
  dst t:=by
    obtain ⟨p,rfl⟩:=(Stage.stream A orig).surjective t
    rw [←stream R]
    simp only [Stage.source,Equiv.symm_apply_apply]
    exact rightHome R p.1

abbrev Ports (h : H) := (A).CellPorts h.1.1 h.1.2 h.2
abbrev NamedPorts (h : H) := (T).CellPorts h.1.1 h.1.2 h.2

def port (h : H) : Ports R h→NamedPorts R h
  | .inl ⟨e,u⟩=> .inl ⟨⟨edge R e.val,(congrArg Prod.fst (leftHome R e.val)).trans e.property.1,
      (congrArg Prod.snd (leftHome R e.val)).trans e.property.2⟩,Fin.cast (grain R e.val).symm u⟩
  | .inr ⟨e,u⟩=> .inr ⟨⟨edge R e.val,(congrArg Prod.fst (rightHome R e.val)).trans e.property.1,
      (congrArg Prod.snd (rightHome R e.val)).trans e.property.2⟩,Fin.cast (grain R e.val).symm u⟩

theorem onto (h:H) : Function.Surjective (port R h) := by
  rintro (⟨⟨a,hp⟩,u⟩|⟨⟨a,hp⟩,u⟩)
  · obtain ⟨e,rfl⟩:=(edge R).surjective a
    exact ⟨.inl ⟨⟨e,(congrArg Prod.fst (leftHome R e)).symm.trans hp.1,
      (congrArg Prod.snd (leftHome R e)).symm.trans hp.2⟩,Fin.cast (grain R e) u⟩,rfl⟩
  · obtain ⟨e,rfl⟩:=(edge R).surjective a
    exact ⟨.inr ⟨⟨e,(congrArg Prod.fst (rightHome R e)).symm.trans hp.1,
      (congrArg Prod.snd (rightHome R e)).symm.trans hp.2⟩,Fin.cast (grain R e) u⟩,rfl⟩

theorem ordinal (h : H) (p : Ports R h) : (Stage.ofPort T next h (port R h p)).val=
    Fin.cast (same R).count (Stage.ofPort A orig h p).val := by
  cases p with
  | inl u=>exact stream R ⟨u.1.val,u.2⟩
  | inr u=>exact stream R ⟨u.1.val,u.2⟩

theorem place (h:H) (p : Ports R h) :
    Stage.signed T next S (reached R).valid h.1 h.2 (port R h p)=Stage.signed A orig S R.valid h.1 h.2 p := by
  apply congrArg finProdFinEquiv
  apply Prod.ext
  · cases p <;> rfl
  · exact (same R).place_at _ _ h _ _ (ordinal R h p)

theorem first (e : Stage.Positive A) :
    Stage.outgoing T next S (reached R).valid ⟨edge R e.val,by simpa only [grain] using e.property⟩=
      Stage.outgoing A orig S R.valid e := by
  let p : Stage.Positive T:=⟨edge R e.val,by simpa only [grain] using e.property⟩
  let h:=Stage.home A (W.graph.src e.val)
  have move {t : H} (atSrc : Stage.home T ((world R).graph.src p.val)=t) :
      Stage.outgoing T next S (reached R).valid p=Stage.outgoingAt T next S (reached R).valid t p atSrc := by cases atSrc;rfl
  rw [move (leftHome R e.val)]
  apply (same R).place_at
  exact stream R ⟨e.val,⟨0,e.property⟩⟩

theorem live (names : H↪ℕ) (h : H) (p : Ports R h) : Stage.live T next S (reached R).valid names h (port R h p)=
    Stage.live A orig S R.valid names h p := by
  let a:=Stage.ofPort A orig h p
  let b:=Stage.ofPort T next h (port R h p)
  have ord:=ordinal R h p
  have nbh := (same R).neighbor_at (Stage.near A) names (Stage.near_room A) (Stage.near_room T)
    (Stage.connected A orig) (Stage.connected T next) h a b ord
  have wireEq : (new).serial h ((new).peer h b.val) b.val=(old).serial h ((old).peer h a.val) a.val := by
    rw [show b.val=Fin.cast (same R).count a.val from ord];apply (same R).wire_at
  have core (e : W.graph.Edge) : (edge R e∈(world R).core) ↔ e∈W.core:=
    PhysicalRename.core_mem W (site R) (edge R) e
  have extRecord {a b : Stage.Live (A).degree (A).cap} (n:a.neighbor=b.neighbor) (w:a.wire=b.wire)
      (s:a.sourceWire=b.sourceWire) (i:a.within=b.within) (t:a.target=b.target) (o:a.markedOut=b.markedOut) : a=b := by
    cases a;cases b;simp_all
  apply extRecord nbh (Fin.ext wireEq)
  · cases p with
    | inl u=>exact first R ⟨u.1.val,Nat.zero_lt_of_lt u.2.isLt⟩
    | inr u=>exact first R ⟨u.1.val,Nat.zero_lt_of_lt u.2.isLt⟩
  · cases p <;> rfl
  · cases p <;> rfl
  · cases p with
    | inl u =>
      simp only [Stage.live,port,Stage.isMarkedOut,Fin.val_cast]
      apply decide_eq_decide.mpr
      exact and_congr (core u.1.val) Iff.rfl
    | inr u=>rfl

theorem panel (names : H↪ℕ) (h:H) (slot : Fin (2*(A).cap)) :
    Stage.signedPanel T next S (reached R).valid names h slot = Stage.signedPanel A orig S R.valid names h slot := by
  by_cases hit : ∃p,Stage.signed A orig S R.valid h.1 h.2 p=slot
  · obtain ⟨p,rfl⟩:=hit
    exact (congrArg (Stage.signedPanel T next S (reached R).valid names h) (place R h p).symm).trans
      ((Stage.signed_read T next S (reached R).valid names h (port R h p)).trans
        ((congrArg some (live R names h p)).trans (Stage.signed_read A orig S R.valid names h p).symm))
  · rw [Stage.signed_empty A orig S R.valid names h slot (fun p eqn=>hit ⟨p,eqn⟩)]
    apply Stage.signed_empty
    intro p
    obtain ⟨u,rfl⟩:=onto R h p
    rw [place];exact fun eqn=>hit ⟨u,eqn⟩

theorem reads {n g M w : ℕ} (bank : ProtocolRAM.Bank) (m : Computability.VPVNP.BurstRAM.Memory w) (whereAt : Fin n→Fin g→H)
    (names:H↪ℕ) (slot:Fin (2*(A).cap))
    (given : DescentPackedColony.Reads bank (fun h j=>DescentSignedCableCodec.encode
       (Stage.signedPanel A orig S R.valid names (whereAt h j) slot)) M m) :
    DescentPackedColony.Reads bank (fun h j=>DescentSignedCableCodec.encode
       (Stage.signedPanel T next S (reached R).valid names (whereAt h j) slot)) M m := by
  change @DescentPackedColony.Reads n g (DescentSignedCableCodec.width (A).degree (A).cap) w bank
    (fun h j=> DescentSignedCableCodec.encode (Stage.signedPanel T next S (reached R).valid names (whereAt h j) slot)) M m
  simpa only [panel R names] using given

theorem padded_reads {n g M w : ℕ} (bank : ProtocolRAM.Bank) (m : Computability.VPVNP.BurstRAM.Memory w)
    (whereAt : Fin n→Fin g→Option H) (names:H↪ℕ) (slot:Fin (2*(A).cap))
    (given : DescentPackedColony.Reads bank (fun h j=>DescentSignedCableCodec.encode
       ((whereAt h j).bind (fun loc=>Stage.signedPanel A orig S R.valid names loc slot))) M m) :
    DescentPackedColony.Reads bank (fun h j=>DescentSignedCableCodec.encode
       ((whereAt h j).bind (fun loc=>Stage.signedPanel T next S (reached R).valid names loc slot))) M m :=by
  change @DescentPackedColony.Reads n g (DescentSignedCableCodec.width (A).degree (A).cap) w bank
    (fun h j=> DescentSignedCableCodec.encode
      ((whereAt h j).bind (fun loc=>Stage.signedPanel T next S (reached R).valid names loc slot))) M m
  simpa only [panel R names] using given

end
end Hierarchy.DescentSixParty.SeedNamed.Signed

end OAI
