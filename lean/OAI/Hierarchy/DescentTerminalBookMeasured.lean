import OAI.Hierarchy.DescentTerminalBookCensus

namespace OAI
/-! # The common-host book decoder reads original paid actor, boundary and signed columns -/
namespace Hierarchy.DescentTerminalLocalPortBook.Rasters
open DescentSixParty DescentCompiler DescentSharedCableNames DescentColonies DescentChosenRouter DescentPacking
open DescentStageEdgeReceipt DescentPacking.PackedMatch.Local.Stage DescentTerminalSignedGrainWord
open DescentTerminalGraphRows DescentSortedRoster ProtocolRAM DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.Routing
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F P V:Type} [Field F] [Fintype P] [Fintype V] [DecidableEq V] {groups d k i H p bw argc w:ℕ}
    {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F} {price ε:ℝ}
    (A:GroupStage W G price ε (Fin groups) V k) (hosts:V↪Fin H) (S:AtomSchedule) (ready:A.StateBounds S i)
    (native:W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (raw:Fin H→Fin A.degree→Option (Fin H))
    (rack:Rasters A.degree (2^k) A.cap) (m:Memory w)
local notation "ord" => native.trans Fin.valEmbedding
local notation "roster" => indexed raw
local notation "atH" => fun v:W.graph.Site=>hosts (Prod.snd (A.pos v))
local notation "signed" => Prepare.signed A ord S ready (Function.Embedding.refl (Fin groups)) hosts
local notation "board" => fun h:Fin H=>measure A.degree (2^k) A.cap groups argc (DescentTerminalPointerDigits.Gather.values (d:=bw) rack.sources m h)

/-- Low-level premises refer exclusively to measured words which precede
the six geometry passes. Bank ranges also pin down total reads on blank hosts. -/
structure Inputs : Prop where
  near : ∀v,present raw (hosts v)=(A.near v).map hosts
  peer : ∀h j z,roster h j=some z→ rack.roster.read m ((h.val*A.degree+j.val:ℕ):Word w)=(z.val:Word w)
  scalarWord : 2<2^w
  shortWord : 2<2^bw
  hostWord:H≤2^w
  actorSlots:groups≤bw
  aritySlots:argc*groups≤bw
  actor:∀ (g : Fin groups) (h : Fin H) (x : Block k), digit 1 g.val ((rack.geometry.occupied x).read m (h.val : Word w)).val =
    if ∃v:W.graph.Site,atH v=h ∧ (A.pos v).1=g ∧ A.block v=x then 1 else 0
  arity:∀ v : W.graph.Site, digit argc (A.pos v).1.val
    ((rack.geometry.primitive (A.block v) 0).read m ((atH v).val : Word w)).val=DescentTerminalGraphRows.arity W.graph p v
  wings:∃M,groups≤M ∧ DescentSignedCableCodec.width A.degree A.cap*M≤w ∧
    ∀b t,DescentPackedColony.Reads (rack.wing b t) (fun h g=>DescentSignedCableCodec.encode (signed b t h g)) M m
  wingSlots:DescentSignedCableCodec.width A.degree A.cap*groups≤bw
  bankRoom:∀b j,H≤(rack.wing b j).size

private theorem one_chunk (n M:ℕ) (hn:0<n) (hm:n≤M):chunks n M=1 := by
  unfold chunks poolBatchCount
  apply Nat.div_eq_of_lt_le <;> omega

include p in
private theorem scan_wing (real:Inputs (p:=p) (bw:=bw) (argc:=argc) A hosts S ready native raw rack m)
    (h:Fin H) (g:Fin groups) (b:Block k) (t:Fin (2*A.cap)) :
    (board h).ports g b t=signed b t h g := by
  rw [wing_digit rack m h b g t argc real.wingSlots]
  obtain ⟨M,covers,wide,held⟩:=real.wings
  have pos:0<M:=Nat.zero_lt_of_lt (g.isLt.trans_le covers)
  let bank:=rack.wing b t
  have atRow:(row H groups M (position h g pos)).val=h.val:=by
    change (g.val/M)+(chunks groups M)*h.val=h.val
    rw [Nat.div_eq_of_lt (g.isLt.trans_le covers),one_chunk groups M (Nat.zero_lt_of_lt g.isLt) covers];omega
  have idx:(lane g pos).val=g.val:=Nat.mod_eq_of_lt (g.isLt.trans_le covers)
  have bit:bank.read m (h.val:Word w)=m (bank.base+h.val):=by
    have room : h.val < bank.size := h.isLt.trans_le (real.bankRoom b t)
    simp only [Bank.read, Fin.val_cast_of_lt (h.isLt.trans_le real.hostWord), Nat.mod_eq_of_lt room]
  have same:=DescentTerminalSignedGrainWord.wing_read bank m (signed b t) (held b t) h g pos wide
  rw [bit]
  simpa only [DescentTerminalSignedGrainWord.wing,chip,atRow,idx] using same

theorem observed (real:Inputs (p:=p) (bw:=bw) (argc:=argc) A hosts S ready native raw rack m) :
    Board.Observed (p:=p) A hosts S ready native raw board := by
  have reach (o:V) (g:Fin groups) (b:Block k) : (board (hosts o)).ports g b=
      Stage.signedPanel A ord S ready
        (cableNames k (groupRank (Fin.valEmbedding (n:=groups)) (hosts.trans Fin.valEmbedding))) ((g,o),b) := by
    funext t
    exact (scan_wing A hosts S ready native raw rack m real _ g b t).trans
      (stored_site A ord S ready (Function.Embedding.refl _) hosts b t (g,o))
  refine ⟨real.near,fun h j z hit=>side_read rack m h j z argc real.scalarWord real.shortWord (real.peer h j z hit) real.hostWord,
    reach,?_,?_⟩
  · intro h none g b t
    rw [scan_wing A hosts S ready native raw rack m real]
    have no:¬∃z:Fin groups×V,z.1=g ∧ hosts z.2=h:=by rintro ⟨z,_,eqn⟩;exact none _ eqn
    simp [Prepare.signed,Prepare.spreadField,no]
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro v hv
      rw [venue_digits rack m h _ _ argc real.actorSlots real.aritySlots,real.actor]
      have live:∃u:W.graph.Site,atH u=h ∧ (A.pos u).1=(A.pos v).1 ∧ A.block u=A.block v:=⟨v,hv,rfl,rfl⟩
      rw [ite_eq_left live]
      simpa only [one_ne_zero, ite_false, ← hv] using congrArg some (real.arity v)
    · intro g b empty
      rw [venue_digits rack m h b g argc real.actorSlots real.aritySlots,real.actor]
      simp [empty]
    · intro v hv
      subst h
      exact reach _ _ _

end
end Hierarchy.DescentTerminalLocalPortBook.Rasters

end OAI
