import OAI.Computability.BorderVNP.CellPacketGeometryHistorySource
import OAI.Computability.BorderVNP.CellPacketGeometryHistoryGateCost

/-! # Joining the genuine public tapes and terminal geometric field programs once -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native

open Packing.Inherited FrozenTape VPVNP.VerifierNetwork Crossing LiveWords CellSparse Packet
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {a C cap k w d t q : ℕ} {R B U V E Orig σ : Type}
variable [Fintype R] [Fintype B] [Fintype U] [Fintype V] [Fintype E] [Fintype σ]

/-- The common public source buffer before the site-owner lookup and three stable sorts. -/
abbrev Bundle (R B U V E : Type) (a d t k w : ℕ) :=
  Pins R B d ⊕ (Pins U V t ⊕ ((Fin a × Column k w) ⊕ ((E × Fin w) ⊕ Bool)))

/-- Direct physical pin selection for the joined upstream buffers. -/
def access : Access R B U V E (Bundle R B U V E a d t k w) a d t k w where
  history := Sum.inl
  binding z := .inr (.inl z)
  table s col := .inr (.inr (.inl (s,col)))
  field e := .inr (.inr (.inr (.inl e)))
  valid := .inr (.inr (.inr (.inr true)))
  zero := .inr (.inr (.inr (.inr false)))

/-- Actual producers, all on the same terminal branch. Their finite row and
field layouts remain fixed before this branch is evaluated. -/
structure Feeds (σ R B U V E : Type) [Fintype σ] [Fintype R] [Fintype B] [Fintype U] [Fintype V] [Fintype E]
    (a d t k w : ℕ) where
  /-- The chronological site-program producer after public sewing. -/
  history : Frame σ (Pins R B d)
  /-- The absolute terminal wire and port binding producer. -/
  binding : Frame σ (Pins U V t)
  /-- The public cell and two relocation prefixes for each site. -/
  table : Frame σ (Fin a × Column k w)
  /-- The upstream report, pointer, and private-size field producer. -/
  field : Frame σ (E × Fin w)
  /-- The upstream validity bit, shared with the final geometry output. -/
  valid : σ

variable (F : Feeds σ R B U V E a d t k w)

private def flag (good : σ) (b : Bool) : Expr σ := if b then .input good else .const false

/-- Evaluate all the actual producers, retaining one shared constant false for
leading zeroes and unused operands. This is composed outside the two source consumers. -/
noncomputable def Feeds.frame : Frame σ (Bundle R B U V E a d t k w) :=
  parallelFrame F.history (parallelFrame F.binding (parallelFrame F.table (parallelFrame F.field
    ((Frame.initial (id : σ → σ)).step (flag F.valid)))))

theorem Feeds.frame_size : F.frame.size ≤ F.history.size+F.binding.size+F.table.size+F.field.size+2 := by
  have h := Frame.step_size_le (Frame.initial (id : σ → σ)) (flag F.valid) 1
    (fun b => by cases b <;> simp [flag,StatementCircuit.Expr.size])
  simp only [Frame.initial_size,Fintype.card_bool,mul_one,zero_add] at h
  simp only [Feeds.frame,parallelFrame_size]
  omega

local notation3 "A₀" => (access : Access R B U V E (Bundle R B U V E a d t k w) a d t k w)

theorem Feeds.history_read (x : σ → Bool) : F.frame.eval x ∘ (A₀).history = F.history.eval x := by
  funext j; simp [Feeds.frame,access]

theorem Feeds.binding_read (x : σ → Bool) : F.frame.eval x ∘ (A₀).binding = F.binding.eval x := by
  funext j; simp [Feeds.frame,access]

theorem Feeds.table_read (x : σ → Bool) (s : Fin a) (col : Column k w) :
    F.frame.eval x ((A₀).table s col) = F.table.eval x (s,col) := by simp [Feeds.frame,access]

theorem Feeds.field_read (x : σ → Bool) (e : E × Fin w) : F.frame.eval x ((A₀).field e) = F.field.eval x e := by
  simp [Feeds.frame,access]

theorem Feeds.valid_read (x : σ → Bool) : F.frame.eval x (A₀).valid = x F.valid := by
  simp [Feeds.frame,access,flag,StatementCircuit.Expr.eval]

theorem Feeds.zero_read (x : σ → Bool) : F.frame.eval x (A₀).zero = false := by
  simp [Feeds.frame,access,flag,StatementCircuit.Expr.eval]

variable (S : Schema R B) (L : Schema U V) (boxes : Fin a → List (Source.Box Orig))
variable (sh : ∀ r, (S.tags r).length≤cap) (lh : ∀ r, (L.tags r).length≤cap)
variable (priv : Fin (C+1) → E) (rep : Fin (C+1) → List (List E))
variable (hd : d≤q) (ht : t≤q) (room : a<2^q) (croom : C<2^k)
variable (hs : ∀ r, S.width r ≤ w) (hl : ∀ u, L.width u ≤ w)
local notation3 "T₀" => template S L boxes sh lh priv rep
variable (base : Fin (roster a S L).length → Fin (C+1)) (pointer : Orig → (template S L boxes sh lh priv rep).Fields)
variable (pad : (roster a S L).length < 2^q) (dest H : ℕ)

/-- The complete terminal packet output circuit. The two source consumers use
the same retained history, binding, field and cell-prefix buffers. -/
noncomputable def Feeds.ordered : Frame σ (GeometryFrameEncoding.Outputs
    (Total (T₀).publicDepth (T₀).chunkDepth) w) := by
  let up := source (cap := cap) S L A₀ hd ht room croom hs hl
  let keys := anchors S L A₀ hd ht room
  let outer := Template.orderedFrame (template S L boxes sh lh priv rep) up keys base pointer pad dest H
  exact Frame.subst outer F.frame

/-- Numerical cost from actual generating frames and true native lookup/roster
dimensions. The common earlier terminal frame may be substituted once after
joining this output to the cable and routing output columns. -/
theorem Feeds.ordered_size (W : ℕ) (wk : k≤W) (ww : w≤W) (wq : q≤W)
    (wp : (T₀).publicDepth≤W) (wd : (T₀).chunkDepth≤W) (wb : (T₀).recordDepth≤W)
    (wh : Nat.clog 2 ((roster a S L).length+(C+1))≤W) :
    (F.ordered S L boxes sh lh priv rep hd ht room croom hs hl base pointer pad dest H).size ≤
      F.history.size+F.binding.size+F.table.size+F.field.size+2+
        siteCost a (roster a S L).length q k w + (roster a S L).length*q*8 +
        16000000*sourceVolume S L boxes rep*(W+1)^3 := by
  have baseCost := frame_size_le_source S L boxes sh lh priv rep
    (source S L A₀ hd ht room croom hs hl) (anchors S L A₀ hd ht room) base pointer pad dest H W wk ww wq wp wd wb wh
  have us := source_size (cap := cap) S L A₀ hd ht room croom hs hl
  have ak := anchors_size S L A₀ hd ht room
  have pre := F.frame_size
  simp only [Feeds.ordered,Frame.subst_size]
  omega

end CellPacketGeometry.History.Native

end BorderVNP
end Computability
end OAI
