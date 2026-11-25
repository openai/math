import OAI.Computability.BorderVNP.PackedFrozenPrepBatch

/-! # Complete record images in the attained child subdivision -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.PrepBatch

open Crossing Shortening Shortening.PublicCapacity Shortening.PublicEndpoints
open PackedHistoryCircuit WorkWords Subdivision Diagonal.ExternalSew.FieldExport
open VPVNP.VerifierNetwork ParseBatchSort
open private oldRead newRead from OAI.Computability.BorderVNP.PackedFrozenPrepBatch

variable {k w np extra : ℕ} {s : Shape} (T : Format)
    {Old A B : Type} [Fintype Old] [Fintype B]
    (prior : Inputs A s.sites s.edges w w → Old) (ports : WorkWords.Ports np) (fit : (s.subdivide extra).sites ≤ 2^w)
    (pre : Frame (Fin k × WithWidths Old s.sites w)
      (Fin k × WithWidths (SavedPins B (s.subdivide extra).sites (s.subdivide extra).edges w) (s.subdivide extra).sites w))
    (x : Fin k × T.Output Old s.sites w w → Bool) (i : Fin k)

local notation3 "raw" => fun z : Fin k × WithWidths Old s.sites w => x (z.1,.inl z.2)
local notation3 "y" => pre.eval raw
local notation3 "joined" => (joint T pre).eval x

private theorem joint_eval : joined = (constants _).eval (Sum.elim x y) := by
  have sel : (Frame.initial (fun z : Fin k × WithWidths Old s.sites w => (z.1,Sum.inl z.2))).eval x = raw :=
    funext (Frame.initial_eval _ _)
  funext z
  cases z with
  | inr b => simp [joint,constants_eval]
  | inl a =>
    cases a with
    | inl u => simp [joint,constants_eval]
    | inr v => simp [joint,constants_eval,sel]

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits) (route : N.WireRoutes)
    (rows : Rows s N) (bound : ∀ e, route.interior e ≤ extra)
    (portID : P ↪ Fin np) (oldDummy : Fin s.edges → N.Site) (newDummy : Fin (s.subdivide extra).edges → (N.subdivide route).Site)
    (programs : Site.Programs N)
local notation3 "G" => N.subdivide route
local notation3 "next" => rows.subdivide route extra bound
local notation3 "F0" => oldFields (B := B) T prior ports fit i
local notation3 "F1" => newFields (B := B) (Old := Old) T ports fit i
local notation3 "wordPin" => siteWord (B := B) (Old := Old) (extra := extra) T i
local notation3 "hopPin" => hopPresent (B := B) (Old := Old) (s := s) (extra := extra) (w := w) T i
local notation3 "priorTape" => earlier (B := B) (Old := Old) (s := s) (extra := extra) (w := w) T i

/-- The full shared pre-frame on a genuine subdivision. The inputs here are the old and
returned public endpoint directories, both physical width words, and the previously frozen
tape. The original programs and all relay equalities have their actual new sparse owner IDs. -/
theorem batch_image
    (oldReady : Represents N rows.site rows.edge oldDummy (fun z => x (i,.inl (.inl (prior z)))))
    (newReady : Represents G (next).site (next).edge newDummy (fun z => y (i,.inl (.inr (.inr z)))))
    (live : ∀ j, y (i,.inl (.inl j)) = true ↔ j ∈ Set.range (next).edge)
    (portsOK : ports.Reads N rows.site portID) (widthFit : ∀ j, ports.width j < 2^w)
    (shape : ∀ e, route.interior e = 0 ∨ route.interior e = extra)
    (words : ∀ v b, value (fun j => x (i,.inl (.inr (rows.site v,b,j)))) =
      if b then (programs v).program.size else (programs v).program.work)
    (before : T.schema.Image (fun z => x (i,.inr z)) (rows.site.trans Fin.valEmbedding) (fun v => (programs v).program))
    (oldFit : ∀ v, incoming N v < 2^w) (newFit : ∀ v, incoming G v < 2^w)
    (room : ∀ v, (programs v).program.size + incoming G (.inl v) < 2^w) (one : 1 < 2^w) :
    (T.append (Format.subdivision s.edges np extra w)).schema.Image
      (fun j => (batch T prior ports fit pre).eval x (i,.inr j)) ((next).site.trans Fin.valEmbedding)
      (fun v => (subdividePrivatePrograms N route rows.edge (next).edge portID programs v).program) := by
  let full := Sum.elim x y
  have join := joint_eval T pre x
  have oldData : Views.EndpointData N F0 rows.site rows.edge portID joined := by
    rw [join]
    exact TerminalCells.named_endpoints ((Nat.le_add_right s.sites _).trans fit)
      (oldRead (extra := extra) (B := B) T prior i) ports.host ports.width N rows.site rows.edge oldDummy portID
      full oldReady portsOK.attach portsOK.size widthFit portsOK.hole
  have newData : Views.EndpointData G F1 (next).site (next).edge portID joined := by
    rw [join]
    exact TerminalCells.named_endpoints fit (newRead (B := B) (Old := Old) (s := s) (extra := extra) (w := w) T i)
      ports.host ports.width G (next).site (next).edge newDummy portID full newReady
      (fun p => (portsOK.attach p).trans ((rows.subdivide_old route extra bound _).symm)) portsOK.size widthFit portsOK.hole
  have hp (j) : joined (hopPin j) = true ↔ j ∈ Set.range (next).edge := by
    simpa only [join,hopPresent,constants_eval,Sum.elim_inl,Sum.elim_inr] using live j
  have oldBits (b : Bool) (v : N.Site) : value (joined ∘ wordPin b (rows.site v)) =
      if b then (programs v).program.size else (programs v).program.work := by
    simpa only [join,siteWord,constants_eval,Sum.elim_inl,Function.comp_def] using words v b
  have prev : (priorTape).eval joined = fun j => x (i,.inr j) := by
    funext j
    simp only [join,earlier,Frame.initial_eval,constants_eval,Sum.elim_inl]
  have priorImage : T.schema.Image ((priorTape).eval joined)
      ((rows.site.trans (F0).sites).trans Fin.valEmbedding) (fun v => (programs v).program) := by
    rw [prev]; exact before
  have h := Gates.completeTape_image rows route bound portID F0 F1 (wordPin false) (wordPin true) hopPin programs
    oldData newData oldFit newFit hp shape (fun v => oldBits false v) (fun v => oldBits true v)
    T.schema priorTape priorImage room one
  have output : (fun j => (batch T prior ports fit pre).eval x (i,.inr j)) =
      (leaf (B := B) T prior ports fit i).eval joined := funext (batch_tape T prior ports fit pre x i)
  rw [output]; exact h

end Packing.Inherited.FrozenTape.PrepBatch

end BorderVNP
end Computability
end OAI
