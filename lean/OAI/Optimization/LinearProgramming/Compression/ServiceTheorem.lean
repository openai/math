import OAI.Optimization.LinearProgramming.Compression.ServiceImplementation
import OAI.Optimization.LinearProgramming.Compression.NumericMinorROM

/-! The fixed on-demand service for the logarithms of actual nonzero rational minors.
Both programs are assembled before the dimensions and matrices are supplied. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

/-- Theorem 1.4, with the independently specified RAM input/output formats, signed bits,
per-call time and size bounds, and one simultaneous extension for every request prefix. -/
theorem online_minor_log_compression_ram : OracleSpec.OnlineMinorLogCompression :=
  onlineMinorLogCompression_of_numeric numericMinorROM_correct


/-- Public comparator root for online minor-log compression. -/
theorem onlineMinorCompression : OracleSpec.OnlineMinorLogCompression :=
  online_minor_log_compression_ram

end Compression
end LinearProgramming
end Optimization
end OAI
