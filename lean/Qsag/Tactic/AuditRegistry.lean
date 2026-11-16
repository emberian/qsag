module
public meta import Lean

public meta section
namespace Qsag.Tactic.AssuranceKit
open Lean

/-- Certificates are written only after auditing an owning module's visible proof.
Normal imports retain this small registry while keeping proof bodies opaque. -/
initialize constructiveAuditExt :
    SimplePersistentEnvExtension Name (Std.HashSet Name) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := mkStateFromImportedEntries (fun s n => s.insert n) {}
    addEntryFn := fun s n => s.insert n
  }

/-- A joint inhabitedness certificate records the exact security/witness pair checked
while the witness proof body is available. -/
initialize inhabitedAuditExt :
    SimplePersistentEnvExtension (Name × Name) (Std.HashSet (Name × Name)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := mkStateFromImportedEntries (fun s n => s.insert n) {}
    addEntryFn := fun s n => s.insert n
  }

end Qsag.Tactic.AssuranceKit
end
