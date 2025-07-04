/-- Compatibility shim: mathlib4 v4.3 merged `Mathlib.Data.Nat.Prime.Basic` into
    `Mathlib.Data.Nat.Prime`.  We provide the old module that simply re-exports the
    new location so legacy imports continue to work.  Remove this file once all
    upstream code is migrated. -/

import Mathlib.Data.Nat.Prime

-- Re-export everything.
export Mathlib.Data.Nat.Prime
