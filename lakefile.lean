import Lake
open Lake DSL

package "annotation-examples" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require "leanprover-community" / "mathlib" @ git "20c73142afa995ac9c8fb80a9bb585a55ca38308"

@[default_target]
lean_lib «AnnotationExamples» where
  -- add any library configuration options here
