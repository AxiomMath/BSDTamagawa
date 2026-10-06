module

public meta import Lean

/-!
# The `bsd_tamagawa` tag attribute

The attribute `@[bsd_tamagawa "TAG"]` marks a declaration as formalizing the numbered statement
with label `TAG`.

    @[bsd_tamagawa "T001"]
    theorem my_result : True := trivial
-/

public meta section

open Lean

/-- `@[bsd_tamagawa "TAG"]` links a Lean declaration to the statement with label `TAG`. -/
syntax (name := bsd_tamagawa) "bsd_tamagawa " str : attr

initialize Lean.registerBuiltinAttribute {
  name  := `bsd_tamagawa
  descr := "marks a declaration with the label of the result of the paper it formalizes"
  add   := fun _ _ _ => pure ()
}

end
