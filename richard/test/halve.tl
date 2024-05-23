halve
: ∀(n: Nat) 
  Nat
= λn 
  (~n λn Nat λnp (~np λn Nat λnpp (succ (halve npp)) zero) zero)