Equal
: ∀(A: *) 
  ∀(a: A) 
  ∀(b: A) 
  *
= λA λa λb 
  ∀(P:∀(x:A) *) ∀(p:(P a)) (P b)