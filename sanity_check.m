SanityCheck[{eqns_List, vars_List}] :=
  Length[FindInstance[Apply[And, eqns], vars]]
